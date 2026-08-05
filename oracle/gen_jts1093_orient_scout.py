#!/usr/bin/env python3
"""
JTS #1093 orientation lane — Ozaki filter scout vs corpus exact orient.

topic: precision (epic #66)
Upstream: locationtech/jts#1093 (Ozaki et al. orientationIndexFilter)
Corpus GT: oracle_bin ORIENT_EXACT (zarith / full-plane sign)
Optional:  ffi_probe ORIENT_FILTERED (Shewchuk Stage A via libntsrocq)

What this gates (no new Rocq claimId — ADR-0004 cold):
  I1  Ozaki CERTAIN never disagrees with ORIENT_EXACT sign (nonzero).
  I2  Corpus Shewchuk Stage A CERTAIN never disagrees with exact.
  I3  JTS-master (DP_SAFE_EPSILON=1e-15) CERTAIN never disagrees with exact.
  I4  Report tighter-filter stats:
        Ozaki CERTAIN when JTS-master UNCERTAIN (PR claim: fewer misses)
        Ozaki CERTAIN when corpus Shewchuk UNCERTAIN
        corpus Shewchuk CERTAIN when Ozaki UNCERTAIN

Three filters mirrored in pure double:

  JTS-master (pre-#1093):
    Shewchuk-style detsum + opposite-sign early CERTAIN
    errbound = 1e-15 * detsum
    certain  iff |det| >= errbound  (or early)

  Ozaki (PR #1093):
    detleft  = (ax-cx)*(by-cy)
    detright = (ay-cy)*(bx-cx)
    det      = detleft - detright
    errbound = |detleft + detright| * 3.3306690621773724e-16
    certain  iff |det| >= errbound

  Corpus Shewchuk Stage A (Orientation_b64 / predicates.c shape):
    detsum construction as JTS-master
    errbound = (3+16ε)ε * detsum, ε=2^-53

Usage:
  python oracle/gen_jts1093_orient_scout.py
  python oracle/gen_jts1093_orient_scout.py --wsl-oracle /path/to/oracle_bin
  python oracle/gen_jts1093_orient_scout.py --ffi-probe /path/to/ffi_probe
"""
from __future__ import annotations

import argparse
import math
import os
import struct
import subprocess
import sys
from dataclasses import dataclass
from typing import List, Optional, Sequence, Tuple

# Ozaki constant from jts#1093 (double literal in CGAlgorithmsDD).
OZAKI_K = 3.3306690621773724e-16

# JTS master DP_SAFE_EPSILON (pre-#1093 orientationIndexFilter).
JTS_DP_SAFE_EPSILON = 1e-15

# Shewchuk ε and ccwerrboundA coefficient (Orientation_b64 / predicates.c).
SHEWCHUK_EPS = math.ldexp(1.0, -53)
CCWERRBOUND_A = (3.0 + 16.0 * SHEWCHUK_EPS) * SHEWCHUK_EPS

Point = Tuple[float, float]


@dataclass
class Vec:
    name: str
    a: Point  # p0 / pa
    b: Point  # p1 / pb
    q: Point  # query / pc  (JTS origin of filter translation)
    expected: Optional[str]  # POS | NEG | ZERO | None
    note: str = ""


def det_parts(a: Point, b: Point, q: Point) -> Tuple[float, float, float]:
    """Return (detleft, detright, det) with origin at q (Shewchuk/Ozaki/JTS form).

    Matches CGAlgorithmsDD: detleft=(pax-pcx)*(pby-pcy), detright=(pay-pcy)*(pbx-pcx).
    """
    ax, ay = a[0] - q[0], a[1] - q[1]
    bx, by = b[0] - q[0], b[1] - q[1]
    detleft = ax * by
    detright = ay * bx
    return detleft, detright, detleft - detright


def _sign_of(det: float) -> str:
    if det > 0:
        return "POS"
    if det < 0:
        return "NEG"
    return "ZERO"


def stage_a_ozaki(a: Point, b: Point, q: Point) -> Tuple[str, float, bool]:
    """Mirror of jts#1093 orientationIndexFilter (Ozaki et al.)."""
    detleft, detright, det = det_parts(a, b, q)
    errbound = abs(detleft + detright) * OZAKI_K
    certain = abs(det) >= errbound
    return _sign_of(det), det, certain


def _detsum_certain(
    detleft: float, detright: float, det: float, k: float
) -> Tuple[str, float, bool]:
    """Shewchuk/JTS-master detsum construction with relative constant k."""
    if detleft > 0.0:
        if detright <= 0.0:
            return _sign_of(det), det, True
        detsum = detleft + detright
    elif detleft < 0.0:
        if detright >= 0.0:
            return _sign_of(det), det, True
        detsum = -detleft - detright
    else:
        return _sign_of(det), det, True

    errbound = k * detsum
    certain = abs(det) >= errbound
    return _sign_of(det), det, certain


def stage_a_jts_master(a: Point, b: Point, q: Point) -> Tuple[str, float, bool]:
    """Mirror of master CGAlgorithmsDD.orientationIndexFilter (DP_SAFE_EPSILON)."""
    detleft, detright, det = det_parts(a, b, q)
    return _detsum_certain(detleft, detright, det, JTS_DP_SAFE_EPSILON)


def stage_a_shewchuk(a: Point, b: Point, q: Point) -> Tuple[str, float, bool]:
    """Shewchuk Stage A permanent-style filter (corpus / predicates.c shape)."""
    detleft, detright, det = det_parts(a, b, q)
    return _detsum_certain(detleft, detright, det, CCWERRBOUND_A)


def corpus_vectors() -> List[Vec]:
    v: List[Vec] = []

    # --- Certified-style pins (EXPECTED set) ---
    v.append(Vec("pin_ccw_unit", (0.0, 0.0), (1.0, 0.0), (0.0, 1.0), "POS", "area +1/2"))
    v.append(Vec("pin_cw_unit", (0.0, 0.0), (0.0, 1.0), (1.0, 0.0), "NEG", "area -1/2"))
    v.append(Vec("pin_collinear_x", (0.0, 0.0), (2.0, 0.0), (1.0, 0.0), "ZERO", "on segment"))
    v.append(Vec("pin_collinear_diag", (0.0, 0.0), (2.0, 2.0), (1.0, 1.0), "ZERO", "diagonal"))
    v.append(Vec("int_tri", (0.0, 0.0), (4.0, 0.0), (0.0, 3.0), "POS", "3-4-5 area"))
    v.append(Vec("int_vertex", (0.0, 0.0), (4.0, 0.0), (0.0, 0.0), "ZERO", "q = a"))
    v.append(Vec("int_vertex_b", (0.0, 0.0), (4.0, 0.0), (4.0, 0.0), "ZERO", "q = b"))
    v.append(Vec("int_mid_edge", (0.0, 0.0), (4.0, 0.0), (2.0, 0.0), "ZERO", "mid edge"))

    # Near-collinear ladder (filter stress; EXPECTED only when far enough)
    v.append(
        Vec(
            "near_col_1e-6",
            (0.0, 0.0),
            (1.0, 0.0),
            (0.5, 1e-6),
            "POS",
            "clear of 1e-15 band",
        )
    )
    v.append(
        Vec(
            "near_col_1e-8",
            (0.0, 0.0),
            (1.0, 0.0),
            (0.5, 1e-8),
            "POS",
            "slightly above segment",
        )
    )
    v.append(
        Vec(
            "near_col_1e-12",
            (0.0, 0.0),
            (1.0, 0.0),
            (0.5, 1e-12),
            None,
            "may sit near Shewchuk/Ozaki bound",
        )
    )
    v.append(
        Vec(
            "near_col_1e-14",
            (0.0, 0.0),
            (1.0, 0.0),
            (0.5, 1e-14),
            None,
            "deep near-col; expect filter UNCERTAIN on some filters",
        )
    )
    v.append(
        Vec(
            "near_col_1e-16",
            (0.0, 0.0),
            (1.0, 0.0),
            (0.5, 1e-16),
            None,
            "sub-ulp of unit segment half-length scale",
        )
    )
    v.append(
        Vec(
            "near_col_neg_1e-12",
            (0.0, 0.0),
            (1.0, 0.0),
            (0.5, -1e-12),
            None,
            "mirror below segment",
        )
    )

    # Large magnitude (homothety preserves exact sign)
    for s, tag in ((1e6, "1e6"), (1e8, "1e8"), (1e12, "1e12")):
        v.append(
            Vec(
                f"large_ccw_{tag}",
                (0.0, 0.0),
                (s, 0.0),
                (0.0, s),
                "POS",
                f"homothetic CCW scale={tag}",
            )
        )
        v.append(
            Vec(
                f"large_near_col_{tag}",
                (0.0, 0.0),
                (s, 0.0),
                (0.5 * s, 1e-6 * s),
                None,
                f"near-col at scale {tag}",
            )
        )

    # JTS-style nearly collinear at ~1e6 (common DD fallback band)
    v.append(
        Vec(
            "jts_style_near_col",
            (2089426.5233462777, 1180182.3877339689),
            (2085646.6891757075, 1195618.7333999649),
            (2099870.0, 1141480.0),
            None,
            "near-collinear geographic-scale sample",
        )
    )

    # Opposite-sign detleft/detright → JTS-master / Shewchuk early CERTAIN
    # (a above-right of q, b above-left of q → mixed product signs)
    v.append(
        Vec(
            "opp_sign_ccw",
            (1.0, 0.0),
            (0.0, 1.0),
            (0.0, 0.0),
            "POS",
            "detleft/detright opposite signs; early CERTAIN on detsum filters",
        )
    )
    v.append(
        Vec(
            "opp_sign_cw",
            (0.0, 1.0),
            (1.0, 0.0),
            (0.0, 0.0),
            "NEG",
            "opposite-sign products; CW",
        )
    )

    # Boundary between JTS 1e-15 and Ozaki ~3.33e-16
    # For unit segment a=(0,0), b=(1,0), q=(0.5,h): detleft=0, detright=-0.5*h? wait
    # ax=-0.5, ay=-h, bx=0.5, by=-h
    # detleft = ax*by = (-0.5)*(-h) = 0.5 h
    # detright = ay*bx = (-h)*(0.5) = -0.5 h
    # det = h
    # Actually with a=(0,0), b=(1,0), q=(0.5,h):
    # ax=-0.5, ay=-h, bx=0.5, by=-h
    # detleft=(-0.5)*(-h)=0.5h, detright=(-h)*(0.5)=-0.5h, det=h
    # detleft and detright opposite signs → both detsum filters early CERTAIN
    # So the 1e-15 vs Ozaki gap needs same-sign products.
    #
    # Same-sign regime: a=(0,0), b=(1,1), q=(1, 1-h) with small h above the diagonal?
    # Better classic: a=(0,0), b=(2,1), q=(1, 0.5 + eps) near the line y=x/2.
    # Line through (0,0)-(2,1): y = 0.5 x. Point (1, 0.5 + h).
    # ax=-1, ay=-(0.5+h), bx=1, by=0.5-(0.5+h)=-h
    # detleft = (-1)*(-h)=h
    # detright = (-(0.5+h))*(1) = -(0.5+h)
    # det = h + 0.5 + h = 0.5 + 2h  — not tiny.
    #
    # Use a=(0,0), b=(1,0.5), q=(2, 1+h) extension of segment (collinear would be h=0).
    # ax=-2, ay=-(1+h), bx=-1, by=0.5-(1+h)=-0.5-h
    # detleft = (-2)*(-0.5-h) = 1+2h
    # detright = (-(1+h))*(-1) = 1+h
    # det = (1+2h)-(1+h)=h
    # both positive when h small → same-sign detsum path.
    for h, tag in (
        (1e-12, "1e-12"),
        (1e-14, "1e-14"),
        (1e-15, "1e-15"),
        (2e-15, "2e-15"),
        (5e-16, "5e-16"),
        (3.3e-16, "3p3e-16"),
        (1e-16, "1e-16"),
    ):
        v.append(
            Vec(
                f"samesign_h_{tag}",
                (0.0, 0.0),
                (1.0, 0.5),
                (2.0, 1.0 + h),
                None,
                f"same-sign products; h={tag}; detsum vs Ozaki band probe",
            )
        )
        v.append(
            Vec(
                f"samesign_h_neg_{tag}",
                (0.0, 0.0),
                (1.0, 0.5),
                (2.0, 1.0 - h),
                None,
                f"same-sign products; h=-{tag}",
            )
        )

    # Scaled same-sign band (geographic-ish magnitudes)
    for scale in (1e3, 1e6):
        h = 1e-10 * scale  # relative ~1e-10 of coordinate scale
        v.append(
            Vec(
                f"samesign_scaled_{scale:g}",
                (0.0, 0.0),
                (scale, 0.5 * scale),
                (2.0 * scale, 1.0 * scale + h),
                None,
                f"same-sign near-col at scale {scale:g}",
            )
        )

    # Collinear floating-point noise (expected ZERO or tiny; open)
    v.append(
        Vec(
            "fp_almost_col",
            (0.1, 0.1),
            (0.2, 0.2),
            (0.3, 0.3),
            None,
            "decimal .1 chain; may be exact-zero or not in b64",
        )
    )
    v.append(
        Vec(
            "fp_almost_col_rev",
            (0.3, 0.3),
            (0.1, 0.1),
            (0.2, 0.2),
            None,
            "decimal .1 reverse order",
        )
    )

    # Degenerate / zero-length edge
    v.append(
        Vec(
            "zero_edge",
            (1.0, 2.0),
            (1.0, 2.0),
            (3.0, 4.0),
            "ZERO",
            "a = b; det = 0",
        )
    )

    # Antisymmetry check pair
    v.append(
        Vec(
            "anti_abq",
            (0.0, 0.0),
            (3.0, 0.0),
            (1.0, 2.0),
            "POS",
            "antisym partner of anti_baq",
        )
    )
    v.append(
        Vec(
            "anti_baq",
            (3.0, 0.0),
            (0.0, 0.0),
            (1.0, 2.0),
            "NEG",
            "swap a/b flips sign",
        )
    )

    # Mesh-lane spillover: orientation of GEOS 955 triangle (CCW check)
    v.append(
        Vec(
            "geos955_abc_orient",
            (18.68285714285716, 100.105),
            (13.41, 104.82100000000001),
            (13.41, 107.179),
            None,
            "GEOS 955 / jts#1171 triangle orientation (mesh spillover)",
        )
    )

    return v


def resolve_oracle_cmd(args: argparse.Namespace) -> List[str]:
    if args.oracle:
        return [args.oracle]
    if args.wsl_oracle:
        return ["wsl.exe", "-e", args.wsl_oracle]
    env = os.environ.get("ORACLE_BIN")
    if env and os.path.isfile(env):
        return [env]
    local = os.path.join(os.path.dirname(__file__), "oracle_bin")
    if os.path.isfile(local):
        return [local]
    wsl = os.environ.get(
        "WSL_ORACLE_BIN", "/home/user/nettopologysuite.proofs/oracle/oracle_bin"
    )
    return ["wsl.exe", "-e", wsl]


def resolve_ffi_probe(args: argparse.Namespace) -> Optional[List[str]]:
    if args.ffi_probe:
        return [args.ffi_probe]
    if args.wsl_ffi_probe:
        return ["wsl.exe", "-e", args.wsl_ffi_probe]
    env = os.environ.get("FFI_PROBE")
    if env and os.path.isfile(env):
        return [env]
    local = os.path.join(os.path.dirname(__file__), "ffi_probe")
    if os.path.isfile(local):
        return [local]
    # Prefer WSL-built probe if present under the Windows mount.
    wsl_probe = os.environ.get(
        "WSL_FFI_PROBE",
        "/mnt/c/com/github/grootstebozewolf/NetTopologySuite.Proofs/oracle/ffi_probe",
    )
    # Try local Windows path equivalent of the mount for existence check.
    win_guess = os.path.join(os.path.dirname(__file__), "ffi_probe")
    if os.path.isfile(win_guess):
        return [win_guess]
    # Probe may only exist as a Linux binary in WSL workspace clone.
    return None


def run_orient_exact(oracle_cmd: Sequence[str], a: Point, b: Point, q: Point) -> str:
    payload = (
        "ORIENT_EXACT\n"
        f"{a[0]} {a[1]}\n"
        f"{b[0]} {b[1]}\n"
        f"{q[0]} {q[1]}\n"
    )
    proc = subprocess.run(
        list(oracle_cmd),
        input=payload,
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"oracle exit {proc.returncode}: {proc.stderr.strip()} {proc.stdout.strip()}"
        )
    line = proc.stdout.strip().splitlines()[-1].strip()
    tok = line.split()[0].upper()
    if tok in ("POS", "NEG", "ZERO", "NAN"):
        return tok
    raise RuntimeError(f"bad ORIENT_EXACT output: {line!r}")


def run_ffi_filtered(
    probe_cmd: Sequence[str], a: Point, b: Point, q: Point
) -> Tuple[int, float]:
    """ffi_probe ORIENT_FILTERED → (sign_code, orient2d bits as float via hex)."""
    payload = f"{a[0]} {a[1]} {b[0]} {b[1]} {q[0]} {q[1]}\n"
    proc = subprocess.run(
        list(probe_cmd) + ["ORIENT_FILTERED"],
        input=payload,
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"ffi_probe exit {proc.returncode}: {proc.stderr.strip()} {proc.stdout.strip()}"
        )
    parts = proc.stdout.strip().split()
    code = int(parts[0])
    bits_hex = parts[1].lstrip("#")
    val = struct.unpack(">d", bytes.fromhex(bits_hex.zfill(16)))[0]
    return code, val


def code_to_sign(code: int) -> str:
    return {1: "POS", -1: "NEG", 0: "ZERO", 2: "NAN", 3: "UNCERTAIN"}.get(
        code, f"CODE{code}"
    )


def cert_tag(cert: bool) -> str:
    return "CERT" if cert else "UNC"


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--oracle", help="Path to oracle_bin")
    ap.add_argument("--wsl-oracle", help="Linux path via wsl.exe -e")
    ap.add_argument("--ffi-probe", help="Optional path to ffi_probe")
    ap.add_argument("--wsl-ffi-probe", help="Optional Linux ffi_probe via wsl")
    ap.add_argument(
        "--out",
        default=os.path.join(os.path.dirname(__file__), "jts1093_orient_vectors.txt"),
    )
    args = ap.parse_args()

    oracle_cmd = resolve_oracle_cmd(args)
    ffi_cmd = resolve_ffi_probe(args)

    try:
        pin = run_orient_exact(oracle_cmd, (0.0, 0.0), (1.0, 0.0), (0.0, 1.0))
    except Exception as e:
        print(f"FATAL: oracle unavailable ({oracle_cmd}): {e}", file=sys.stderr)
        return 2
    if pin != "POS":
        print(f"FATAL: ORIENT_EXACT pin failed: {pin} (expected POS)", file=sys.stderr)
        return 2
    print(f"Oracle ORIENT_EXACT pin OK: {pin}  via {oracle_cmd}")
    if ffi_cmd:
        try:
            c, _ = run_ffi_filtered(ffi_cmd, (0.0, 0.0), (1.0, 0.0), (0.0, 1.0))
            print(f"FFI ORIENT_FILTERED pin: code={c} ({code_to_sign(c)}) via {ffi_cmd}")
        except Exception as e:
            print(f"WARN: FFI probe failed (continuing without FFI): {e}")
            ffi_cmd = None
    else:
        print("FFI probe: (none — oracle-only)")

    vecs = corpus_vectors()
    lines = [
        "# JTS #1093 Ozaki orientation filter scout",
        "# topic: precision  epic: #66",
        f"# OZAKI_K = {OZAKI_K!r}",
        f"# JTS_DP_SAFE_EPSILON = {JTS_DP_SAFE_EPSILON!r}",
        f"# CCWERRBOUND_A (Shewchuk) = {CCWERRBOUND_A!r}",
        "# Columns: name EXACT JTS_MASTER OZAKI SHEW FFI_FILT note",
        "# CERT = filter commits sign; UNC = escalate to DD/exact",
        "#",
    ]

    n_ozaki_conflict = 0
    n_shew_conflict = 0
    n_jts_conflict = 0
    n_ozaki_unc = 0
    n_shew_unc = 0
    n_jts_unc = 0
    n_ozaki_vs_jts = 0  # Ozaki CERTAIN, JTS-master UNCERTAIN (PR win)
    n_jts_vs_ozaki = 0
    n_ozaki_vs_shew = 0
    n_shew_vs_ozaki = 0
    n_expected_fail = 0
    failures: List[str] = []
    highlights: List[str] = []

    for vec in vecs:
        exact = run_orient_exact(oracle_cmd, vec.a, vec.b, vec.q)
        o_sign, _o_det, o_cert = stage_a_ozaki(vec.a, vec.b, vec.q)
        s_sign, _s_det, s_cert = stage_a_shewchuk(vec.a, vec.b, vec.q)
        j_sign, _j_det, j_cert = stage_a_jts_master(vec.a, vec.b, vec.q)

        if not o_cert:
            n_ozaki_unc += 1
        if not s_cert:
            n_shew_unc += 1
        if not j_cert:
            n_jts_unc += 1
        if o_cert and not j_cert:
            n_ozaki_vs_jts += 1
            highlights.append(
                f"{vec.name}: Ozaki CERTAIN {o_sign} while JTS-master UNCERTAIN "
                f"(exact={exact})"
            )
        if j_cert and not o_cert:
            n_jts_vs_ozaki += 1
            highlights.append(
                f"{vec.name}: JTS-master CERTAIN {j_sign} while Ozaki UNCERTAIN "
                f"(exact={exact})"
            )
        if o_cert and not s_cert:
            n_ozaki_vs_shew += 1
        if s_cert and not o_cert:
            n_shew_vs_ozaki += 1

        # CERTAIN commits a concrete sign (incl. ZERO); mismatch vs nonzero exact is conflict.
        if o_cert and exact in ("POS", "NEG") and o_sign != exact:
            n_ozaki_conflict += 1
            failures.append(f"{vec.name}: Ozaki CERTAIN {o_sign} vs exact {exact}")
        if s_cert and exact in ("POS", "NEG") and s_sign != exact:
            n_shew_conflict += 1
            failures.append(f"{vec.name}: Shewchuk CERTAIN {s_sign} vs exact {exact}")
        if j_cert and exact in ("POS", "NEG") and j_sign != exact:
            n_jts_conflict += 1
            failures.append(f"{vec.name}: JTS-master CERTAIN {j_sign} vs exact {exact}")

        if vec.expected is not None and exact != vec.expected:
            n_expected_fail += 1
            failures.append(f"{vec.name}: EXPECTED {vec.expected} exact {exact}")

        ffi_s = "-"
        if ffi_cmd:
            try:
                code, _ = run_ffi_filtered(ffi_cmd, vec.a, vec.b, vec.q)
                ffi_s = code_to_sign(code)
            except Exception as e:
                ffi_s = f"ERR:{e}"

        lines.append(
            f"{vec.name}\tEXACT={exact}\t"
            f"JTS={j_sign}/{cert_tag(j_cert)}\t"
            f"OZAKI={o_sign}/{cert_tag(o_cert)}\t"
            f"SHEW={s_sign}/{cert_tag(s_cert)}\t"
            f"FFI_FILT={ffi_s}\t# {vec.note}"
        )

    summary = [
        "",
        "# --- summary ---",
        f"# vectors={len(vecs)}",
        f"# expected_fail={n_expected_fail}",
        f"# ozaki_certain_vs_exact_conflict={n_ozaki_conflict}",
        f"# shew_certain_vs_exact_conflict={n_shew_conflict}",
        f"# jts_master_certain_vs_exact_conflict={n_jts_conflict}",
        f"# ozaki_uncertain={n_ozaki_unc}",
        f"# shew_uncertain={n_shew_unc}",
        f"# jts_master_uncertain={n_jts_unc}",
        f"# ozaki_tighter_than_jts_master={n_ozaki_vs_jts}",
        f"# jts_master_tighter_than_ozaki={n_jts_vs_ozaki}",
        f"# ozaki_tighter_than_shew={n_ozaki_vs_shew}",
        f"# shew_tighter_than_ozaki={n_shew_vs_ozaki}",
    ]
    lines.extend(summary)

    with open(args.out, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(f"Vectors: {len(vecs)}  → {args.out}")
    print(f"EXPECTED pin failures: {n_expected_fail}")
    print(f"Ozaki CERTAIN vs exact conflicts: {n_ozaki_conflict}")
    print(f"Shewchuk CERTAIN vs exact conflicts: {n_shew_conflict}")
    print(f"JTS-master CERTAIN vs exact conflicts: {n_jts_conflict}")
    print(
        f"UNCERTAIN counts — Ozaki: {n_ozaki_unc}  Shewchuk: {n_shew_unc}  "
        f"JTS-master: {n_jts_unc}"
    )
    print(f"Ozaki tighter than JTS-master (CERT while JTS UNC): {n_ozaki_vs_jts}")
    print(f"JTS-master tighter than Ozaki: {n_jts_vs_ozaki}")
    print(f"Ozaki tighter than corpus Shewchuk: {n_ozaki_vs_shew}")
    print(f"Corpus Shewchuk tighter than Ozaki: {n_shew_vs_ozaki}")
    if highlights:
        print("TIGHTNESS HIGHLIGHTS:")
        for x in highlights:
            print(" ", x)
    if failures:
        print("FAILURES:")
        for x in failures:
            print(" ", x)
        return 1
    print("GATE: GREEN")
    return 0


if __name__ == "__main__":
    sys.exit(main())
