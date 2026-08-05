#!/usr/bin/env python3
"""
JTS #1093 orientation lane — Ozaki filter scout vs corpus exact orient.

topic: precision (epic #66)
Upstream: locationtech/jts#1093 (Ozaki et al. orientationIndexFilter)
Corpus GT: oracle_bin ORIENT_EXACT (zarith / full-plane sign)
Optional:  ffi_probe ORIENT_FILTERED (Shewchuk Stage A via libntsrocq)

What this gates (no new Rocq claimId — ADR-0004 cold):
  I1  Ozaki CERTAIN never disagrees with ORIENT_EXACT sign (nonzero).
  I2  Shewchuk-corpus Stage A CERTAIN never disagrees with exact.
  I3  Report tighter-filter stats: Ozaki CERTAIN when Shewchuk UNCERTAIN.

Ozaki (PR #1093):
  detleft  = (ax-cx)*(by-cy)
  detright = (ay-cy)*(bx-cx)
  det      = detleft - detright
  errbound = |detleft + detright| * 3.3306690621773724e-16
  certain  iff |det| >= errbound

Corpus Shewchuk Stage A (Orientation_b64 / JTS pre-Ozaki shape with
published constant): errbound = (3+16ε)ε * detsum, ε=2^-53, with the
standard detsum construction (see stage_a_shewchuk).

Usage:
  python oracle/gen_jts1093_orient_scout.py
  python oracle/gen_jts1093_orient_scout.py --wsl-oracle /path/to/oracle_bin
  python oracle/gen_jts1093_orient_scout.py --ffi-probe /path/to/ffi_probe
"""
from __future__ import annotations

import argparse
import math
import os
import subprocess
import sys
from dataclasses import dataclass
from typing import List, Optional, Sequence, Tuple

# Ozaki constant from jts#1093 (double literal in CGAlgorithmsDD).
OZAKI_K = 3.3306690621773724e-16

# Shewchuk ε and ccwerrboundA coefficient (Orientation_b64 / predicates.c).
SHEWCHUK_EPS = math.ldexp(1.0, -53)
CCWERRBOUND_A = (3.0 + 16.0 * SHEWCHUK_EPS) * SHEWCHUK_EPS

Point = Tuple[float, float]


@dataclass
class Vec:
    name: str
    a: Point  # p0
    b: Point  # p1
    q: Point  # query
    expected: Optional[str]  # POS | NEG | ZERO | None
    note: str = ""


def det_parts(a: Point, b: Point, q: Point) -> Tuple[float, float, float]:
    """Return (detleft, detright, det) with origin at q (Shewchuk/Ozaki form)."""
    ax, ay = a[0] - q[0], a[1] - q[1]
    bx, by = b[0] - q[0], b[1] - q[1]
    detleft = ax * by
    detright = ay * bx
    return detleft, detright, detleft - detright


def stage_a_ozaki(a: Point, b: Point, q: Point) -> Tuple[str, float, bool]:
    """Mirror of jts#1093 orientationIndexFilter."""
    detleft, detright, det = det_parts(a, b, q)
    errbound = abs(detleft + detright) * OZAKI_K
    certain = abs(det) >= errbound
    if det > 0:
        sign = "POS"
    elif det < 0:
        sign = "NEG"
    else:
        sign = "ZERO"
    return sign, det, certain


def stage_a_shewchuk(a: Point, b: Point, q: Point) -> Tuple[str, float, bool]:
    """Shewchuk Stage A permanent-style filter (corpus / predicates.c shape).

    detsum construction matches the classic public-domain orientation filter:
    if detleft and detright have opposite signs (or either is zero), the sign
    of det is already exact in floating point for this form; else scale.
    """
    detleft, detright, det = det_parts(a, b, q)
    if detleft > 0.0:
        if detright <= 0.0:
            certain = True
            detsum = 0.0
        else:
            detsum = detleft + detright
            certain = False
    elif detleft < 0.0:
        if detright >= 0.0:
            certain = True
            detsum = 0.0
        else:
            detsum = -detleft - detright
            certain = False
    else:
        certain = True
        detsum = 0.0

    if not certain:
        errbound = CCWERRBOUND_A * detsum
        certain = abs(det) >= errbound

    if det > 0:
        sign = "POS"
    elif det < 0:
        sign = "NEG"
    else:
        sign = "ZERO"
    return sign, det, certain


def corpus_vectors() -> List[Vec]:
    v: List[Vec] = []
    # Classic CCW unit right triangle → POS
    v.append(Vec("pin_ccw_unit", (0.0, 0.0), (1.0, 0.0), (0.0, 1.0), "POS", "area +1/2"))
    v.append(Vec("pin_cw_unit", (0.0, 0.0), (0.0, 1.0), (1.0, 0.0), "NEG", "area -1/2"))
    v.append(Vec("pin_collinear_x", (0.0, 0.0), (2.0, 0.0), (1.0, 0.0), "ZERO", "on segment"))
    v.append(Vec("pin_collinear_diag", (0.0, 0.0), (2.0, 2.0), (1.0, 1.0), "ZERO", "diagonal"))
    # Near-collinear at moderate scale
    v.append(
        Vec(
            "near_collinear_1e-8",
            (0.0, 0.0),
            (1.0, 0.0),
            (0.5, 1e-8),
            "POS",
            "slightly above segment",
        )
    )
    v.append(
        Vec(
            "near_collinear_1e-12",
            (0.0, 0.0),
            (1.0, 0.0),
            (0.5, 1e-12),
            None,
            "may be filter-uncertain",
        )
    )
    # Large magnitude (filter stress; exact still defined)
    s = 1e8
    v.append(
        Vec(
            "large_ccw",
            (0.0, 0.0),
            (s, 0.0),
            (0.0, s),
            "POS",
            "homothetic CCW",
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
    # Integer-regime pins (corpus sound_small_int)
    v.append(Vec("int_tri", (0.0, 0.0), (4.0, 0.0), (0.0, 3.0), "POS", "3-4-5 area"))
    v.append(Vec("int_vertex", (0.0, 0.0), (4.0, 0.0), (0.0, 0.0), "ZERO", "q = a"))
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
    # POS / NEG / ZERO / NAN
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
    # "1 #3ff0000000000000" or "3 #..."
    parts = proc.stdout.strip().split()
    code = int(parts[0])
    bits_hex = parts[1].lstrip("#")
    import struct

    val = struct.unpack(">d", bytes.fromhex(bits_hex.zfill(16)))[0]
    return code, val


def code_to_sign(code: int) -> str:
    return {1: "POS", -1: "NEG", 0: "ZERO", 2: "NAN", 3: "UNCERTAIN"}.get(
        code, f"CODE{code}"
    )


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

    # Sanity: ORIENT_EXACT on unit CCW
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
        f"# CCWERRBOUND_A (Shewchuk) = {CCWERRBOUND_A!r}",
        "# Columns: name EXACT OZAKI_SIGN/CERT SHEW_SIGN/CERT FFI_FILT note",
        "#",
    ]

    n_ozaki_conflict = 0
    n_shew_conflict = 0
    n_ozaki_unc = 0
    n_shew_unc = 0
    n_ozaki_tighter = 0  # Ozaki CERTAIN, Shewchuk UNCERTAIN
    n_shew_tighter = 0
    n_expected_fail = 0
    failures: List[str] = []

    for vec in vecs:
        exact = run_orient_exact(oracle_cmd, vec.a, vec.b, vec.q)
        o_sign, o_det, o_cert = stage_a_ozaki(vec.a, vec.b, vec.q)
        s_sign, s_det, s_cert = stage_a_shewchuk(vec.a, vec.b, vec.q)

        if not o_cert:
            n_ozaki_unc += 1
        if not s_cert:
            n_shew_unc += 1
        if o_cert and not s_cert:
            n_ozaki_tighter += 1
        if s_cert and not o_cert:
            n_shew_tighter += 1

        if o_cert and exact in ("POS", "NEG") and o_sign != exact:
            n_ozaki_conflict += 1
            failures.append(f"{vec.name}: Ozaki CERTAIN {o_sign} vs exact {exact}")
        if s_cert and exact in ("POS", "NEG") and s_sign != exact:
            n_shew_conflict += 1
            failures.append(f"{vec.name}: Shewchuk CERTAIN {s_sign} vs exact {exact}")

        if vec.expected is not None and exact != vec.expected:
            if not (vec.expected == "ZERO" and exact == "ZERO"):
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
            f"OZAKI={o_sign}/{'CERT' if o_cert else 'UNC'}\t"
            f"SHEW={s_sign}/{'CERT' if s_cert else 'UNC'}\t"
            f"FFI_FILT={ffi_s}\t# {vec.note}"
        )

    with open(args.out, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(f"Vectors: {len(vecs)}  → {args.out}")
    print(f"EXPECTED pin failures: {n_expected_fail}")
    print(f"Ozaki CERTAIN vs exact conflicts: {n_ozaki_conflict}")
    print(f"Shewchuk CERTAIN vs exact conflicts: {n_shew_conflict}")
    print(f"Ozaki UNCERTAIN: {n_ozaki_unc}  Shewchuk UNCERTAIN: {n_shew_unc}")
    print(f"Ozaki tighter (CERT while Shew UNCERTAIN): {n_ozaki_tighter}")
    print(f"Shewchuk tighter (CERT while Ozaki UNCERTAIN): {n_shew_tighter}")
    if failures:
        print("FAILURES:")
        for x in failures:
            print(" ", x)
        return 1
    print("GATE: GREEN")
    return 0


if __name__ == "__main__":
    sys.exit(main())
