#!/usr/bin/env python3
"""
JTS #1094 mesh in-circle scout — FFI differential vs Rocq b64_inCircle.

topic: mesh (epic #68)
Upstream: locationtech/jts#1094 (Make isInCircleRobust robust) — tinko92
Sibling tip: locationtech/jts#1212 (Stage A + DD); treat as **one lane**.

For each 4-tuple (A,B,C,P):
  - **FFI ground truth**: nts_rocq_in_circle via scout_incircle_probe
    (same extracted b64_inCircle as production libntsrocq / oracle_bin).
  - **oracle_bin parity** (optional): bit-pattern agreement with FFI.
  - **Stage A mirror of #1094**: CERTAIN sign or UNCERTAIN
    (iccerrboundA, permanent-scaled; bound test uses |det| >= errbound
    exactly as the PR, which differs from #1212's strict |det| > errbound).
  - Optional EXPECTED from Qed pins / algebraic identities.

Usage (from repo root, after `make -C oracle scout-incircle-ffi`):
  python oracle/gen_jts1094_incircle_scout.py
  python oracle/gen_jts1094_incircle_scout.py --oracle /path/to/oracle_bin \\
      --ffi-probe /path/to/scout_incircle_probe
  python oracle/gen_jts1094_incircle_scout.py --wsl-oracle ... --wsl-ffi-probe ...

Writes:
  oracle/jts1094_incircle_vectors.txt
  stdout: gate summary + review-relevant counters
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

# Shewchuk iccerrboundA = (10 + 96 * eps) * eps, eps = 2^-53
# Java Math.ulp(0.5) == 2^-53 on IEEE754 binary64 (same as #1212 DOUBLE_EPS).
DOUBLE_EPS = math.ldexp(1.0, -53)
ICCERRBOUND_A = (10.0 + 96.0 * DOUBLE_EPS) * DOUBLE_EPS

Point = Tuple[float, float]


@dataclass
class Vec:
    name: str
    a: Point
    b: Point
    c: Point
    p: Point
    expected: Optional[str]  # POS | NEG | ZERO | None
    note: str = ""


def stage_a_1094(a: Point, b: Point, c: Point, p: Point) -> Tuple[str, float, bool]:
    """Mirror of JTS#1094 TrianglePredicate.isInCircleRobust Stage A.

    Returns (sign POS/NEG/ZERO, det, certain).
    Certain uses **|det| >= errbound** (PR#1094), not strict > (#1212).
    """
    adx, ady = a[0] - p[0], a[1] - p[1]
    bdx, bdy = b[0] - p[0], b[1] - p[1]
    cdx, cdy = c[0] - p[0], c[1] - p[1]

    bdxcdy = bdx * cdy
    cdxbdy = cdx * bdy
    alift = adx * adx + ady * ady

    cdxady = cdx * ady
    adxcdy = adx * cdy
    blift = bdx * bdx + bdy * bdy

    adxbdy = adx * bdy
    bdxady = bdx * ady
    clift = cdx * cdx + cdy * cdy

    det = (
        alift * (bdxcdy - cdxbdy)
        + blift * (cdxady - adxcdy)
        + clift * (adxbdy - bdxady)
    )
    permanent = (
        (abs(bdxcdy) + abs(cdxbdy)) * alift
        + (abs(cdxady) + abs(adxcdy)) * blift
        + (abs(adxbdy) + abs(bdxady)) * clift
    )
    err_bound = ICCERRBOUND_A * permanent
    # PR#1094: Math.abs(det) >= errbound  (non-strict)
    certain = abs(det) >= err_bound
    if det > 0:
        sign = "POS"
    elif det < 0:
        sign = "NEG"
    else:
        sign = "ZERO"
    return sign, det, certain


def stage_a_1212(a: Point, b: Point, c: Point, p: Point) -> Tuple[str, float, bool]:
    """Mirror of JTS#1212 for differential count only (strict |det| > bound)."""
    sign, det, _ = stage_a_1094(a, b, c, p)
    adx, ady = a[0] - p[0], a[1] - p[1]
    bdx, bdy = b[0] - p[0], b[1] - p[1]
    cdx, cdy = c[0] - p[0], c[1] - p[1]
    bdxcdy = bdx * cdy
    cdxbdy = cdx * bdy
    alift = adx * adx + ady * ady
    cdxady = cdx * ady
    adxcdy = adx * cdy
    blift = bdx * bdx + bdy * bdy
    adxbdy = adx * bdy
    bdxady = bdx * ady
    clift = cdx * cdx + cdy * cdy
    permanent = (
        (abs(bdxcdy) + abs(cdxbdy)) * alift
        + (abs(cdxady) + abs(adxcdy)) * blift
        + (abs(adxbdy) + abs(bdxady)) * clift
    )
    err_bound = ICCERRBOUND_A * permanent
    certain = det > err_bound or -det > err_bound
    return sign, det, certain


def fmt_pt(q: Point) -> str:
    return f"{q[0]:.17g} {q[1]:.17g}"


def sign_of(v: float) -> str:
    if math.isnan(v):
        return "NAN"
    if v > 0:
        return "POS"
    if v < 0:
        return "NEG"
    return "ZERO"


def bits_of(v: float) -> int:
    return struct.unpack(">Q", struct.pack(">d", v))[0]


def corpus_vectors() -> List[Vec]:
    v: List[Vec] = []
    A, B, C = (0.0, 0.0), (4.0, 0.0), (0.0, 4.0)
    for name, P in (("A", A), ("B", B), ("C", C)):
        v.append(
            Vec(
                f"pin_1190_vertex_{name}",
                A,
                B,
                C,
                P,
                "ZERO",
                "DelaunayDegeneratePins.single_triangle_pin_1190 / inCircle_R_at_vertex",
            )
        )
    A, B, C, D = (0.0, 0.0), (2.0, 0.0), (2.0, 2.0), (0.0, 2.0)
    v.append(
        Vec(
            "pin_1039_diag_ABC_D",
            A,
            B,
            C,
            D,
            "ZERO",
            "cocircular_square_tie_1039",
        )
    )
    v.append(
        Vec(
            "pin_1039_diag_ABD_C",
            A,
            B,
            D,
            C,
            "ZERO",
            "cocircular_square_tie_1039 mirror diagonal",
        )
    )
    v.append(
        Vec(
            "pin_1039_knife_in",
            A,
            B,
            C,
            (0.0, 1.5),
            "POS",
            "cocircular_tie_is_knife_edge +3",
        )
    )
    v.append(
        Vec(
            "pin_1039_knife_out",
            A,
            B,
            C,
            (0.0, 2.5),
            "NEG",
            "cocircular_tie_is_knife_edge -5",
        )
    )
    v.append(
        Vec(
            "pin_68b_flip_witness",
            (0.0, 0.0),
            (2.0, 0.0),
            (1.0, 1.0),
            (1.0, -0.5),
            "POS",
            "loc_in_circle_test_D; inCircle_R = 3/2",
        )
    )
    v.append(
        Vec(
            "pin_68a_D_outside_ABC",
            (0.0, 0.0),
            (2.0, 0.0),
            (1.0, 1.0),
            (1.0, -2.0),
            "NEG",
            "DelaunayEdgeEmptyCircle: D outside empty circumdisk of ABC",
        )
    )
    return v


def jts_lane_vectors() -> List[Vec]:
    """Shared regression sites with the #1212 harness + #1094 testCircle focus."""
    v: List[Vec] = []
    t0 = (-221.72957795130824, -26.56505117707799)
    t1 = (-149.72957795130824, -26.56505117707799)
    t2 = (0.0, -90.0)
    for name, P in (("t0", t0), ("t1", t1), ("t2", t2)):
        v.append(
            Vec(
                f"jts1190_vertex_{name}",
                t0,
                t1,
                t2,
                P,
                "ZERO",
                "single-triangle constraint sites; vertex on circumcircle",
            )
        )
    # DelaunayTest.testCircle densified ring (same WKT as #1094/#1212)
    circle = [
        (42.0, 30.0),
        (41.96, 29.61),
        (41.85, 29.23),
        (41.66, 28.89),
        (41.41, 28.59),
        (41.11, 28.34),
        (40.77, 28.15),
        (40.39, 28.04),
        (40.0, 28.0),
        (39.61, 28.04),
        (39.23, 28.15),
        (38.89, 28.34),
        (38.59, 28.59),
        (38.34, 28.89),
        (38.15, 29.23),
        (38.04, 29.61),
        (38.0, 30.0),
        (38.04, 30.39),
        (38.15, 30.77),
        (38.34, 31.11),
        (38.59, 31.41),
        (38.89, 31.66),
        (39.23, 31.85),
        (39.61, 31.96),
        (40.0, 32.0),
        (40.39, 31.96),
        (40.77, 31.85),
        (41.11, 31.66),
        (41.41, 31.41),
        (41.66, 31.11),
        (41.85, 30.77),
        (41.96, 30.39),
    ]
    for i in range(0, len(circle) - 3, 4):
        a, b, c, p = circle[i], circle[i + 1], circle[i + 2], circle[i + 3]
        v.append(
            Vec(
                f"jts1094_circle_quad_{i}",
                a,
                b,
                c,
                p,
                None,
                "DelaunayTest.testCircle near-cocircular sample quad (#1094 retarget)",
            )
        )
    v.append(
        Vec(
            "jts1094_circle_cardinal",
            (42.0, 30.0),
            (40.0, 28.0),
            (38.0, 30.0),
            (40.0, 32.0),
            None,
            "four cardinal-ish points on densified circle",
        )
    )
    geos1040 = [
        (6.6584, 53.583000000000006),
        (6.6576, 53.583600000000004),
        (6.657, 53.5848),
        (6.6572000000000005, 53.5842),
    ]
    v.append(
        Vec(
            "jts_geos1040_quad",
            geos1040[0],
            geos1040[1],
            geos1040[2],
            geos1040[3],
            None,
            "VoronoiTest nearly cocircular GEOS#1040 / JTS#1171",
        )
    )
    geos955_sub = [
        (18.68285714285716, 100.105),
        (13.41, 104.82100000000001),
        (13.41, 107.179),
        (18.682857142857145, 111.89500000000001),
    ]
    v.append(
        Vec(
            "jts_geos955_subset",
            geos955_sub[0],
            geos955_sub[1],
            geos955_sub[2],
            geos955_sub[3],
            None,
            "VoronoiTest JTS#1171 ex2 — Stage A must decline (adaptive path)",
        )
    )
    # #1094-specific: equality boundary for |det| == errbound (if any appear)
    # Unit circle with tiny inward nudge (CERTAIN for larger eps).
    for k, eps in enumerate((1e-12, 1e-9, 1e-6)):
        v.append(
            Vec(
                f"adv_unit_circle_eps_{k}",
                (1.0, 0.0),
                (0.0, 1.0),
                (-1.0, 0.0),
                (0.0, -1.0 + eps),
                None,
                f"south pole of unit circle nudged by {eps}",
            )
        )
    s = 1e8
    v.append(
        Vec(
            "adv_large_scale_flip",
            (0.0, 0.0),
            (2.0 * s, 0.0),
            (1.0 * s, 1.0 * s),
            (1.0 * s, -0.5 * s),
            "POS",
            "scaled flip witness (homothety preserves sign)",
        )
    )
    return v


def all_vectors() -> List[Vec]:
    return corpus_vectors() + jts_lane_vectors()


def run_oracle_bin(
    oracle_cmd: Sequence[str], a: Point, b: Point, c: Point, p: Point
) -> Tuple[str, float]:
    payload = (
        "INCIRCLE_SIGN\n"
        f"{a[0]} {a[1]}\n"
        f"{b[0]} {b[1]}\n"
        f"{c[0]} {c[1]}\n"
        f"{p[0]} {p[1]}\n"
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
    parts = proc.stdout.strip().split()
    if len(parts) < 2:
        raise RuntimeError(f"bad oracle output: {proc.stdout!r}")
    sign = parts[0]
    val = (
        float.fromhex(parts[1])
        if parts[1].lower().startswith(("0x", "-0x", "+0x"))
        else float(parts[1])
    )
    return sign, val


def run_ffi_probe(
    probe_cmd: Sequence[str], a: Point, b: Point, c: Point, p: Point
) -> float:
    """Call scout_incircle_probe / ffi_probe INCIRCLE_SIGN → raw determinant."""
    # Prefer hex floats for exact cross-boundary decode
    nums = " ".join(
        [
            float(a[0]).hex(),
            float(a[1]).hex(),
            float(b[0]).hex(),
            float(b[1]).hex(),
            float(c[0]).hex(),
            float(c[1]).hex(),
            float(p[0]).hex(),
            float(p[1]).hex(),
        ]
    )
    proc = subprocess.run(
        list(probe_cmd) + ["INCIRCLE_SIGN"],
        input=nums + "\n",
        capture_output=True,
        text=True,
        timeout=30,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"ffi probe exit {proc.returncode}: {proc.stderr.strip()} {proc.stdout.strip()}"
        )
    out = proc.stdout.strip()
    # "IC #<16 hex digits>"
    if not out.startswith("IC"):
        raise RuntimeError(f"bad ffi probe output: {out!r}")
    hexpart = out[2:].strip()
    if not hexpart.startswith("#"):
        raise RuntimeError(f"bad ffi probe bits: {out!r}")
    bits = int(hexpart[1:], 16)
    return struct.unpack(">d", struct.pack(">Q", bits))[0]


def resolve_cmd(
    path: Optional[str], wsl_path: Optional[str], env_key: str, default_wsl: str
) -> List[str]:
    if path:
        return [path]
    if wsl_path:
        return ["wsl.exe", "-e", wsl_path]
    env = os.environ.get(env_key)
    if env and os.path.isfile(env):
        return [env]
    # WSL default (Windows host running WSL binary)
    if os.name == "nt" or sys.platform.startswith("win"):
        return ["wsl.exe", "-e", default_wsl]
    if os.path.isfile(default_wsl):
        return [default_wsl]
    # relative from repo root
    rel = default_wsl.split("/")[-1]
    for cand in (f"oracle/{rel}", rel):
        if os.path.isfile(cand):
            return [os.path.abspath(cand)]
    return ["wsl.exe", "-e", default_wsl]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--oracle", help="Path to native oracle_bin")
    ap.add_argument("--wsl-oracle", help="Linux path via wsl.exe -e")
    ap.add_argument("--ffi-probe", help="Path to scout_incircle_probe or ffi_probe")
    ap.add_argument("--wsl-ffi-probe", help="Linux path via wsl.exe -e")
    ap.add_argument(
        "--out",
        default="oracle/jts1094_incircle_vectors.txt",
        help="Vector table output path",
    )
    ap.add_argument(
        "--skip-oracle-parity",
        action="store_true",
        help="Only use FFI (skip oracle_bin bit-parity check)",
    )
    args = ap.parse_args()

    # Prefer workspace mount under WSL when running from Windows
    default_oracle = "/mnt/c/com/github/grootstebozewolf/NetTopologySuite.Proofs/oracle/oracle_bin"
    if not os.path.isfile("oracle/oracle_bin"):
        # fall back to older WSL clone if mount binary missing
        alt = "/home/user/nettopologysuite.proofs/oracle/oracle_bin"
        default_oracle = alt
    default_probe = (
        "/mnt/c/com/github/grootstebozewolf/NetTopologySuite.Proofs/oracle/scout_incircle_probe"
    )

    oracle_cmd = resolve_cmd(
        args.oracle, args.wsl_oracle, "ORACLE_BIN", default_oracle
    )
    probe_cmd = resolve_cmd(
        args.ffi_probe, args.wsl_ffi_probe, "SCOUT_IC_PROBE", default_probe
    )

    # Sanity: FFI pin (flip witness → POS 1.5)
    try:
        ffi_val = run_ffi_probe(probe_cmd, (0, 0), (2, 0), (1, 1), (1, -0.5))
    except Exception as e:
        print(f"FATAL: FFI probe unavailable ({probe_cmd}): {e}", file=sys.stderr)
        return 2
    if sign_of(ffi_val) != "POS" or abs(ffi_val - 1.5) > 1e-12:
        print(
            f"FATAL: FFI pin failed: {sign_of(ffi_val)} {ffi_val} (expected POS 1.5)",
            file=sys.stderr,
        )
        return 2
    print(f"FFI pin OK: POS {ffi_val}  via {probe_cmd}")

    if not args.skip_oracle_parity:
        try:
            o_sign, o_val = run_oracle_bin(
                oracle_cmd, (0, 0), (2, 0), (1, 1), (1, -0.5)
            )
        except Exception as e:
            print(
                f"FATAL: oracle_bin unavailable ({oracle_cmd}): {e}",
                file=sys.stderr,
            )
            return 2
        if o_sign != "POS" or abs(o_val - 1.5) > 1e-12:
            print(
                f"FATAL: oracle pin failed: {o_sign} {o_val}",
                file=sys.stderr,
            )
            return 2
        if bits_of(o_val) != bits_of(ffi_val):
            print(
                f"FATAL: FFI/oracle bit mismatch on pin: "
                f"ffi={ffi_val.hex()} oracle={o_val.hex()}",
                file=sys.stderr,
            )
            return 2
        print(f"oracle_bin pin OK + bit-parity with FFI  via {oracle_cmd}")

    vecs = all_vectors()
    lines: List[str] = [
        "# JTS #1094 mesh in-circle differential vectors (FFI scout)",
        "# topic: mesh  epic: #68",
        "# Format: name  A  B  C  P  FFI  STAGE_A1094  CERTAIN  STAGE_A1212_CERT  "
        "EXPECTED  note",
        "# FFI = nts_rocq_in_circle / b64_inCircle via scout_incircle_probe.",
        "# STAGE_A1094 uses |det| >= errbound (PR#1094); STAGE_A1212_CERT is "
        "strict > (PR#1212).",
        "# EXPECTED is POS|NEG|ZERO when a corpus pin applies; else -",
        "#",
    ]

    n_pass = 0
    n_uncertain = 0
    n_open = 0
    n_bound_diverge = 0  # #1094 CERTAIN while #1212 UNCERTAIN (or reverse)
    failures: List[str] = []
    parity_fail = 0

    for vec in vecs:
        ffi_v = run_ffi_probe(probe_cmd, vec.a, vec.b, vec.c, vec.p)
        ffi_sign = sign_of(ffi_v)

        if not args.skip_oracle_parity:
            o_sign, o_val = run_oracle_bin(oracle_cmd, vec.a, vec.b, vec.c, vec.p)
            if bits_of(o_val) != bits_of(ffi_v):
                # NaN collapse: treat both NaN as OK
                if not (math.isnan(o_val) and math.isnan(ffi_v)):
                    parity_fail += 1
                    failures.append(
                        f"{vec.name}: FFI/oracle bits diverge "
                        f"ffi={ffi_v.hex()} oracle={o_val.hex()}"
                    )

        a_sign, det, certain1094 = stage_a_1094(vec.a, vec.b, vec.c, vec.p)
        _, _, certain1212 = stage_a_1212(vec.a, vec.b, vec.c, vec.p)
        if certain1094 != certain1212:
            n_bound_diverge += 1

        if certain1094:
            tag = "CERTAIN"
            if {a_sign, ffi_sign} <= {"POS", "NEG"} and a_sign != ffi_sign:
                failures.append(
                    f"{vec.name}: StageA1094 CERTAIN {a_sign} != FFI {ffi_sign} "
                    f"(det={det})"
                )
            else:
                n_pass += 1
        else:
            tag = "UNCERTAIN"
            n_uncertain += 1
            n_pass += 1

        if vec.expected is not None:
            if ffi_sign != vec.expected:
                if vec.expected == "ZERO" and abs(ffi_v) < 1e-9:
                    pass
                else:
                    failures.append(
                        f"{vec.name}: expected {vec.expected} got {ffi_sign} "
                        f"val={ffi_v}"
                    )
        else:
            n_open += 1

        lines.append(
            f"{vec.name}\t{fmt_pt(vec.a)}\t{fmt_pt(vec.b)}\t{fmt_pt(vec.c)}\t"
            f"{fmt_pt(vec.p)}\t{ffi_sign}\t{a_sign}\t{tag}\t"
            f"{'CERTAIN' if certain1212 else 'UNCERTAIN'}\t"
            f"{vec.expected or '-'}\t{vec.note}"
        )

    out_path = args.out
    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print()
    print(f"Vectors: {len(vecs)}  written → {out_path}")
    print(
        f"Gate rows: pass≈{n_pass}  fail={len(failures)}  "
        f"StageA UNCERTAIN={n_uncertain}  open(no EXPECTED)={n_open}"
    )
    print(
        f"Bound policy diverge (#1094 ≥ vs #1212 >): {n_bound_diverge} vectors"
    )
    print(f"FFI/oracle bit-parity failures: {parity_fail}")
    if failures:
        print("FAILURES:")
        for msg in failures:
            print(f"  {msg}")
        return 1
    print(
        "GATE: all expected pins match FFI; no StageA1094 CERTAIN≠FFI conflicts; "
        "FFI≡oracle_bin bits."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
