#!/usr/bin/env python3
"""
JTS #311 mesh in-circle lane — design-history Stage A gate (session 3).

topic: mesh (epic #68)
Upstream: locationtech/jts#311 (isInCircleAdapt sketch Java port, Komzpa)
          superseded in product by #1094 (full adaptive) / #1212 (tip: Stage A + DD).

What this script is:
  - Pure-Python mirror of PR #311 Stage A only (not DDFast, not full adapt).
  - Reuses the #1212/#1094 vector bank + #311's own unit-test quads.
  - Compares CERTAIN signs against Rocq INCIRCLE_SIGN when oracle_bin is available.
  - Highlights the #311 ε choice: Math.ulp(1.0) == 2^-52 vs Shewchuk/corpus 2^-53.

What this script is not:
  - A claim that Java isInCircleDDFast equals b64_inCircle bit-for-bit.
  - A reason to dual-track an NTS port of #311.

Usage:
  python oracle/gen_jts311_incircle_history.py
  python oracle/gen_jts311_incircle_history.py --oracle /path/to/oracle_bin
  python oracle/gen_jts311_incircle_history.py --wsl-oracle /home/user/.../oracle_bin

Writes:
  oracle/jts311_incircle_history.txt
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

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
# Shewchuk / corpus / #1212 / #1094: eps = 2^-53
SHEWCHUK_EPS = math.ldexp(1.0, -53)
ICCERRBOUND_A_SHEWCHUK = (10.0 + 96.0 * SHEWCHUK_EPS) * SHEWCHUK_EPS

# PR #311: double epsilon = Math.ulp(1.0)  →  2^-52 on binary64
# (one binade larger than Shewchuk's published machine epsilon for Stage A).
PR311_EPS = math.ulp(1.0)  # == 2^-52
assert PR311_EPS == math.ldexp(1.0, -52)
ICCERRBOUND_A_311 = (10.0 + 96.0 * PR311_EPS) * PR311_EPS

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


def stage_a(
    a: Point,
    b: Point,
    c: Point,
    p: Point,
    iccerrbound_a: float,
) -> Tuple[str, float, bool, float]:
    """Shewchuk in-circle Stage A (translated so P is origin).

    CERTAIN when |det| > errbound (strict), matching both #311 and #1212.
    Returns (sign, det, certain, errbound).
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
    errbound = iccerrbound_a * permanent
    # #311: if (det > errbound) true; if (-det > errbound) false; else DD
    certain = det > errbound or -det > errbound
    if det > 0:
        sign = "POS"
    elif det < 0:
        sign = "NEG"
    else:
        sign = "ZERO"
    return sign, det, certain, errbound


def stage_a_311(a: Point, b: Point, c: Point, p: Point) -> Tuple[str, float, bool, float]:
    return stage_a(a, b, c, p, ICCERRBOUND_A_311)


def stage_a_shewchuk(
    a: Point, b: Point, c: Point, p: Point
) -> Tuple[str, float, bool, float]:
    return stage_a(a, b, c, p, ICCERRBOUND_A_SHEWCHUK)


def fmt_pt(q: Point) -> str:
    return f"{q[0]:.17g} {q[1]:.17g}"


# ---------------------------------------------------------------------------
# Vectors: corpus pins + #1212 bank + #311 unit tests
# ---------------------------------------------------------------------------


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
                "DelaunayDegeneratePins / inCircle_R_at_vertex",
            )
        )
    A, B, C, D = (0.0, 0.0), (2.0, 0.0), (2.0, 2.0), (0.0, 2.0)
    v.append(Vec("pin_1039_diag_ABC_D", A, B, C, D, "ZERO", "cocircular_square_tie_1039"))
    v.append(Vec("pin_1039_diag_ABD_C", A, B, D, C, "ZERO", "cocircular_square_tie_1039 mirror"))
    v.append(Vec("pin_1039_knife_in", A, B, C, (0.0, 1.5), "POS", "knife +3"))
    v.append(Vec("pin_1039_knife_out", A, B, C, (0.0, 2.5), "NEG", "knife -5"))
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
            "DelaunayEdgeEmptyCircle outside disk",
        )
    )
    return v


def jts311_unit_test_vectors() -> List[Vec]:
    """Quads from TrianglePredicateTest added in the 2026-05 refresh of #311."""
    a, b, c = (0.0, 0.0), (10.0, 0.0), (0.0, 10.0)
    v = [
        Vec(
            "jts311_clear_inside",
            a,
            b,
            c,
            (1.0, 1.0),
            "POS",
            "TrianglePredicateTest.testAdaptiveInCircleClearCases inside",
        ),
        Vec(
            "jts311_clear_outside",
            a,
            b,
            c,
            (20.0, 20.0),
            "NEG",
            "TrianglePredicateTest.testAdaptiveInCircleClearCases outside",
        ),
        Vec(
            "jts311_large_coord_fallback",
            (100000000000000.19, 100000000000000.53),
            (100000000000000.19, 100000000000000.47),
            (100000000000000.22, 100000000000000.38),
            (100000000000000.40, 100000000000000.75),
            # PR asserts isInCircleDDFast / robust true, but binary64 Stage A and
            # b64_inCircle both classify ZERO after literal collapse at 1e14 —
            # keep open (characterization), not EXPECTED POS.
            None,
            "TrianglePredicateTest large-magnitude fallback; PR expects true, "
            "corpus oracle ZERO after b64 rounding (see jts-311 lane doc §5)",
        ),
    ]
    return v


def jts1212_sample_vectors() -> List[Vec]:
    """Subset of the #1212 adversarial bank (same float literals)."""
    v: List[Vec] = []
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
        aa, bb, cc, pp = circle[i], circle[i + 1], circle[i + 2], circle[i + 3]
        v.append(
            Vec(
                f"jts1212_circle_quad_{i}",
                aa,
                bb,
                cc,
                pp,
                None,
                "DelaunayTest.testCircle near-cocircular sample (also #311 retarget)",
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
            "jts1212_geos955_subset",
            geos955_sub[0],
            geos955_sub[1],
            geos955_sub[2],
            geos955_sub[3],
            None,
            "GEOS955 / JTS#1171 — Stage A must decline; DD or adapt required",
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
            "jts1212_geos1040_quad",
            geos1040[0],
            geos1040[1],
            geos1040[2],
            geos1040[3],
            None,
            "GEOS#1040 / JTS#1171 near-cocircular",
        )
    )
    return v


def all_vectors() -> List[Vec]:
    return corpus_vectors() + jts311_unit_test_vectors() + jts1212_sample_vectors()


# ---------------------------------------------------------------------------
# Oracle driver (same wire format as other scouts)
# ---------------------------------------------------------------------------


def resolve_oracle_cmd(args: argparse.Namespace) -> List[str]:
    """Same resolution policy as gen_jts1212_incircle_vectors.py."""
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


def run_oracle(
    oracle_cmd: Sequence[str], a: Point, b: Point, c: Point, p: Point
) -> Tuple[str, float]:
    """Call INCIRCLE_SIGN via stdin (same wire format as #1212 generator)."""
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
    tok = parts[1]
    val = (
        float.fromhex(tok)
        if tok.lower().startswith(("0x", "-0x", "+0x"))
        else float(tok)
    )
    return sign, val


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--oracle", default=None, help="Path to oracle_bin")
    ap.add_argument("--wsl-oracle", default=None, help="WSL path to oracle_bin")
    ap.add_argument(
        "--out",
        default=os.path.join(os.path.dirname(__file__), "jts311_incircle_history.txt"),
        help="Output table path",
    )
    args = ap.parse_args()

    vectors = all_vectors()
    oracle_cmd = resolve_oracle_cmd(args)

    # Sanity pin (same as other mesh scouts)
    try:
        pin_s, pin_val = run_oracle(
            oracle_cmd, (0.0, 0.0), (2.0, 0.0), (1.0, 1.0), (1.0, -0.5)
        )
    except Exception as e:
        print(f"FATAL: oracle unavailable ({oracle_cmd}): {e}", file=sys.stderr)
        return 2
    if pin_s != "POS" or abs(pin_val - 1.5) > 1e-12:
        print(
            f"FATAL: oracle pin failed: {pin_s} {pin_val} (expected POS 1.5)",
            file=sys.stderr,
        )
        return 2
    print(f"Oracle pin OK: {pin_s} {pin_val}  via {oracle_cmd}")

    lines: List[str] = []
    lines.append("# JTS #311 isInCircleAdapt — Stage A design-history gate")
    lines.append("# topic: mesh  epic: #68")
    lines.append(f"# PR311_EPS = ulp(1.0) = {PR311_EPS!r}  (2^-52)")
    lines.append(f"# SHEWCHUK_EPS = {SHEWCHUK_EPS!r}  (2^-53)")
    lines.append(
        f"# ICCERRBOUND_A_311 / ICCERRBOUND_A_SHEW ≈ "
        f"{ICCERRBOUND_A_311 / ICCERRBOUND_A_SHEWCHUK:.6g}"
    )
    lines.append(
        "# Columns: NAME | ORACLE | A311_SIGN | A311_CERT | A53_CERT | DET | ERR311 | NOTE"
    )
    lines.append("#")

    n_expected_fail = 0
    n_certain_conflict = 0
    n_a311_uncertain = 0
    n_a53_uncertain = 0
    n_eps_diverge = 0
    n_pass = 0
    failures: List[str] = []
    divergences: List[str] = []

    for vec in vectors:
        a311_sign, det, a311_cert, err311 = stage_a_311(vec.a, vec.b, vec.c, vec.p)
        _, _, a53_cert, _ = stage_a_shewchuk(vec.a, vec.b, vec.c, vec.p)

        if not a311_cert:
            n_a311_uncertain += 1
        if not a53_cert:
            n_a53_uncertain += 1
        if a311_cert != a53_cert:
            n_eps_diverge += 1
            divergences.append(
                f"  {vec.name}: A311={'CERT' if a311_cert else 'UNC'} "
                f"A53={'CERT' if a53_cert else 'UNC'} det={det:.6g} err311={err311:.6g}"
            )

        try:
            oracle_s, oracle_val = run_oracle(
                oracle_cmd, vec.a, vec.b, vec.c, vec.p
            )
        except RuntimeError as e:
            failures.append(f"{vec.name}: oracle error {e}")
            oracle_s, oracle_val = "ERR", float("nan")

        if vec.expected is not None and oracle_s in ("POS", "NEG", "ZERO"):
            if oracle_s != vec.expected:
                if vec.expected == "ZERO" and abs(oracle_val) < 1e-9:
                    pass  # soft-zero
                else:
                    n_expected_fail += 1
                    failures.append(
                        f"{vec.name}: EXPECTED {vec.expected} oracle "
                        f"{oracle_s} ({oracle_val})"
                    )

        if a311_cert and oracle_s in ("POS", "NEG", "ZERO"):
            if {a311_sign, oracle_s} <= {"POS", "NEG"} and a311_sign != oracle_s:
                n_certain_conflict += 1
                failures.append(
                    f"{vec.name}: A311 CERTAIN {a311_sign} vs oracle {oracle_s}"
                )
            else:
                n_pass += 1
        elif not a311_cert:
            n_pass += 1  # UNCERTAIN is OK for Stage A

        lines.append(
            f"{vec.name}\t"
            f"ORACLE={oracle_s}\t"
            f"A311={a311_sign}/{'CERT' if a311_cert else 'UNC'}\t"
            f"A53={'CERT' if a53_cert else 'UNC'}\t"
            f"det={det:.17g}\t"
            f"err311={err311:.17g}\t"
            f"# {vec.note}"
        )
        lines.append(
            f"  A=({fmt_pt(vec.a)}) B=({fmt_pt(vec.b)}) "
            f"C=({fmt_pt(vec.c)}) P=({fmt_pt(vec.p)})"
        )

    out_path = args.out
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print(f"Vectors: {len(vectors)}")
    print(f"oracle: {oracle_cmd}")
    print(f"PR311_EPS / SHEWCHUK_EPS = {PR311_EPS / SHEWCHUK_EPS:.0f}x")
    print(
        f"ICCERRBOUND_A_311 / ICCERRBOUND_A_SHEW ≈ "
        f"{ICCERRBOUND_A_311 / ICCERRBOUND_A_SHEWCHUK:.6g}"
    )
    print(f"EXPECTED pin failures: {n_expected_fail}")
    print(f"Stage A#311 CERTAIN vs oracle conflicts: {n_certain_conflict}")
    print(f"Stage A#311 UNCERTAIN: {n_a311_uncertain}")
    print(f"Stage A Shewchuk-ε UNCERTAIN: {n_a53_uncertain}")
    print(f"ε-policy CERT diverge (311 vs 2^-53): {n_eps_diverge}")
    print(f"CERTAIN/uncertain handled: {n_pass}")
    print(f"Wrote: {out_path}")
    if divergences:
        print("ε divergences:")
        for d in divergences:
            print(d)
    if failures:
        print("FAILURES:")
        for x in failures:
            print(" ", x)
        return 1
    print("GATE: GREEN")
    return 0


if __name__ == "__main__":
    sys.exit(main())
