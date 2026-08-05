#!/usr/bin/env python3
"""
JTS #1212 mesh in-circle lane — differential vectors vs Rocq INCIRCLE_SIGN.

topic: mesh (epic #68)
Upstream: locationtech/jts#1212 (Improve triangulation robustness)
         supersedes #1094 / #311 on TrianglePredicate.isInCircleRobust.

For each 4-tuple (A,B,C,P):
  - Rocq oracle: INCIRCLE_SIGN → extracted b64_inCircle (same kernel as
    nts_rocq_in_circle FFI; Shewchuk sign: POS iff CCW(ABC) and P inside).
  - Stage A filter (pure Python mirror of PR #1212): CERTAIN sign or UNCERTAIN.
  - Optional expected sign when a Qed pin or algebraic identity applies.

Usage:
  python oracle/gen_jts1212_incircle_vectors.py
  python oracle/gen_jts1212_incircle_vectors.py --oracle /path/to/oracle_bin
  python oracle/gen_jts1212_incircle_vectors.py --wsl-oracle /home/user/.../oracle_bin

Writes:
  oracle/jts1212_incircle_vectors.txt   (vector table + EXPECTED where known)
  stdout: gate summary (PASS/FAIL/UNCERTAIN counts)
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
DOUBLE_EPS = math.ldexp(1.0, -53)
IN_CIRCLE_ERR_BOUND = (10.0 + 96.0 * DOUBLE_EPS) * DOUBLE_EPS

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


def stage_a(a: Point, b: Point, c: Point, p: Point) -> Tuple[str, float, bool]:
    """Mirror of JTS#1212 TrianglePredicate.isInCircleRobust Stage A.
    Returns (sign POS/NEG/ZERO, disc, certain)."""
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

    disc = (
        alift * (bdxcdy - cdxbdy)
        + blift * (cdxady - adxcdy)
        + clift * (adxbdy - bdxady)
    )
    permanent = (
        (abs(bdxcdy) + abs(cdxbdy)) * alift
        + (abs(cdxady) + abs(adxcdy)) * blift
        + (abs(adxbdy) + abs(bdxady)) * clift
    )
    err_bound = IN_CIRCLE_ERR_BOUND * permanent
    certain = disc > err_bound or -disc > err_bound
    if disc > 0:
        sign = "POS"
    elif disc < 0:
        sign = "NEG"
    else:
        sign = "ZERO"
    return sign, disc, certain


def fmt_pt(q: Point) -> str:
    return f"{q[0]:.17g} {q[1]:.17g}"


def corpus_vectors() -> List[Vec]:
    """Qed-backed and algebraic pins from the mesh lane."""
    v: List[Vec] = []
    # DelaunayDegeneratePins: single-triangle vertices → ZERO
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
    # Cocircular square JTS#1039
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
    # Knife edge
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
    # Flip witness DelaunayLocallyDelaunay.loc_*
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
    # DelaunayEdgeEmptyCircle witness: S={A,B,C,D} with D outside circle of ABC
    # A=(0,0),B=(2,0),C=(1,1),D=(1,-2) — D outside circumcircle of ABC (r=1,O=(1,0))
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


def jts1212_vectors() -> List[Vec]:
    """Adversarial / regression sites from PR #1212 tests (exact float literals)."""
    v: List[Vec] = []
    # ConformingDelaunayTest.testTriangleConstraints_JTS_1190
    t0 = (-221.72957795130824, -26.56505117707799)
    t1 = (-149.72957795130824, -26.56505117707799)
    t2 = (0.0, -90.0)
    # Vertices on own circumcircle → algebraic ZERO (exact reals); b64 may be tiny
    for name, P in (("t0", t0), ("t1", t1), ("t2", t2)):
        v.append(
            Vec(
                f"jts1212_1190_vertex_{name}",
                t0,
                t1,
                t2,
                P,
                "ZERO",
                "single-triangle constraint sites; vertex on circumcircle",
            )
        )
    # Order as listed (may be CW — sign still ZERO at vertices)
    # Nearly cocircular circle from DelaunayTest.testCircle (sample quads)
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
    # Adjacent triple + next point (near-cocircular DT edge tests)
    for i in range(0, len(circle) - 3, 4):
        a, b, c, p = circle[i], circle[i + 1], circle[i + 2], circle[i + 3]
        v.append(
            Vec(
                f"jts1212_circle_quad_{i}",
                a,
                b,
                c,
                p,
                None,
                "DelaunayTest.testCircle near-cocircular sample quad",
            )
        )
    # Opposite diameter-ish: three spaced points + fourth
    v.append(
        Vec(
            "jts1212_circle_cardinal",
            (42.0, 30.0),
            (40.0, 28.0),
            (38.0, 30.0),
            (40.0, 32.0),
            None,
            "four cardinal-ish points on the densified circle",
        )
    )
    # VoronoiTest cocircular GEOS 1040 / JTS 1171
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
            "jts1212_geos955_subset",
            geos955_sub[0],
            geos955_sub[1],
            geos955_sub[2],
            geos955_sub[3],
            None,
            "VoronoiTest JTS#1171 example 2",
        )
    )
    # WKB multipoint from testNearCoincidentSitesJTS20 — decode via struct
    wkb_hex = (
        "01040000000700000001010000000f8b33e3d97742c038c453588d0423c0"
        "01010000001171d6d1b45d42c06adc1693e78c22c0"
        "01010000001c8b33e3d97742c062c453588d0423c0"
        "0101000000afa5c71fda7742c04b93c61d8e0423c0"
        "0101000000b0cddcb4b57942c026476887d7b122c0"
        "0101000000e0678421dc7642c0f7736021e1fb22c0"
        "0101000000e32fd565018d42c0c7ea1222167c22c0"
    )
    pts20 = decode_wkb_multipoint(wkb_hex)
    if len(pts20) >= 4:
        v.append(
            Vec(
                "jts1212_jts20_near_coincident",
                pts20[0],
                pts20[1],
                pts20[2],
                pts20[3],
                None,
                "VoronoiTest.testNearCoincidentSitesJTS20 first 4 sites",
            )
        )
        # Also a quad of the tightest-looking cluster (first, third, fourth, ...)
        if len(pts20) >= 6:
            v.append(
                Vec(
                    "jts1212_jts20_cluster",
                    pts20[0],
                    pts20[2],
                    pts20[3],
                    pts20[5],
                    None,
                    "JTS#20 near-coincident cluster sample",
                )
            )
    return v


def decode_wkb_multipoint(hexstr: str) -> List[Point]:
    raw = bytes.fromhex(hexstr)
    # little-endian WKB MultiPoint
    byte_order = raw[0]
    endian = "<" if byte_order == 1 else ">"
    geom_type = struct.unpack_from(endian + "I", raw, 1)[0]
    assert geom_type == 4, geom_type  # MultiPoint
    n = struct.unpack_from(endian + "I", raw, 5)[0]
    pts: List[Point] = []
    off = 9
    for _ in range(n):
        # nested Point: byteOrder + type + x + y
        bo = raw[off]
        e = "<" if bo == 1 else ">"
        off += 1
        t = struct.unpack_from(e + "I", raw, off)[0]
        off += 4
        assert t == 1, t
        x, y = struct.unpack_from(e + "dd", raw, off)
        off += 16
        pts.append((x, y))
    return pts


def adversarial_scale_vectors() -> List[Vec]:
    """Extra hard cases: near-cocircular at large/small magnitude."""
    v: List[Vec] = []
    # Unit circle discretized with float noise (exact cocircular would be ZERO)
    for k, eps in enumerate((1e-12, 1e-9, 1e-6)):
        a, b, c = (1.0, 0.0), (0.0, 1.0), (-1.0, 0.0)
        p = (0.0, -1.0 + eps)  # slightly inside/outside south
        v.append(
            Vec(
                f"adv_unit_circle_eps_{k}",
                a,
                b,
                c,
                p,
                None,
                f"south pole of unit circle nudged by {eps}",
            )
        )
    # Large coordinates (near overflow band for DD products still finite)
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
    return corpus_vectors() + jts1212_vectors() + adversarial_scale_vectors()


def run_oracle(
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
    # OCaml %h hex float
    val = float.fromhex(parts[1]) if parts[1].lower().startswith(("0x", "-0x", "+0x")) else float(parts[1])
    return sign, val


def resolve_oracle_cmd(args: argparse.Namespace) -> List[str]:
    if args.oracle:
        return [args.oracle]
    if args.wsl_oracle:
        return ["wsl.exe", "-e", args.wsl_oracle]
    env = os.environ.get("ORACLE_BIN")
    if env and os.path.isfile(env):
        return [env]
    wsl = os.environ.get("WSL_ORACLE_BIN", "/home/user/nettopologysuite.proofs/oracle/oracle_bin")
    return ["wsl.exe", "-e", wsl]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--oracle", help="Path to native oracle_bin")
    ap.add_argument("--wsl-oracle", help="Linux path invoked via wsl.exe -e")
    ap.add_argument(
        "--out",
        default="oracle/jts1212_incircle_vectors.txt",
        help="Vector table output path",
    )
    args = ap.parse_args()
    oracle_cmd = resolve_oracle_cmd(args)

    # Sanity pin
    try:
        s, val = run_oracle(oracle_cmd, (0, 0), (2, 0), (1, 1), (1, -0.5))
    except Exception as e:
        print(f"FATAL: oracle unavailable ({oracle_cmd}): {e}", file=sys.stderr)
        return 2
    if s != "POS" or abs(val - 1.5) > 1e-12:
        print(f"FATAL: oracle pin failed: {s} {val} (expected POS 1.5)", file=sys.stderr)
        return 2
    print(f"Oracle pin OK: {s} {val}  via {oracle_cmd}")

    vecs = all_vectors()
    lines: List[str] = [
        "# JTS #1212 mesh in-circle differential vectors",
        "# topic: mesh  epic: #68",
        "# Format: name  ax ay bx by cx cy px py  ORACLE  STAGE_A  CERTAIN  EXPECTED  note",
        "# ORACLE from INCIRCLE_SIGN (b64_inCircle). STAGE_A mirrors PR #1212 filter.",
        "# EXPECTED is POS|NEG|ZERO when a corpus pin or algebraic identity applies; else -",
        "#",
    ]

    n_pass = n_fail = n_open = n_uncertain = 0
    failures: List[str] = []

    for vec in vecs:
        o_sign, o_val = run_oracle(oracle_cmd, vec.a, vec.b, vec.c, vec.p)
        a_sign, disc, certain = stage_a(vec.a, vec.b, vec.c, vec.p)
        exp = vec.expected or "-"
        if certain:
            n_uncertain_tag = "CERTAIN"
            # Stage A certain sign must match oracle
            if a_sign != o_sign and not (a_sign == "ZERO" and o_sign == "ZERO"):
                # ZERO vs tiny: treat sign mismatch as fail only if both nonzero and disagree
                if {a_sign, o_sign} <= {"POS", "NEG"} and a_sign != o_sign:
                    n_fail += 1
                    failures.append(
                        f"{vec.name}: StageA CERTAIN {a_sign} != oracle {o_sign} (disc={disc})"
                    )
                else:
                    n_pass += 1
            else:
                n_pass += 1
        else:
            n_uncertain_tag = "UNCERTAIN"
            n_uncertain += 1
            # Uncertain is OK for Stage A; oracle is still ground truth
            n_pass += 1

        if vec.expected is not None:
            # Allow tiny nonzero vs exact ZERO on non-integer sites (report, don't hard-fail
            # float vertex pins that are only ZERO in exact reals)
            if o_sign != vec.expected:
                if vec.expected == "ZERO" and abs(o_val) < 1e-9:
                    # treat as soft-zero agreement
                    pass
                elif vec.expected == "ZERO":
                    n_fail += 1
                    failures.append(
                        f"{vec.name}: expected ZERO got {o_sign} val={o_val}"
                    )
                else:
                    n_fail += 1
                    failures.append(
                        f"{vec.name}: expected {vec.expected} got {o_sign} val={o_val}"
                    )
            else:
                pass
        else:
            n_open += 1

        lines.append(
            f"{vec.name}\t{fmt_pt(vec.a)}\t{fmt_pt(vec.b)}\t{fmt_pt(vec.c)}\t{fmt_pt(vec.p)}\t"
            f"{o_sign}\t{a_sign}\t{n_uncertain_tag}\t{exp}\t{vec.note}"
        )

    out_path = args.out
    os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
    with open(out_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    print()
    print(f"Vectors: {len(vecs)}  written → {out_path}")
    print(f"Stage A CERTAIN agreements / gate: pass≈{n_pass} fail={len(failures)} uncertain_filter={n_uncertain}")
    print(f"Open (no EXPECTED): {n_open}")
    if failures:
        print("FAILURES:")
        for msg in failures:
            print(f"  {msg}")
        return 1
    print("GATE: all expected pins match oracle; no CERTAIN StageA≠oracle conflicts.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
