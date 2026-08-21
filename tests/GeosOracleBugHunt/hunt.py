#!/usr/bin/env python3
"""GEOS vs Rocq oracle differential hunt — make curve ops rock-solid.

Uses geosop + oracle_bin (ARC_LENGTH, ARC_DISTANCE, POINT_IN_CURVE_RING, ARC_AREA).

Assisted-by: xAI Grok
"""
from __future__ import annotations

import math
import os
import re
import subprocess
import sys
from dataclasses import dataclass

GEOSOP = os.environ.get("GEOSOP", "/home/user/geos-build/bin/geosop")
ORACLE = os.environ.get(
    "ORACLE",
    "/mnt/c/com/github/grootstebozewolf/NetTopologySuite.Proofs/"
    ".ci-artifacts/oracle-bin-linux/oracle_bin",
)

ok = warn = bug = fail = 0


def hit(sev: str, tag: str, detail: str) -> None:
    global ok, warn, bug, fail
    if sev == "OK":
        ok += 1
    elif sev == "WARN":
        warn += 1
    elif sev == "BUG":
        bug += 1
    else:
        fail += 1
    print(f"{sev}\t{tag}\t{detail}")


def geosop(*args: str) -> str:
    r = subprocess.run(
        [GEOSOP, *args],
        capture_output=True,
        text=True,
        timeout=30,
    )
    out = (r.stdout or "").strip()
    err = (r.stderr or "").strip()
    if r.returncode != 0 and not out:
        raise RuntimeError(f"geosop rc={r.returncode}: {err or out}")
    return out


def oracle(stdin: str) -> str:
    r = subprocess.run(
        [ORACLE],
        input=stdin,
        capture_output=True,
        text=True,
        timeout=20,
    )
    out = (r.stdout or "").strip()
    if r.returncode != 0 and not out:
        raise RuntimeError(f"oracle rc={r.returncode}: {r.stderr}")
    return out


def parse_hex_float(s: str) -> float:
    s = s.strip()
    if s in ("DEGENERATE", "NAN"):
        return float("nan")
    if s.startswith("-"):
        return -parse_hex_float(s[1:])
    if not s.lower().startswith("0x"):
        return float(s)
    body = s[2:]
    p = body.lower().find("p")
    if p < 0:
        return float(int(body, 16))
    mant, exp_s = body[:p], body[p + 1 :]
    exp = int(exp_s)
    if "." in mant:
        whole, frac = mant.split(".", 1)
        m = int(whole, 16) if whole else 0
        f = 0.0
        for ch in frac:
            f = f * 16 + int(ch, 16)
        m += f / (16 ** len(frac))
    else:
        m = int(mant, 16)
    return m * (2.0 ** exp)


def near(a: float, b: float, rel: float = 1e-9, abs_tol: float = 1e-9) -> bool:
    if math.isnan(a) or math.isnan(b):
        return False
    d = abs(a - b)
    return d <= abs_tol or d <= rel * max(abs(a), abs(b), 1e-30)


@dataclass(frozen=True)
class Arc:
    name: str
    ax: float
    ay: float
    bx: float
    by: float
    cx: float
    cy: float

    def wkt(self) -> str:
        return (
            f"CIRCULARSTRING ({self.ax} {self.ay}, "
            f"{self.bx} {self.by}, {self.cx} {self.cy})"
        )

    def oracle_pts(self) -> str:
        return f"{self.ax} {self.ay}\n{self.bx} {self.by}\n{self.cx} {self.cy}"


ARCS = [
    Arc("unit_quarter", 1, 0, 0.7071067811865476, 0.7071067811865476, 0, 1),
    Arc("unit_semicircle", 1, 0, 0, 1, -1, 0),
    Arc("unit_lower_semi", 1, 0, 0, -1, -1, 0),
    Arc("R5_semi", 5, 0, 0, 5, -5, 0),
    Arc("flat_almost_chord", 0, 0, 5, 0.01, 10, 0),
    Arc("off_centre", 3, 4, 5, 4, 4, 5),
    Arc("tiny_arc", 0, 0, 1e-3, 1e-6, 2e-3, 0),
]

DIST_Q = [
    ("semi_center", "unit_semicircle", 0, 0),
    ("semi_outside", "unit_semicircle", 0, 2),
    ("semi_endpoint", "unit_semicircle", 1, 0),
    ("semi_off_sweep", "unit_semicircle", 0, -2),
    ("quarter_origin", "unit_quarter", 0, 0),
    ("quarter_inside", "unit_quarter", 0.5, 0.5),
    ("semi_far", "unit_semicircle", 10, 10),
    ("lower_center", "unit_lower_semi", 0, 0),
    ("R5_center", "R5_semi", 0, 0),
    ("off_mid", "off_centre", 4, 4),
]


def arc_by_name(n: str) -> Arc:
    for a in ARCS:
        if a.name == n:
            return a
    raise KeyError(n)


def hunt_length() -> None:
    print("=== ARC_LENGTH vs GEOS CircularString.Length ===")
    for a in ARCS:
        try:
            o = oracle(f"ARC_LENGTH\n{a.oracle_pts()}\n")
            g = float(geosop("-a", a.wkt(), "length"))
        except Exception as e:
            hit("FAIL", f"LEN/{a.name}", str(e))
            continue
        if o in ("DEGENERATE", "NAN"):
            hit("WARN", f"LEN/{a.name}", f"oracle={o} geos={g:g}")
            continue
        ol = parse_hex_float(o)
        if near(g, ol):
            hit("OK", f"LEN/{a.name}", f"geos={g:.17g} oracle={ol:.17g}")
        else:
            hit(
                "BUG",
                f"LEN/{a.name}",
                f"geos={g:.17g} oracle={ol:.17g} abs={abs(g - ol):.17g}",
            )


def hunt_distance() -> None:
    print("=== ARC_DISTANCE vs GEOS Point×CircularString distance ===")
    for name, an, px, py in DIST_Q:
        a = arc_by_name(an)
        try:
            o = oracle(f"ARC_DISTANCE\n{a.oracle_pts()}\n{px} {py}\n")
            g = float(
                geosop("-a", f"POINT ({px} {py})", "-b", a.wkt(), "distance")
            )
        except Exception as e:
            hit("FAIL", f"DIST/{name}", str(e))
            continue
        if o in ("DEGENERATE", "NAN"):
            hit("WARN", f"DIST/{name}", f"oracle={o} geos={g:g}")
            continue
        od = parse_hex_float(o)
        if near(g, od, rel=1e-8, abs_tol=1e-8):
            hit("OK", f"DIST/{name}", f"geos={g:.17g} oracle={od:.17g}")
        else:
            hit(
                "BUG",
                f"DIST/{name}",
                f"geos={g:.17g} oracle={od:.17g} abs={abs(g - od):.17g}",
            )


def hunt_envelope() -> None:
    print("=== ENVELOPE analytical arc extrema ===")
    a = math.radians(-30)
    b = math.radians(10)
    c = math.radians(50)
    wkt = (
        f"CIRCULARSTRING ({math.cos(a)} {math.sin(a)}, "
        f"{math.cos(b)} {math.sin(b)}, {math.cos(c)} {math.sin(c)})"
    )
    try:
        env = geosop("-a", wkt, "envelope")
        nums = [
            float(x)
            for x in re.findall(r"[-+]?\d*\.?\d+(?:[eE][-+]?\d+)?", env)
        ]
        xs = nums[0::2]
        maxx = max(xs)
    except Exception as e:
        hit("FAIL", "ENV/axis_extreme", str(e))
        return
    if maxx + 1e-12 >= 1.0:
        hit("OK", "ENV/axis_extreme", f"MaxX={maxx:.17g} (true=1)")
    else:
        hit("BUG", "ENV/axis_extreme", f"MaxX={maxx:.17g} < 1")


def hunt_area() -> None:
    print("=== ARC_AREA / unit disk area ===")
    a = Arc("semi", 1, 0, 0, 1, -1, 0)
    try:
        o = oracle(f"ARC_AREA\n{a.oracle_pts()}\n")
        cp = (
            "CURVEPOLYGON (COMPOUNDCURVE ("
            "CIRCULARSTRING (1 0, 0 1, -1 0), (-1 0, 1 0)))"
        )
        g = float(geosop("-a", cp, "area"))
        g2 = float(
            geosop(
                "-a",
                "CURVEPOLYGON (CIRCULARSTRING (1 0, 0 1, -1 0, 0 -1, 1 0))",
                "area",
            )
        )
    except Exception as e:
        hit("FAIL", "AREA", str(e))
        return
    if o not in ("DEGENERATE", "NAN"):
        oa = parse_hex_float(o)
        if near(g, oa, rel=1e-8) or near(g, math.pi / 2, rel=1e-8):
            hit(
                "OK",
                "AREA/halfdisk_cp",
                f"geos={g:.17g} oracle_seg={oa:.17g}",
            )
        else:
            hit(
                "BUG",
                "AREA/halfdisk_cp",
                f"geos={g:.17g} oracle_seg={oa:.17g} pi/2={math.pi / 2:.17g}",
            )
    if near(g2, math.pi, rel=1e-8):
        hit("OK", "AREA/unit_disk", f"geos={g2:.17g} pi={math.pi:.17g}")
    else:
        hit("BUG", "AREA/unit_disk", f"geos={g2:.17g} pi={math.pi:.17g}")


def hunt_pip() -> None:
    print("=== POINT_IN_CURVE_RING vs GEOS contains/intersects ===")
    ring_segs = "2\nA 1 0 0 1 -1 0\nC -1 0 1 0\n"
    cp = (
        "CURVEPOLYGON (COMPOUNDCURVE ("
        "CIRCULARSTRING (1 0, 0 1, -1 0), (-1 0, 1 0)))"
    )
    queries = [
        ("center", 0.0, 0.5),
        ("bulge", 0.0, 0.9),
        ("below_chord", 0.0, -0.1),
        ("far", 2.0, 2.0),
        ("near_arc_inside", 0.0, 0.2),
    ]
    for name, px, py in queries:
        try:
            o = oracle(f"POINT_IN_CURVE_RING\n{ring_segs}{px} {py}\n")
            cont = (
                geosop("-a", cp, "-b", f"POINT ({px} {py})", "contains").lower()
                == "true"
            )
            inter = (
                geosop(
                    "-a", cp, "-b", f"POINT ({px} {py})", "intersects"
                ).lower()
                == "true"
            )
        except Exception as e:
            hit("FAIL", f"PIP/{name}", str(e))
            continue
        if o not in ("IN", "OUT", "NAN"):
            hit("FAIL", f"PIP/{name}", f"oracle={o}")
            continue
        o_in = o == "IN"
        if o_in and cont and inter:
            hit("OK", f"PIP/{name}", f"oracle=IN contains=T intersects=T")
        elif o_in and inter and not cont:
            hit(
                "WARN",
                f"PIP/{name}",
                "oracle=IN contains=F intersects=T (boundary-ish)",
            )
        elif o_in and not inter:
            hit(
                "BUG",
                f"PIP/{name}",
                f"oracle=IN contains={cont} intersects={inter}",
            )
        elif not o_in and not cont and not inter:
            hit("OK", f"PIP/{name}", "oracle=OUT contains=F intersects=F")
        elif not o_in and not cont and inter:
            hit(
                "WARN",
                f"PIP/{name}",
                "oracle=OUT contains=F intersects=T (boundary convention)",
            )
        else:
            hit(
                "BUG",
                f"PIP/{name}",
                f"oracle={o} contains={cont} intersects={inter}",
            )


def hunt_pip_grid() -> None:
    print("=== POINT_IN_CURVE_RING grid (half-disk) ===")
    ring_segs = "2\nA 1 0 0 1 -1 0\nC -1 0 1 0\n"
    cp = (
        "CURVEPOLYGON (COMPOUNDCURVE ("
        "CIRCULARSTRING (1 0, 0 1, -1 0), (-1 0, 1 0)))"
    )
    hard = 0
    soft = 0
    checked = 0
    samples: list[str] = []
    for i in range(-5, 6):
        for j in range(-2, 8):
            px = i * 0.25
            py = j * 0.25
            try:
                o = oracle(f"POINT_IN_CURVE_RING\n{ring_segs}{px} {py}\n")
                if o == "NAN":
                    continue
                cont = (
                    geosop(
                        "-a", cp, "-b", f"POINT ({px} {py})", "contains"
                    ).lower()
                    == "true"
                )
                inter = (
                    geosop(
                        "-a", cp, "-b", f"POINT ({px} {py})", "intersects"
                    ).lower()
                    == "true"
                )
            except Exception as e:
                hit("FAIL", f"PIP_GRID/{px},{py}", str(e))
                return
            checked += 1
            if o == "IN":
                if not inter:
                    hard += 1
                    samples.append(f"IN !intersects @({px},{py})")
                elif not cont:
                    soft += 1
                    samples.append(f"IN !contains @({px},{py})")
            else:
                if cont:
                    hard += 1
                    samples.append(f"OUT contains @({px},{py})")
                elif inter:
                    soft += 1
                    samples.append(f"OUT intersects @({px},{py})")
    if hard == 0:
        hit(
            "OK",
            "PIP_GRID/halfdisk",
            f"checked={checked} hard={hard} soft_boundary={soft}",
        )
        for s in samples[:6]:
            hit("WARN", "PIP_GRID/boundary", s)
    else:
        hit("BUG", "PIP_GRID/halfdisk", f"checked={checked} hard={hard}")
        for s in samples[:12]:
            hit("BUG", "PIP_GRID/sample", s)


def hunt_covers_968() -> None:
    print("=== #968 covers Line/Point float robustness ===")
    cases = [
        ("orig", "LINESTRING (1 0, 0 2)", "POINT (0.9 0.2)", True),
        ("x10", "LINESTRING (10 0, 0 20)", "POINT (9 2)", True),
        ("off", "LINESTRING (1 0, 0 2)", "POINT (0.5 0.5)", False),
    ]
    for name, line, pt, expect in cases:
        try:
            cov = geosop("-a", line, "-b", pt, "covers").lower() == "true"
        except Exception as e:
            try:
                cov = geosop("-a", pt, "-b", line, "within").lower() == "true"
            except Exception as e2:
                hit("FAIL", f"COVERS968/{name}", f"{e}; {e2}")
                continue
        if cov == expect:
            hit("OK", f"COVERS968/{name}", f"covers={cov} expected={expect}")
        else:
            hit("BUG", f"COVERS968/{name}", f"covers={cov} expected={expect}")


def hunt_split_1497() -> None:
    print("=== #1497 CurvePolygon split (post-#1500) ===")
    a = (
        "CURVEPOLYGON (COMPOUNDCURVE((5 0, 0 0, 0 5, 5 5), "
        "CIRCULARSTRING(5 5, 7 1, 5 0)))"
    )
    b = (
        "CURVEPOLYGON (COMPOUNDCURVE((5 0, 0 0, 5 5), "
        "CIRCULARSTRING(5 5, 7 4, 5 0)))"
    )
    try:
        out = geosop("-a", a, "-b", b, "split")
    except Exception as e:
        hit("FAIL", "SPLIT1497", str(e))
        return
    if "CIRCULARSTRING" in out and "CURVEPOLYGON" in out:
        hit("OK", "SPLIT1497/curved_preserved", out[:100].replace("\n", " "))
    else:
        hit("BUG", "SPLIT1497/curved_dropped", out[:200].replace("\n", " "))


def hunt_multipoint_ms() -> None:
    print("=== MultiSurface × MultiPoint A/P (PR #1502) ===")
    ms = (
        "MULTISURFACE (CURVEPOLYGON ("
        "CIRCULARSTRING (0 0, 1 1, 2 0, 1 -1, 0 0)))"
    )
    cases = [
        ("int", "MULTIPOINT ((1 0))", True, True),
        ("ext", "MULTIPOINT ((3 3))", False, False),
        ("mixed", "MULTIPOINT ((1 0),(3 3))", False, True),
        ("empty", "MULTIPOINT EMPTY", False, False),
        ("boundary", "MULTIPOINT ((0 0))", False, True),
    ]
    for name, mp, exp_c, exp_i in cases:
        try:
            c = geosop("-a", ms, "-b", mp, "contains").lower() == "true"
            i = geosop("-a", ms, "-b", mp, "intersects").lower() == "true"
            d = geosop("-a", ms, "-b", mp, "disjoint").lower() == "true"
        except Exception as e:
            hit("FAIL", f"MS/{name}", str(e))
            continue
        if c == exp_c and i == exp_i and d == (not exp_i):
            hit("OK", f"MS/{name}", f"contains={c} intersects={i} disjoint={d}")
        else:
            hit(
                "BUG",
                f"MS/{name}",
                f"contains={c}(exp {exp_c}) intersects={i}(exp {exp_i}) "
                f"disjoint={d}",
            )


def main() -> int:
    print(f"GEOSOP={GEOSOP}")
    print(f"ORACLE={ORACLE}")
    try:
        ver = geosop("--help").splitlines()[0]
    except Exception as e:
        print(f"FATAL: cannot run geosop: {e}", file=sys.stderr)
        return 2
    print(f"geos: {ver}")
    hunt_length()
    hunt_distance()
    hunt_envelope()
    hunt_area()
    hunt_pip()
    hunt_pip_grid()
    hunt_covers_968()
    hunt_split_1497()
    hunt_multipoint_ms()
    print()
    print(f"SUMMARY\tok={ok}\twarn={warn}\tbug={bug}\tfail={fail}")
    return 1 if (bug + fail) > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
