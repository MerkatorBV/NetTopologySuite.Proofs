#!/usr/bin/env python3
# coverage: feat:arc-len geom:ellipse,bezier,clothoid,nurbs
"""
RED tests for LENGTH_UNIFIED over the Zoo tokens (#508 M-LEN-ZOO, Bible §4.2
length() obligation; token grammars are ISO/IEC 13249-3:2016 §5.1.67
projections — see the LENGTH_UNIFIED header in driver.ml).

Extended protocol (C/A behaviour and output are unchanged):
  LENGTH_UNIFIED
  <nsegs>
  segs...   "C x1 y1 x2 y2"
          | "A x1 y1 x2 y2 x3 y3"
          | "E cx cy rx ry rot sa sw"           (ELLIPTICALCURVE projection)
          | "B x0 y0 x1 y1 x2 y2 x3 y3"         (Esri cubic Bézier; no ISO form)
          | "K x y dx dy A sd ed"               (CLOTHOID projection)
          | "N d x0 y0 w0 ... xd yd wd"         (NURBSCURVE, single-span clamped)
Output: "<len>" (%h) | "DEGENERATE" | "NAN", and — only when the input holds at
least one zoo segment (E/B/K/N) — a second line "DENSIFIED <len>" (%h): the
uniform chord-sum cross-check column decided in #508 (oracle answers stay
single-line for pre-zoo consumers).

Independent truth sources (never the driver's own quadrature route):
  - circular-bridge ellipse rx=ry: closed form r*|sweep|
  - non-circular ellipse quarter: Carlson RF/RD symmetric integrals
    (Carlson 1995 duplication algorithm), quarter = a*E(e^2)
  - collinear cubic Béziers: |P3-P0|
  - clothoid: ISO arc-length parameterization, length = ed - sd exactly
  - degree-1 NURBS: point distance; rational-quadratic quarter circle
    (w1 = cos 45°): pi/2
"""
import math
import os
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")


def run(stdin):
    p = subprocess.run([BIN], input=stdin, capture_output=True, text=True)
    return p.stdout.strip(), p.stderr.strip(), p.returncode


def fail(name, got, exp, sample):
    print(f"RED FAIL {name}")
    print("  got:", got)
    print("  exp:", exp)
    print("  stdin[:300]:", sample[:300])
    sys.exit(1)


def to_float(s):
    try:
        return float(s)
    except ValueError:
        return float.fromhex(s)


def parse_zoo_output(name, out, sample):
    """Zoo inputs answer two lines: '<len>' then 'DENSIFIED <len>'."""
    lines = [ln for ln in out.splitlines() if ln.strip()]
    if len(lines) != 2 or not lines[1].startswith("DENSIFIED "):
        fail(name, out, "<len> then 'DENSIFIED <len>'", sample)
    return to_float(lines[0]), to_float(lines[1].split()[1])


def check_crosscheck(name, primary, densified, sample):
    if abs(primary - densified) > 1e-6 * max(1.0, abs(primary)):
        fail(name + "_crosscheck", f"{primary} vs DENSIFIED {densified}",
             "agreement within 1e-6 rel", sample)


# ---- Carlson symmetric elliptic integrals (independent truth source) -------
def carlson_rf(x, y, z):
    for _ in range(200):
        lam = math.sqrt(x) * math.sqrt(y) + math.sqrt(y) * math.sqrt(z) \
            + math.sqrt(z) * math.sqrt(x)
        x, y, z = (x + lam) / 4, (y + lam) / 4, (z + lam) / 4
        mu = (x + y + z) / 3
        if max(abs(x - mu), abs(y - mu), abs(z - mu)) < 1e-14 * mu:
            break
    mu = (x + y + z) / 3
    X, Y, Z = 1 - x / mu, 1 - y / mu, 1 - z / mu
    e2 = X * Y - Z * Z
    e3 = X * Y * Z
    return (1 - e2 / 10 + e3 / 14 + e2 * e2 / 24 - 3 * e2 * e3 / 44) \
        / math.sqrt(mu)


def carlson_rd(x, y, z):
    s = 0.0
    fac = 1.0
    for _ in range(200):
        lam = math.sqrt(x) * math.sqrt(y) + math.sqrt(y) * math.sqrt(z) \
            + math.sqrt(z) * math.sqrt(x)
        s += fac / (math.sqrt(z) * (z + lam))
        fac /= 4
        x, y, z = (x + lam) / 4, (y + lam) / 4, (z + lam) / 4
        mu = (x + y + 3 * z) / 5
        if max(abs(x - mu), abs(y - mu), abs(z - mu)) < 1e-14 * mu:
            break
    mu = (x + y + 3 * z) / 5
    X, Y, Z = 1 - x / mu, 1 - y / mu, 1 - z / mu
    ea = X * Y
    eb = Z * Z
    ec = ea - eb
    ed_ = ea - 6 * eb
    ee = ed_ + ec + ec
    poly = 1 + ed_ * (-3 / 14 + 9 / 88 * ed_ - 4.5 / 26 * Z * ee) \
        + Z * (ee / 6 + Z * (-9 / 22 * ec + 3 / 26 * Z * ea))
    return 3 * s + fac * poly / (mu * math.sqrt(mu))


def ellip_e_complete(m):
    """Complete elliptic integral of the 2nd kind, parameter m = e^2."""
    return carlson_rf(0, 1 - m, 1) - m / 3 * carlson_rd(0, 1 - m, 1)


# 1) rx = ry bridge: circular ellipse, sweep pi/2, r = 2 -> length pi
stdin = """LENGTH_UNIFIED
1
E 0 0 2 2 0 0 1.5707963267948966
"""
out, _, rc = run(stdin)
print("RED_NOTE ellipse_bridge_got=", out)
if rc != 0 or not out:
    fail("ellipse_bridge", out, "pi", stdin)
got, dens = parse_zoo_output("ellipse_bridge", out, stdin)
if abs(got - math.pi) > 1e-9:
    fail("ellipse_bridge", out, "pi", stdin)
check_crosscheck("ellipse_bridge", got, dens, stdin)
print("ellipse rx=ry bridge ok")

# 2) non-circular quarter ellipse a=2 b=1 (rotation must not change length):
#    expected 2*E(0.75) via Carlson
exp_quarter = 2 * ellip_e_complete(0.75)
stdin = """LENGTH_UNIFIED
1
E 0 0 2 1 0.5 0 1.5707963267948966
"""
out, _, rc = run(stdin)
print("RED_NOTE ellipse_quarter_got=", out, "exp=", exp_quarter)
if rc != 0 or not out:
    fail("ellipse_quarter", out, str(exp_quarter), stdin)
got, dens = parse_zoo_output("ellipse_quarter", out, stdin)
if abs(got - exp_quarter) > 1e-9:
    fail("ellipse_quarter", out, str(exp_quarter), stdin)
check_crosscheck("ellipse_quarter", got, dens, stdin)
print("ellipse quarter (Carlson) ok")

# 3) collinear cubic Béziers: straight line, uniform and non-uniform controls
for name, seg, exp in [
    ("bezier_collinear", "B 0 0 1 1 2 2 3 3", 3 * math.sqrt(2)),
    ("bezier_collinear_nonuniform", "B 0 0 0.1 0 0.2 0 3 0", 3.0),
]:
    stdin = f"LENGTH_UNIFIED\n1\n{seg}\n"
    out, _, rc = run(stdin)
    print(f"RED_NOTE {name}_got=", out)
    if rc != 0 or not out:
        fail(name, out, str(exp), stdin)
    got, dens = parse_zoo_output(name, out, stdin)
    if abs(got - exp) > 1e-9:
        fail(name, out, str(exp), stdin)
    check_crosscheck(name, got, dens, stdin)
    print(name, "ok")

# 4) curved cubic: sandwich chord <= len <= control polygon + cross-check
stdin = """LENGTH_UNIFIED
1
B 0 0 1 2 2 -1 3 1
"""
out, _, rc = run(stdin)
print("RED_NOTE bezier_curved_got=", out)
if rc != 0 or not out:
    fail("bezier_curved", out, "chord<len<polygon", stdin)
got, dens = parse_zoo_output("bezier_curved", out, stdin)
chord = math.hypot(3, 1)
poly = math.hypot(1, 2) + math.hypot(1, 3) + math.hypot(1, 2)
if not (chord < got < poly):
    fail("bezier_curved_sandwich", out, f"({chord}, {poly})", stdin)
check_crosscheck("bezier_curved", got, dens, stdin)
print("bezier curved sandwich ok")

# 5) clothoid: ISO arc-length parameterization -> length = ed - sd exactly;
#    DENSIFIED validates unit speed numerically
stdin = """LENGTH_UNIFIED
1
K 0 0 1 0 1 0.5 3.25
"""
out, _, rc = run(stdin)
print("RED_NOTE clothoid_got=", out)
if rc != 0 or not out:
    fail("clothoid", out, "2.75", stdin)
got, dens = parse_zoo_output("clothoid", out, stdin)
if abs(got - 2.75) > 1e-12:
    fail("clothoid", out, "2.75", stdin)
check_crosscheck("clothoid", got, dens, stdin)
print("clothoid exact-by-subtraction ok")

# 6) clothoid degenerate: ed < sd, and scalefactor 0
for name, seg in [
    ("clothoid_reversed", "K 0 0 1 0 1 3.25 0.5"),
    ("clothoid_zero_scale", "K 0 0 1 0 0 0.5 3.25"),
]:
    stdin = f"LENGTH_UNIFIED\n1\n{seg}\n"
    out, _, rc = run(stdin)
    print(f"RED_NOTE {name}_got=", out)
    if rc != 0 or out != "DEGENERATE":
        fail(name, out, "DEGENERATE", stdin)
    print(name, "ok")

# 7) NURBS degree 1 (line) and rational-quadratic quarter circle (w1 = cos 45°)
stdin = """LENGTH_UNIFIED
1
N 1 0 0 1 3 4 1
"""
out, _, rc = run(stdin)
print("RED_NOTE nurbs_line_got=", out)
if rc != 0 or not out:
    fail("nurbs_line", out, "5", stdin)
got, dens = parse_zoo_output("nurbs_line", out, stdin)
if abs(got - 5.0) > 1e-9:
    fail("nurbs_line", out, "5", stdin)
check_crosscheck("nurbs_line", got, dens, stdin)
print("nurbs line ok")

stdin = """LENGTH_UNIFIED
1
N 2 1 0 1 1 1 0.7071067811865476 0 1 1
"""
out, _, rc = run(stdin)
print("RED_NOTE nurbs_arc_got=", out)
if rc != 0 or not out:
    fail("nurbs_arc", out, "pi/2", stdin)
got, dens = parse_zoo_output("nurbs_arc", out, stdin)
if abs(got - math.pi / 2) > 1e-9:
    fail("nurbs_arc", out, "pi/2", stdin)
check_crosscheck("nurbs_arc", got, dens, stdin)
print("nurbs rational quarter circle ok")

# 8) mixed pre-zoo + zoo: chord 1 + circular-bridge ellipse pi + clothoid 2.75
stdin = """LENGTH_UNIFIED
3
C 0 0 1 0
E 0 0 2 2 0 0 1.5707963267948966
K 0 0 1 0 1 0.5 3.25
"""
out, _, rc = run(stdin)
print("RED_NOTE mixed_zoo_got=", out)
if rc != 0 or not out:
    fail("mixed_zoo", out, str(1 + math.pi + 2.75), stdin)
got, dens = parse_zoo_output("mixed_zoo", out, stdin)
if abs(got - (1 + math.pi + 2.75)) > 1e-9:
    fail("mixed_zoo", out, str(1 + math.pi + 2.75), stdin)
print("mixed pre-zoo + zoo ok")

# 9) C/A-only inputs still answer a single line (pre-zoo consumers unbroken)
stdin = """LENGTH_UNIFIED
1
C 0 0 3 4
"""
out, _, rc = run(stdin)
print("RED_NOTE ca_single_line_got=", out)
lines = [ln for ln in out.splitlines() if ln.strip()]
if rc != 0 or len(lines) != 1 or abs(to_float(lines[0]) - 5.0) > 1e-12:
    fail("ca_single_line", out, "single line 5.0", stdin)
print("C/A single-line back-compat ok")

# 10) NaN guard on zoo tokens
stdin = """LENGTH_UNIFIED
1
E nan 0 2 2 0 0 1
"""
out, _, rc = run(stdin)
print("RED_NOTE zoo_nan_got=", out)
if rc != 0 or out != "NAN":
    fail("zoo_nan", out, "NAN", stdin)
print("zoo NaN guard ok")

print("RED tests for #508 zoo LENGTH_UNIFIED: all assertions passed.")
