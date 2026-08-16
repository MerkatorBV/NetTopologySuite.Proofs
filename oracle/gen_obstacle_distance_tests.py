#!/usr/bin/env python3
# =============================================================================
# oracle/gen_obstacle_distance_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for OBSTACLE_DISTANCE (RocqRefRunner), the typed
# per-component obstacle clearance of the LEC laser -- proof companion
# theories/LECObstacleDistance.v (obstacle_distance_headline:
# empty_disk_disc_iff / empty_disk_ring_iff / empty_disk_union_iff /
# min_disc_dist_weighted / lec_two_discs / corner_clearance_zero /
# centre_clearance_one).
#
# PROVEN invariants the oracle MUST satisfy (a violation '!!' is a real bug
# and fails CI, mirroring oracle/gen_lec_circle_tests.py):
#   I1 PINS      the 3-4-5 witness cell (discs r=3 at (+-4,0)) is bit-exact:
#                clearance 2.0 at (0,+-3) [lec_two_discs, equidistant],
#                1.0 at the rect centre, 0.0 at all four rect corners
#                [corner_sampling_hypothesis_refuted's pins]
#   I2 WEIGHTED  DISC-only clearance == max(0, min_i (|P-c_i| - r_i)),
#                bit-exact vs the generator mirror (min_disc_dist_weighted:
#                the Apollonius reduction), clamp binding included
#   I3 SHELL     filled disc vs full-circle ring at the same (c, r):
#                interior -> DISC 0.0 while RING r-d > 0; on-circle
#                (3-4-5 rational point) -> both 0.0; exterior -> equal
#   I4 FLATTEN   permutation / duplication of the component list leaves the
#                output line identical; singleton == the row value
#                (empty_disk_union_iff)
#   I5 GRID      clearance <= 2.0 across the 0.5-grid of the witness
#                rectangle, == 2.0 exactly at (0,+-3) only, and every grid
#                value bit-matches the generator mirror (lec_two_discs +
#                lec_two_discs_maximisers)
#   I6 VERDICTS  k < 1 / r < 0 / unknown tag -> DEGENERATE; any non-finite
#                input -> NAN; NAN wins over DEGENERATE.  The k = 0 verdict
#                is FORCED, not a policy: Rmin has no unit in R
#                (LECFlattenRow.empty_fold_no_finite_unit, ledger F5)
#   I7 ARC       the ARC member row is the ARC_DISTANCE kernel: singleton
#                ARC is bit-identical to the ARC_DISTANCE mode on the same
#                query; mixed lists min-fold across all four typed rows
#                bit-exactly (LECArcRow.arc_dist_exact + LECFlattenRow.v
#                empty_disk_flatten_iff); collinear controls -> DEGENERATE
#   I8 SEG       the SEG member row is the clamped projection
#                (LECSegmentRow.seg_dist, proven the exact facet distance):
#                interior-foot and endpoint-clamp pins bit-exact; the
#                UNCLAMPED line foot understates beyond an endpoint
#                (ledger F6 -- the 3-4-5 witness pins 5, the foot says 4);
#                a zero-length facet collapses to the POINT row bit-exactly
#                (seg_dist_degenerate), NOT DEGENERATE
# =============================================================================

import math
import os
import subprocess
import sys
from fractions import Fraction as F

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")

failures = 0


def emit(s=""):
    print(s)


def run(query_line, comps):
    stdin = "OBSTACLE_DISTANCE\n" + query_line + "\n" + str(len(comps)) + "\n"
    stdin += "".join(c + "\n" for c in comps)
    out = subprocess.run([BIN], input=stdin, capture_output=True, text=True)
    if out.returncode != 0:
        return f"<exit {out.returncode}: {out.stderr.strip()}>"
    return out.stdout.strip()


def parse(line):
    # "DIST <d> N <k>" -> (d, k) or None
    tok = line.split()
    if len(tok) == 4 and tok[0] == "DIST" and tok[2] == "N":
        return (float.fromhex(tok[1]), int(tok[3]))
    return None


# --- the generator mirror: SAME float ops as driver.ml / the engine rows ---

def arc_circumcentre(ax, ay, mx, my, ex, ey):
    # exact-Q circumcentre, mirroring driver circumcentre_q; None if collinear
    a1, a2, b1, b2, c1, c2 = F(ax), F(ay), F(mx), F(my), F(ex), F(ey)
    dd = 2 * ((b1 - a1) * (c2 - a2) - (b2 - a2) * (c1 - a1))
    if dd == 0:
        return None
    bk = b1 * b1 + b2 * b2 - a1 * a1 - a2 * a2
    ck = c1 * c1 + c2 * c2 - a1 * a1 - a2 * a2
    ox = ((c2 - a2) * bk - (b2 - a2) * ck) / dd
    oy = ((b1 - a1) * ck - (c1 - a1) * bk) / dd
    r2 = (ox - a1) ** 2 + (oy - a2) ** 2
    return (float(ox), float(oy), math.sqrt(float(r2)))


def arc_sector(ox, oy, a, b, c, q):
    # driver point_on_arc_sector, op-for-op (atan2 sector gate on the FOOT's
    # ray -- rays are angle-invariant, so testing q is testing its foot)
    twopi = 2.0 * math.pi

    def ccw(f, t):
        x = math.fmod(t - f, twopi)
        return x + twopi if x < 0.0 else x

    def ang(px_, py_):
        return math.atan2(py_ - oy, px_ - ox)

    ang_a = ang(a[0], a[1])
    d_ab = ccw(ang_a, ang(b[0], b[1]))
    d_ac = ccw(ang_a, ang(c[0], c[1]))
    d_aq = ccw(ang_a, ang(q[0], q[1]))
    if d_ab <= d_ac:
        return d_aq <= d_ac
    return d_aq >= d_ac or d_aq == 0.0


def row(comp, qx, qy):
    tag = comp[0]
    if tag == "ARC":
        ax, ay, mx, my, ex, ey = comp[1:]
        oxf, oyf, r = arc_circumcentre(ax, ay, mx, my, ex, ey)
        dpa = math.sqrt((qx - ax) * (qx - ax) + (qy - ay) * (qy - ay))
        dpc = math.sqrt((qx - ex) * (qx - ex) + (qy - ey) * (qy - ey))
        cand = dpa if dpa <= dpc else dpc
        d = math.sqrt((qx - oxf) * (qx - oxf) + (qy - oyf) * (qy - oyf))
        if d > 0.0 and arc_sector(oxf, oyf, (ax, ay), (mx, my), (ex, ey),
                                  (qx, qy)):
            radial = abs(d - r)
            if radial < cand:
                cand = radial
        return cand
    if tag == "SEG":
        ax, ay, bx, by = comp[1:]
        dx = bx - ax
        dy = by - ay
        l2 = dx * dx + dy * dy
        if l2 == 0.0:
            return math.sqrt((qx - ax) * (qx - ax) + (qy - ay) * (qy - ay))
        t = ((qx - ax) * dx + (qy - ay) * dy) / l2
        tc = 0.0 if t < 0.0 else (1.0 if t > 1.0 else t)
        fx = ax + tc * dx
        fy = ay + tc * dy
        return math.sqrt((qx - fx) * (qx - fx) + (qy - fy) * (qy - fy))
    x, y = comp[1], comp[2]
    d = math.sqrt((qx - x) * (qx - x) + (qy - y) * (qy - y))
    if tag == "POINT":
        return d
    r = comp[3]
    e = d - r
    if tag == "DISC":
        return 0.0 if e <= 0.0 else e
    if tag == "RING":
        return -e if e < 0.0 else e
    raise ValueError(tag)


def mirror(comps, qx, qy):
    ds = [row(c, qx, qy) for c in comps]
    m = ds[0]
    for d in ds[1:]:
        if d < m:
            m = d
    return m


def fmt(comp):
    return " ".join(str(t) for t in comp)


def assess(name, qx, qy, comps, expect_verdict=None, pin=None,
           mirror_check=False):
    global failures
    line = run(f"{qx} {qy}", [fmt(c) for c in comps])
    tags = []
    p = parse(line)
    if expect_verdict is not None:
        if line != expect_verdict:
            tags.append(f"!! I6_VERDICT got={line!r} want={expect_verdict}")
    else:
        if p is None:
            tags.append(f"!! I6_SHAPE got={line!r}")
        else:
            d, k = p
            if k != len(comps):
                tags.append(f"!! I6_COUNT got={k} want={len(comps)}")
            if pin is not None and d.hex() != pin.hex():
                tags.append(f"!! I1_PIN got={d.hex()} want={pin.hex()}")
            if mirror_check:
                m = mirror(comps, qx, qy)
                if d.hex() != m.hex():
                    tags.append(f"!! I2_MIRROR got={d.hex()} want={m.hex()}")
    status = "   ok" if not tags else "  " + " ".join(tags)
    emit(f"  [{name}] -> '{line}'{status}")
    if tags:
        failures += 1
    return p


TWO_DISCS = [("DISC", -4, 0, 3), ("DISC", 4, 0, 3)]

emit("# Adversarial tests for OBSTACLE_DISTANCE (RocqRefRunner) vs Qed")
emit("# invariants in theories/LECObstacleDistance.v")
emit("# (obstacle_distance_headline, lec_two_discs, min_disc_dist_weighted,")
emit("# corner_clearance_zero, centre_clearance_one).  '!!' lines are")
emit("# PROVEN-invariant violations (CI-failing).")
emit("# I1 3-4-5 pins  I2 weighted mirror  I3 disc-vs-ring  I4 flatten")
emit("# I5 witness grid  I6 verdicts")
emit()

emit("## A. Locked fixture: the 3-4-5 witness cell (discs r=3 at (+-4,0)).")
assess("LEC centre (0,3) -> 2", 0, 3, TWO_DISCS, pin=2.0, mirror_check=True)
assess("mirror maximiser (0,-3) -> 2", 0, -3, TWO_DISCS, pin=2.0,
       mirror_check=True)
assess("rect centre (0,0) -> 1", 0, 0, TWO_DISCS, pin=1.0, mirror_check=True)
for (cx, cy) in ((-4, -3), (-4, 3), (4, -3), (4, 3)):
    assess(f"rect corner ({cx},{cy}) -> 0", cx, cy, TWO_DISCS, pin=0.0,
           mirror_check=True)
emit()

emit("## B. Weighted (Apollonius) mirror: DISC min == clamped weighted min.")
for (qx, qy) in ((1, 2), (-2.5, 1.25), (0, 3), (3.5, -0.5), (0.125, -2.875)):
    assess(f"weighted at ({qx},{qy})", qx, qy, TWO_DISCS, mirror_check=True)
assess("clamp binds inside a disc", 4, 0.5, TWO_DISCS, pin=0.0,
       mirror_check=True)
assess("clamp binds in disc overlap", 0, 0,
       [("DISC", -1, 0, 2), ("DISC", 1, 0, 2)], pin=0.0, mirror_check=True)
emit()

emit("## C. Filled disc vs full-circle ring (the two typed curved rows).")
assess("disc: interior -> 0", 4, 1, [("DISC", 4, 0, 3)], pin=0.0)
assess("ring: same interior -> r-d", 4, 1, [("RING", 4, 0, 3)], pin=2.0,
       mirror_check=True)
assess("disc: on-circle point (7,0)", 7, 0, [("DISC", 4, 0, 3)], pin=0.0,
       mirror_check=True)
assess("ring: on-circle point (7,0)", 7, 0, [("RING", 4, 0, 3)], pin=0.0,
       mirror_check=True)
assess("disc: exterior", 10, 0, [("DISC", 4, 0, 3)], pin=3.0,
       mirror_check=True)
assess("ring: exterior equals disc", 10, 0, [("RING", 4, 0, 3)], pin=3.0,
       mirror_check=True)
assess("ring: centre -> r", 4, 0, [("RING", 4, 0, 3)], pin=3.0,
       mirror_check=True)
emit()

emit("## D. Flatten: permutation / duplication / singleton / mixed rows.")
base = assess("mixed POINT+DISC+RING", 1, 1,
              [("POINT", 0, 3), ("DISC", 4, 0, 3), ("RING", -4, 0, 3)],
              mirror_check=True)
perm = assess("permuted list, same output", 1, 1,
              [("RING", -4, 0, 3), ("POINT", 0, 3), ("DISC", 4, 0, 3)],
              mirror_check=True)
if base is not None and perm is not None and base[0].hex() != perm[0].hex():
    emit("  !! I4_PERM mismatch")
    failures += 1
else:
    emit("  [permutation == original]   ok")
dup = assess("duplicated component, same min", 1, 1,
             [("DISC", 4, 0, 3), ("DISC", 4, 0, 3), ("POINT", 0, 3),
              ("RING", -4, 0, 3)], mirror_check=True)
if base is not None and dup is not None and base[0].hex() != dup[0].hex():
    emit("  !! I4_DUP mismatch")
    failures += 1
else:
    emit("  [duplication == original]   ok")
assess("singleton POINT is euclid", -3, 4, [("POINT", 0, 0)], pin=5.0,
       mirror_check=True)
emit()

emit("## E. Witness-rectangle grid: clearance <= 2, equality only at (0,+-3).")
grid_bad = 0
qy = -3.0
while qy <= 3.0:
    qx = -4.0
    while qx <= 4.0:
        m = mirror(TWO_DISCS, qx, qy)
        line = run(f"{qx} {qy}", [fmt(c) for c in TWO_DISCS])
        p = parse(line)
        if p is None or p[0].hex() != m.hex():
            emit(f"  !! I5_GRID_MIRROR at ({qx},{qy}) got={line!r}"
                 f" want={m.hex()}")
            grid_bad += 1
        elif p[0] > 2.0:
            emit(f"  !! I5_GRID_BOUND at ({qx},{qy}) d={p[0].hex()} > 2")
            grid_bad += 1
        elif p[0] == 2.0 and not (qx == 0.0 and abs(qy) == 3.0):
            emit(f"  !! I5_GRID_MAXIMISER at ({qx},{qy}) unexpected d=2")
            grid_bad += 1
        qx += 0.5
    qy += 0.5
if grid_bad:
    failures += grid_bad
else:
    emit("  [17x13 grid: mirror-exact, bounded by 2, maximisers (0,+-3)]   ok")
emit()

emit("## F. Verdicts.")
assess("k=0 DEGENERATE (empty list)", 0, 0, [], expect_verdict="DEGENERATE")
assess("negative radius DEGENERATE", 0, 0, [("DISC", 1, 1, -3)],
       expect_verdict="DEGENERATE")
assess("unknown tag DEGENERATE", 0, 0, [("BLOB", 1, 1, 1)],
       expect_verdict="DEGENERATE")
assess("wrong arity DEGENERATE", 0, 0, [("DISC", 1, 1)],
       expect_verdict="DEGENERATE")
assess("nan query NAN", float("nan"), 0, [("DISC", 1, 1, 1)],
       expect_verdict="NAN")
assess("nan component NAN", 0, 0, [("RING", float("nan"), 1, 1)],
       expect_verdict="NAN")
assess("NAN wins over DEGENERATE", 0, 0,
       [("DISC", 1, 1, -3), ("POINT", float("nan"), 0)],
       expect_verdict="NAN")
assess("r=0 disc is a point (allowed)", 3, 4, [("DISC", 0, 0, 0)], pin=5.0,
       mirror_check=True)
emit()

emit("## G. ARC members (LECArcRow.v arc_dist_exact + LECFlattenRow.v")
emit("##    empty_disk_flatten_iff): the full 4-row typed table, min-folded.")

F4ARC = ("ARC", 3, 4, 0, 5, -3, 4)  # the F4 witness arc: centre (0,0), r=5


def run_arc_mode(arc, qx, qy):
    stdin = ("ARC_DISTANCE\n%s %s\n%s %s\n%s %s\n%s %s\n"
             % (arc[1], arc[2], arc[3], arc[4], arc[5], arc[6], qx, qy))
    out = subprocess.run([BIN], input=stdin, capture_output=True, text=True)
    return out.stdout.strip()


# singleton ARC is the ARC_DISTANCE kernel, bit-identical across modes
for (qx, qy) in ((16, 12), (0, 8), (10, 0)):
    single = assess(f"singleton ARC at ({qx},{qy})", qx, qy, [F4ARC],
                    mirror_check=True)
    arcline = run_arc_mode(F4ARC, qx, qy)
    try:
        arcval = float.fromhex(arcline)
    except ValueError:
        arcval = None
    if single is None or arcval is None or arcval.hex() != single[0].hex():
        emit(f"  !! I7_PARITY obstacle={single} arc_distance={arcline!r}")
        failures += 1
    else:
        emit(f"  [parity with ARC_DISTANCE at ({qx},{qy})]   ok")
# mixed lists: each typed row wins in turn
assess("mixed: disc beats arc at (16,12)", 16, 12,
       [F4ARC, ("DISC", 4, 0, 3)], mirror_check=True)
assess("mixed: arc radial wins at (0,8) -> 3", 0, 8,
       [F4ARC, ("DISC", 4, 0, 3)], pin=3.0, mirror_check=True)
assess("mixed: point wins at (0,8) -> 1/2", 0, 8,
       [F4ARC, ("POINT", 0, 7.5)], pin=0.5, mirror_check=True)
# flatten invariants with an arc member (I4 pattern across all four rows)
gbase = assess("mixed quad ARC+DISC+RING+POINT", 1, 1,
               [F4ARC, ("DISC", 4, 0, 3), ("RING", -4, 0, 3),
                ("POINT", 0, 3)], mirror_check=True)
gperm = assess("permuted quad, same output", 1, 1,
               [("POINT", 0, 3), ("RING", -4, 0, 3), F4ARC,
                ("DISC", 4, 0, 3)], mirror_check=True)
if gbase is not None and gperm is not None and gbase[0].hex() != gperm[0].hex():
    emit("  !! I7_PERM mismatch")
    failures += 1
else:
    emit("  [arc-quad permutation == original]   ok")
gdup = assess("duplicated arc member, same min", 1, 1,
              [F4ARC, F4ARC, ("DISC", 4, 0, 3), ("RING", -4, 0, 3),
               ("POINT", 0, 3)], mirror_check=True)
if gbase is not None and gdup is not None and gbase[0].hex() != gdup[0].hex():
    emit("  !! I7_DUP mismatch")
    failures += 1
else:
    emit("  [arc duplication == original]   ok")
# verdicts with arcs
assess("degenerate ARC (collinear controls)", 0, 0,
       [("ARC", 0, 0, 1, 1, 2, 2)], expect_verdict="DEGENERATE")
assess("wrong ARC arity DEGENERATE", 0, 0, [("ARC", 1, 2, 3, 4)],
       expect_verdict="DEGENERATE")
assess("nan ARC coord NAN", 0, 0, [("ARC", float("nan"), 4, 0, 5, -3, 4)],
       expect_verdict="NAN")
assess("NAN wins over degenerate ARC", 0, 0,
       [("ARC", 0, 0, 1, 1, 2, 2), ("POINT", float("nan"), 0)],
       expect_verdict="NAN")
emit()

emit("## H. SEG members (LECSegmentRow.v seg_dist exact; the F6 clamp trap).")
SEG40 = ("SEG", 0, 0, 4, 0)
# interior foot: (2,3) projects to (2,0), distance exactly 3
assess("SEG interior foot at (2,3) -> 3", 2, 3, [SEG40], pin=3.0,
       mirror_check=True)
# THE F6 WITNESS: (7,4) has line foot (7,0) at distance 4, but the segment's
# nearest point is the ENDPOINT (4,0) at distance 5 -- the pin refutes the
# unclamped-foot hypothesis in float exactly as the theorem does in R
assess("SEG endpoint clamp at (7,4) -> 5 (line foot would say 4)", 7, 4,
       [SEG40], pin=5.0, mirror_check=True)
assess("SEG endpoint clamp at (-3,4) -> 5", -3, 4, [SEG40], pin=5.0,
       mirror_check=True)
# zero-length facet collapses to the POINT row (seg_dist_degenerate):
# same value, bit-exact, and NOT a DEGENERATE verdict
hseg = assess("zero-length SEG at (5,7) -> 5 (3-4-5)", 5, 7,
              [("SEG", 2, 3, 2, 3)], pin=5.0, mirror_check=True)
hpt = assess("POINT twin of zero-length SEG", 5, 7, [("POINT", 2, 3)],
             pin=5.0, mirror_check=True)
if hseg is not None and hpt is not None and hseg[0].hex() != hpt[0].hex():
    emit("  !! I8_COLLAPSE zero-length SEG != POINT")
    failures += 1
else:
    emit("  [zero-length SEG == POINT row]   ok")
# the full 5-row typed table min-folded (I4 pattern, all five types)
hbase = assess("mixed quint SEG+ARC+DISC+RING+POINT", 1, 1,
               [SEG40, F4ARC, ("DISC", 4, 0, 3), ("RING", -4, 0, 3),
                ("POINT", 0, 3)], mirror_check=True)
hperm = assess("permuted quint, same output", 1, 1,
               [("POINT", 0, 3), F4ARC, ("RING", -4, 0, 3), SEG40,
                ("DISC", 4, 0, 3)], mirror_check=True)
if hbase is not None and hperm is not None \
        and hbase[0].hex() != hperm[0].hex():
    emit("  !! I8_PERM mismatch")
    failures += 1
else:
    emit("  [quint permutation == original]   ok")
# segment row winning the fold: query hugs the facet
assess("mixed: SEG wins at (2,0.25) -> 1/4", 2, 0.25,
       [SEG40, ("DISC", 4, 3, 1), ("POINT", 0, 3)], pin=0.25,
       mirror_check=True)
# verdicts
assess("wrong SEG arity DEGENERATE", 0, 0, [("SEG", 1, 2, 3)],
       expect_verdict="DEGENERATE")
assess("nan SEG coord NAN", 0, 0, [("SEG", float("nan"), 0, 4, 0)],
       expect_verdict="NAN")
emit()

if failures:
    emit(f"# {failures} PROVEN-invariant violation(s) -- RocqRefRunner bug.")
    sys.exit(1)
emit("# All proven invariants (I1-I8) hold across the suite.")
