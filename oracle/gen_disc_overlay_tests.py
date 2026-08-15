#!/usr/bin/env python3
# =============================================================================
# oracle/gen_disc_overlay_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the DISC_OVERLAY oracle mode (OV-DISC / OverlayNGCurve
# two-disc closed form), driven by the RocqRefRunner (oracle_bin).
#
# Ground truth ties directly to the Qed-proven theorems in
# theories/DiscOverlay.v (and the reused ArcArcCircles radical-axis kernel):
#
#   * radical-axis nodes lie on BOTH circles
#         (radical_nodes_in_lens / radical_points_on_circles)
#   * locked fixture centres (0,0) and (7,0), r=5 → nodes (3.5, ±√12.75)
#         (locked_disc_nodes)
#   * point-set algebra: CAP ∪ XOR = CUP, CAP ∪ SUB = A
#         (lens_or_crescents_iff_blob / lens_or_crescent_iff_A)
#   * coincident discs reject (d==0 ∧ r1==r2)
#
# PROVEN invariants the oracle MUST satisfy (a violation '!!' is a real bug
# and fails CI, mirroring oracle/gen_adversarial_tests.sh / gen_arc_arc_tests.py):
#
#   I1  ON-BOTH-CIRCLES   every CROSSING/TANGENT node lies on BOTH discs'
#                         circumcircles (two_circles_radical_point).
#   I2  LOCKED-FIXTURE    CAP of (0,0)r=5 vs (7,0)r=5 emits nodes
#                         (3.5, ±√12.75) — locked_disc_nodes.
#   I3  CAP+XOR=CUP       area(CAP)+area(XOR) == area(CUP)  (point-set).
#   I4  CAP+SUB=A         area(CAP)+area(SUB) == π r1²      (point-set).
#   I5  DISJOINT-AREAS    CAP=0 and CUP=π(r1²+r2²) when d > r1+r2.
#   I6  SYMMETRY          CAP/CUP/XOR areas and node-sets survive A↔B swap.
#   I7  COINCIDENT        identical discs → COINCIDENT reject.
#
# Run from repo root:
#   python3 oracle/gen_disc_overlay_tests.py > oracle/disc_overlay_tests.txt
# Exit status: nonzero iff a PROVEN invariant (I1-I7) is violated.
# =============================================================================
import math
import os
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")

violations = 0

PI = math.acos(-1.0)
LOCKED_H = math.sqrt(12.75)  # √(51/4) = √12.75


def emit(s=""):
    print(s)


def run(op, disc_a, disc_b):
    """disc_* is a string line (centre+radius or CS ...). Returns raw oracle line."""
    stdin = f"DISC_OVERLAY\n{op}\n{disc_a}\n{disc_b}\n"
    out = subprocess.run([BIN], input=stdin, capture_output=True, text=True)
    if out.returncode != 0:
        return f"ERR rc={out.returncode} {out.stderr.strip()}"
    return out.stdout.strip().splitlines()[-1] if out.stdout.strip() else "ERR empty"


def parse_hex(tok):
    if "x" in tok or "p" in tok.lower():
        return float.fromhex(tok)
    return float(tok)


def parse(line):
    """(kind, config, shape, nodes, area) or a reject tag."""
    tok = line.split()
    if not tok:
        return ("NAN", None, None, [], None)
    if tok[0] in ("COINCIDENT", "DEGENERATE", "NAN") and len(tok) == 1:
        return (tok[0], None, None, [], None)
    # <config> <shape> NODES <n> [x y ...] AREA <hex>
    try:
        config, shape = tok[0], tok[1]
        ni = tok.index("NODES")
        n = int(tok[ni + 1])
        coords = [parse_hex(t) for t in tok[ni + 2:ni + 2 + 2 * n]]
        nodes = [(coords[2 * i], coords[2 * i + 1]) for i in range(n)]
        ai = tok.index("AREA")
        area = parse_hex(tok[ai + 1])
        return ("OK", config, shape, nodes, area)
    except (ValueError, IndexError):
        return ("PARSE", None, None, [], None)


def on_both_circles(c1, r1, c2, r2, nodes, tol_scale=1e-9):
    bad = []
    for (x, y) in nodes:
        for (cx, cy, r) in ((c1[0], c1[1], r1), (c2[0], c2[1], r2)):
            res = (x - cx) ** 2 + (y - cy) ** 2 - r * r
            tol = tol_scale * (1.0 + r * r)
            if abs(res) > tol:
                bad.append((x, y, cx, cy, r, res, tol))
    return bad


def node_set_close(a, b, tol=1e-9):
    if len(a) != len(b):
        return False
    used = [False] * len(b)
    for (x, y) in a:
        hit = False
        for i, (u, v) in enumerate(b):
            if used[i]:
                continue
            if abs(x - u) <= tol and abs(y - v) <= tol:
                used[i] = True
                hit = True
                break
        if not hit:
            return False
    return True


def assess(name, op, disc_a, disc_b, meta, expect=None):
    """Run a case, print it, and gate the proven invariants.

    meta keys: c1, r1, c2, r2  (float centres/radii for I1/I3/I4/I5/I6)
               locked (bool)   (I2)
    """
    global violations
    line = run(op, disc_a, disc_b)
    kind, config, shape, nodes, area = parse(line)
    tags = []
    c1, r1 = meta.get("c1"), meta.get("r1")
    c2, r2 = meta.get("c2"), meta.get("r2")

    # I1: returned nodes on both circles.
    if kind == "OK" and nodes and c1 is not None:
        bad = on_both_circles(c1, r1, c2, r2, nodes)
        if bad:
            violations += 1
            tags.append(f"!! I1_OFF_CIRCLE res={bad[0][5]:.3g}>tol{bad[0][6]:.1g}")

    # I2: locked fixture nodes (3.5, ±√12.75).
    if meta.get("locked") and op == "CAP":
        if kind != "OK" or config != "CROSSING" or len(nodes) != 2:
            violations += 1
            tags.append(f"!! I2_LOCKED_SHAPE kind={kind} cfg={config} n={len(nodes)}")
        else:
            xs = sorted(nodes, key=lambda p: p[1], reverse=True)
            exp = [(3.5, LOCKED_H), (3.5, -LOCKED_H)]
            if not node_set_close(xs, exp, tol=1e-12):
                violations += 1
                tags.append(f"!! I2_LOCKED_NODES got={xs} want={exp}")
            elif abs(xs[0][0] - 3.5) > 0 or abs(xs[1][0] - 3.5) > 0:
                # x must be exactly 3.5 in binary64 (7/2 is dyadic).
                if abs(xs[0][0] - 3.5) > 1e-15 or abs(xs[1][0] - 3.5) > 1e-15:
                    violations += 1
                    tags.append(f"!! I2_LOCKED_X got={[p[0] for p in xs]}")

    # I3 / I4: area algebra on a live pair (skip rejects).
    if kind == "OK" and c1 is not None and op == "CAP":
        cup = parse(run("CUP", disc_a, disc_b))
        sub = parse(run("SUB", disc_a, disc_b))
        xor = parse(run("XOR", disc_a, disc_b))
        if cup[0] == "OK" and xor[0] == "OK":
            lhs = area + xor[4]
            if abs(lhs - cup[4]) > 1e-9 * (1.0 + abs(cup[4])):
                violations += 1
                tags.append(f"!! I3_CAP_XOR_CUP {lhs:.6g}!={cup[4]:.6g}")
        if sub[0] == "OK":
            lhs = area + sub[4]
            want = PI * r1 * r1
            if abs(lhs - want) > 1e-9 * (1.0 + want):
                violations += 1
                tags.append(f"!! I4_CAP_SUB_A {lhs:.6g}!={want:.6g}")

    # I5: disjoint areas.
    if meta.get("disjoint") and op == "CAP" and kind == "OK":
        if abs(area) > 1e-12:
            violations += 1
            tags.append(f"!! I5_DISJOINT_CAP {area}")
        cup = parse(run("CUP", disc_a, disc_b))
        if cup[0] == "OK":
            want = PI * (r1 * r1 + r2 * r2)
            if abs(cup[4] - want) > 1e-9 * (1.0 + want):
                violations += 1
                tags.append(f"!! I5_DISJOINT_CUP {cup[4]:.6g}!={want:.6g}")

    # I6: CAP/CUP/XOR symmetry (node-set + area).
    if kind == "OK" and op in ("CAP", "CUP", "XOR"):
        k2, cfg2, _, nodes2, area2 = parse(run(op, disc_b, disc_a))
        if k2 != "OK" or cfg2 != config:
            violations += 1
            tags.append(f"!! I6_ASYM_CFG {k2}/{cfg2}")
        elif abs((area2 or 0) - area) > 1e-9 * (1.0 + abs(area)):
            violations += 1
            tags.append(f"!! I6_ASYM_AREA {area2:.6g}!={area:.6g}")
        elif not node_set_close(nodes, nodes2, tol=1e-9):
            violations += 1
            tags.append("!! I6_ASYM_NODES")

    # I7: coincident reject.
    if meta.get("coincident"):
        if kind != "COINCIDENT":
            violations += 1
            tags.append(f"!! I7_COINCIDENT got={line!r}")

    exp = "" if expect is None else f" expect={expect}"
    status = " ".join(tags) if tags else "ok"
    emit(f"  [{name}] {op} -> {line!r}{exp}   {status}")
    return line


# ---------------------------------------------------------------------------
emit("# Adversarial tests for DISC_OVERLAY (RocqRefRunner) vs Qed invariants")
emit("# in theories/DiscOverlay.v (radical_nodes_in_lens, locked_disc_nodes,")
emit("# lens_or_crescents_iff_blob).  '!!' lines are PROVEN-invariant")
emit("# violations (CI-failing).")
emit("# I1 on-both-circles  I2 locked (3.5, ±√12.75)  I3 CAP+XOR=CUP")
emit("# I4 CAP+SUB=π r1²   I5 disjoint areas  I6 symmetry  I7 coincident")
emit()

# A. Locked fixture — the accept pin.
emit("## A. Locked fixture CIRCLE_5 ∩ CIRCLE_CROSSING  (0,0)r=5 vs (7,0)r=5.")
locked_meta = dict(c1=(0.0, 0.0), r1=5.0, c2=(7.0, 0.0), r2=5.0, locked=True)
for op in ("CAP", "CUP", "SUB", "XOR"):
    assess(f"locked {op} centre+radius", op, "0 0 5", "7 0 5", locked_meta,
           expect="CROSSING nodes (3.5, ±√12.75)" if op == "CAP" else None)

# Same pair as a 5-point CIRCULARSTRING ring (circumcentre_q path).
cs_a = "CS 5 0 0 5 -5 0 0 -5 5 0"
cs_b = "CS 12 0 7 5 2 0 7 -5 12 0"
assess("locked CAP CIRCULARSTRING", "CAP", cs_a, cs_b, locked_meta,
       expect="CROSSING nodes (3.5, ±√12.75)")

emit()
emit("## B. Equal-r crossing (not the locked pair).")
eq = dict(c1=(0.0, 0.0), r1=5.0, c2=(8.0, 0.0), r2=5.0)
assess("equal-r d=8 CAP", "CAP", "0 0 5", "8 0 5", eq, expect="CROSSING LENS")
assess("equal-r d=8 CUP", "CUP", "0 0 5", "8 0 5", eq)

emit()
emit("## C. Unequal-r crossing.")
un = dict(c1=(0.0, 0.0), r1=5.0, c2=(6.0, 0.0), r2=3.0)
assess("unequal 5-vs-3 d=6 CAP", "CAP", "0 0 5", "6 0 3", un, expect="CROSSING LENS")
assess("unequal 5-vs-3 d=6 SUB", "SUB", "0 0 5", "6 0 3", un)

emit()
emit("## D. Disjoint (d > r1+r2).")
dj = dict(c1=(0.0, 0.0), r1=5.0, c2=(20.0, 0.0), r2=5.0, disjoint=True)
assess("disjoint d=20 CAP", "CAP", "0 0 5", "20 0 5", dj, expect="DISJOINT EMPTY")
assess("disjoint d=20 CUP", "CUP", "0 0 5", "20 0 5", dj, expect="DISJOINT BLOB")
assess("disjoint d=20 SUB", "SUB", "0 0 5", "20 0 5", dj)
assess("disjoint d=20 XOR", "XOR", "0 0 5", "20 0 5", dj)

emit()
emit("## E. External / internal tangent.")
et = dict(c1=(0.0, 0.0), r1=5.0, c2=(10.0, 0.0), r2=5.0)
assess("ext-tangent d=10 CAP", "CAP", "0 0 5", "10 0 5", et, expect="EXT_TANGENT")
it = dict(c1=(0.0, 0.0), r1=5.0, c2=(2.0, 0.0), r2=3.0)
assess("int-tangent d=2 CAP", "CAP", "0 0 5", "2 0 3", it, expect="INT_TANGENT")

emit()
emit("## F. Nested / covers (d < |r1−r2|) and concentric.")
nest = dict(c1=(0.0, 0.0), r1=5.0, c2=(1.0, 0.0), r2=2.0)
assess("nested A-covers-B CAP", "CAP", "0 0 5", "1 0 2", nest, expect="NESTED DISC")
assess("nested A-covers-B SUB", "SUB", "0 0 5", "1 0 2", nest, expect="NESTED CRESCENT")
assess("nested B-covers-A SUB", "SUB", "1 0 2", "0 0 5",
       dict(c1=(1.0, 0.0), r1=2.0, c2=(0.0, 0.0), r2=5.0), expect="NESTED EMPTY")
conc = dict(c1=(0.0, 0.0), r1=5.0, c2=(0.0, 0.0), r2=3.0)
assess("concentric distinct CAP", "CAP", "0 0 5", "0 0 3", conc, expect="NESTED DISC")

emit()
emit("## G. Coincident reject.")
assess("coincident centre+radius", "CAP", "0 0 5", "0 0 5",
       dict(c1=(0.0, 0.0), r1=5.0, c2=(0.0, 0.0), r2=5.0, coincident=True),
       expect="COINCIDENT")
assess("coincident CIRCULARSTRING", "CUP", cs_a, cs_a,
       dict(c1=(0.0, 0.0), r1=5.0, c2=(0.0, 0.0), r2=5.0, coincident=True),
       expect="COINCIDENT")

emit()
emit("## H. Degenerate / NaN.")
assess("r=0 DEGENERATE", "CAP", "0 0 0", "7 0 5",
       dict(c1=(0.0, 0.0), r1=0.0, c2=(7.0, 0.0), r2=5.0), expect="DEGENERATE")
assess("collinear CS DEGENERATE", "CAP",
       "CS 0 0 1 0 2 0 3 0 4 0", "7 0 5",
       dict(), expect="DEGENERATE")

emit()
if violations:
    emit(f"::error::DISC_OVERLAY violated {violations} proven invariant(s) (I1-I7).")
    sys.exit(1)
emit("# All proven invariants (I1-I7) hold across the suite.")
