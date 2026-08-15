#!/usr/bin/env python3
# =============================================================================
# oracle/gen_lec_circle_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for LEC_CIRCLE (RocqRefRunner), the LargestEmptyCircle
# closed form on a circle obstacle -- proof companion theories/LECChordGap.v
# (lec_chord_hypothesis_refuted: the exact LEC of the radius-r circle over
# its disk is (centre, r); the chord path answers r*cos(pi/n), Qed-pinned at
# n = 4 / r = 2 where the chorded answer is sqrt 2).
#
# PROVEN invariants the oracle MUST satisfy (a violation '!!' is a real bug
# and fails CI, mirroring oracle/gen_disc_overlay_tests.py):
#   I1 ECHO        direct-form LEC output is the input circle, bit-exact
#   I2 LOCKED      r=2, n=4 chorded == binary64 sqrt(2), bit-exact
#                  (theories/LECChordGap.v : lec_chorded_answer)
#   I3 UNDER+MONO  chorded < r at every finite n; increasing along the ladder
#   I4 CS==DIRECT  the 5-point CIRCULARSTRING encoding of the same circle
#                  yields the identical output line (circumcentre_q exactness)
#   I5 VERDICTS    r<=0 / collinear CS -> DEGENERATE; non-finite -> NAN;
#                  n < 2 -> DEGENERATE
# =============================================================================

import math
import os
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")

failures = 0


def emit(s=""):
    print(s)


def run(circle_line, n):
    stdin = f"LEC_CIRCLE\n{circle_line}\n{n}\n"
    out = subprocess.run([BIN], input=stdin, capture_output=True, text=True)
    if out.returncode != 0:
        return f"<exit {out.returncode}: {out.stderr.strip()}>"
    return out.stdout.strip()


def parse(line):
    # "LEC <cx> <cy> <r> CHORDED <n> <rn>" -> (cx, cy, r, n, rn) or None
    tok = line.split()
    if len(tok) == 7 and tok[0] == "LEC" and tok[4] == "CHORDED":
        return (float.fromhex(tok[1]), float.fromhex(tok[2]),
                float.fromhex(tok[3]), int(tok[5]), float.fromhex(tok[6]))
    return None


def assess(name, circle_line, n, expect_verdict=None, echo=None,
           pin_hex=None, under_r=None):
    global failures
    line = run(circle_line, n)
    tags = []
    p = parse(line)
    if expect_verdict is not None:
        if line != expect_verdict:
            tags.append(f"!! I5_VERDICT got={line!r} want={expect_verdict}")
    else:
        if p is None:
            tags.append(f"!! I5_SHAPE got={line!r}")
        else:
            cx, cy, r, nn, rn = p
            if echo is not None:
                ex, ey, er = echo
                if not (cx == ex and cy == ey and r == er):
                    tags.append(f"!! I1_ECHO got=({cx.hex()},{cy.hex()},{r.hex()})")
            if pin_hex is not None and rn.hex() != pin_hex:
                tags.append(f"!! I2_LOCKED got={rn.hex()} want={pin_hex}")
            if under_r is not None and not (rn < under_r):
                tags.append(f"!! I3_UNDER rn={rn.hex()} r={under_r.hex()}")
    status = "   ok" if not tags else "  " + " ".join(tags)
    emit(f"  [{name}] -> '{line}'{status}")
    if tags:
        failures += 1
    return parse(line)


emit("# Adversarial tests for LEC_CIRCLE (RocqRefRunner) vs Qed invariants")
emit("# in theories/LECChordGap.v (lec_chord_hypothesis_refuted,")
emit("# lec_circle_closed_form, lec_chorded_answer).  '!!' lines are")
emit("# PROVEN-invariant violations (CI-failing).")
emit("# I1 echo  I2 locked sqrt2 pin  I3 under+monotone  I4 CS==direct  I5 verdicts")
emit()

SQRT2 = math.sqrt(2.0).hex()

emit("## A. Locked fixture: circle (0,0) r=2, the LECChordGap witness cell.")
direct = assess("locked direct n=4", "0 0 2", 4,
                echo=(0.0, 0.0, 2.0), pin_hex=SQRT2, under_r=2.0)
cs = assess("locked CIRCULARSTRING n=4", "CS 2 0 0 2 -2 0 0 -2 2 0", 4,
            echo=(0.0, 0.0, 2.0), pin_hex=SQRT2, under_r=2.0)
if direct is not None and cs is not None and direct != cs:
    emit("  !! I4_CS_DIRECT mismatch")
    failures += 1
else:
    emit("  [locked CS == direct]   ok")
emit()

emit("## B. Underestimate + monotone convergence (circle (3,-1) r=5).")
prev = None
for n in (3, 4, 6, 12, 96, 1024):
    p = assess(f"r=5 n={n}", "3 -1 5", n, echo=(3.0, -1.0, 5.0), under_r=5.0)
    if p is not None:
        if prev is not None and not (p[4] > prev):
            emit(f"  !! I3_MONO n={n} rn={p[4].hex()} prev={prev.hex()}")
            failures += 1
        prev = p[4]
emit()

emit("## C. Degenerate / NaN / bad n.")
assess("r=0 DEGENERATE", "0 0 0", 4, expect_verdict="DEGENERATE")
assess("negative r DEGENERATE", "1 1 -3", 4, expect_verdict="DEGENERATE")
assess("collinear CS DEGENERATE", "CS 0 0 1 1 2 2 3 3 4 4", 4,
       expect_verdict="DEGENERATE")
assess("NaN NAN", "nan 0 2", 4, expect_verdict="NAN")
assess("n=1 DEGENERATE", "0 0 2", 1, expect_verdict="DEGENERATE")
emit()

if failures:
    emit(f"# {failures} PROVEN-invariant violation(s) -- RocqRefRunner bug.")
    sys.exit(1)
emit("# All proven invariants (I1-I5) hold across the suite.")
