#!/usr/bin/env python3
# =============================================================================
# oracle/gen_ffi_parity_tests.py
# -----------------------------------------------------------------------------
# Phase 5 gate: the in-process FFI (`libntsrocq`, oracle/nts_ffi.h) must answer
# BIT-IDENTICALLY to the published `oracle_bin` stdin/stdout protocol on every
# shared entry point.
#
# Both sides call the SAME Coq-extracted symbol (oracle/extracted.ml), so the
# only way they can diverge is a marshalling bug — wrong argument order, a
# dropped sign, a truncated result list, an enum mis-encoded across the C ABI.
# That is exactly the class of bug this harness is here to catch, and exactly
# the class that would otherwise reach production NTS silently.
#
# Invariants gated (a '!!' line fails CI):
#   I1  PARITY     oracle_bin and ffi_probe agree, bit for bit, on every case
#                  (doubles compared as raw IEEE 754 bit patterns, not decimal;
#                  NaN == NaN, and -0.0 != +0.0)
#   I2  TOTALITY   neither side errors on adversarial input (NaN, +/-inf,
#                  +/-0.0, subnormals, 2^512-scale coordinates)
#   I3  ABI        ffi_probe's reported ABI version matches its header
#                  (checked by ffi_probe itself; a mismatch aborts the run)
#
# Coverage: every FFI entry point that has an oracle_bin counterpart.
# `nts_rocq_snap_coord` has no standalone oracle mode; it is exercised
# indirectly through SNAP_SCALED (scale = 1) and listed in the summary.
# `nts_rocq_orient_sign_exact` is gated twice: against ORIENT_EXACT (the
# independent zarith re-implementation — a genuine arithmetic differential
# test, the only pairing here whose two sides share no code) and against
# ORIENT_EXACT_EXTRACTED (the same extracted symbol — marshalling parity).
#
# Run from repo root (after `make -C oracle` and `make -C oracle ffi`):
#   python3 oracle/gen_ffi_parity_tests.py
# Exit status: nonzero iff a gated invariant fails.
# =============================================================================
import math
import os
import random
import struct
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
PROBE = os.environ.get("FFI_PROBE", "oracle/ffi_probe")

SEED = 20260727
CASES_PER_MODE = int(os.environ.get("FFI_PARITY_CASES", "60"))

violations = 0
checked = 0


def emit(s=""):
    print(s)


def fail(mode, case, oracle_out, probe_out, why):
    global violations
    violations += 1
    emit(f"!! {mode} parity violation ({why})")
    emit(f"!!   input : {' '.join(case)}")
    emit(f"!!   oracle: {oracle_out!r}")
    emit(f"!!   ffi   : {probe_out!r}")


# ---------------------------------------------------------------------------
# Exact value plumbing.  Every number crosses both boundaries as a hex float,
# which OCaml's float_of_string and C's strtod parse identically and exactly.
# ---------------------------------------------------------------------------


def hx(v):
    return float(v).hex()


def bits(x):
    """Canonical comparison key for a double: NaN collapses (the oracle's
    textual output does not carry a payload), everything else is exact —
    so -0.0 and +0.0 are distinguished."""
    if math.isnan(x):
        return "nan"
    return struct.pack(">d", x).hex()


def bits_of_token(tok):
    """Oracle side: '0x1.8p+0' / 'nan' / 'infinity' -> comparison key."""
    try:
        return bits(float.fromhex(tok))
    except ValueError:
        return bits(float(tok))


def bits_of_probe(tok):
    """Probe side: '#3ff0000000000000' -> comparison key."""
    assert tok.startswith("#"), tok
    return bits(struct.unpack(">d", bytes.fromhex(tok[1:]))[0])


ORIENT_CODE = {"POS": 1, "NEG": -1, "ZERO": 0, "NAN": 2, "UNCERTAIN": 3}
INTERSECT_CODE = {"NONE": 0, "POINT": 1, "COLLINEAR": 2, "NAN": 3, "UNCERTAIN": 4}
BOOL_CODE = {"FALSE": 0, "TRUE": 1}
OP_NAME = ["UNION", "INTERSECTION", "DIFFERENCE", "SYMDIFF"]


def run_oracle(lines):
    inp = "\n".join(lines) + "\n"
    r = subprocess.run([BIN], input=inp, capture_output=True, text=True)
    if r.returncode != 0:
        return None
    return r.stdout.strip()


def run_probe(mode, vals):
    inp = " ".join(vals) + "\n"
    r = subprocess.run([PROBE, mode], input=inp, capture_output=True, text=True)
    if r.returncode != 0:
        return None
    return r.stdout.strip()


# ---------------------------------------------------------------------------
# Per-mode adapters.
#
#   oracle_lines(vals) -> stdin for oracle_bin
#   norm_oracle(out)   -> comparison tuple
#   norm_probe(out)    -> comparison tuple
# ---------------------------------------------------------------------------


def pts(vals, n, off=0):
    return [f"{vals[off + 2 * i]} {vals[off + 2 * i + 1]}" for i in range(n)]


def norm_sign_and_value(code_table):
    def f(out):
        t = out.split()
        return (code_table[t[0]], bits_of_token(t[1]))

    return f


def norm_probe_int_and_value(out):
    t = out.split()
    return (int(t[0]), bits_of_probe(t[1]))


def norm_code_only(code_table):
    def f(out):
        return (code_table[out.split()[0]],)

    return f


def norm_probe_int_only(out):
    return (int(out.split()[0]),)


MODES = {}


def mode(name, arity, oracle_lines, norm_oracle, norm_probe, gen, probe_mode=None):
    # probe_mode lets several oracle_bin modes gate the SAME ffi_probe entry
    # point (e.g. ORIENT_EXACT and ORIENT_EXACT_EXTRACTED both against
    # nts_rocq_orient_sign_exact, making the gate a differential check
    # between the zarith and extracted implementations).
    MODES[name] = dict(
        arity=arity,
        oracle_lines=oracle_lines,
        norm_oracle=norm_oracle,
        norm_probe=norm_probe,
        gen=gen,
        probe_mode=probe_mode or name,
    )


# ---- Phase 0 --------------------------------------------------------------


def gen_orient(rng, curated_only=False):
    curated = [
        (0, 0, 1, 0, 0, 1),                                    # unit CCW
        (0, 0, 0, 1, 1, 0),                                    # unit CW
        (0, 0, 1, 1, 2, 2),                                    # collinear
        (0, 0, 0, 0, 0, 0),                                    # all-degenerate
        (0, 0, 1, 0, 1, 0),                                    # repeated vertex
        # near-collinear at 2^27: the naive determinant rounds to zero
        (0, 0, 134217729, 134217730, 134217728, 134217729),
        (0.0, -0.0, 1.0, -0.0, -0.0, 1.0),                     # signed zeros
        (0, 0, 2.0 ** 512, 0, 0, 2.0 ** 512),                  # overflow band
        (0, 0, 2.0 ** -540, 0, 0, 2.0 ** -540),                # underflow band
        (0, 0, 5e-324, 0, 0, 5e-324),                          # subnormal
        (float("nan"), 0, 1, 0, 0, 1),                         # NaN in
        (float("inf"), 0, 1, 0, 0, 1),                         # +inf in
        (0, 0, float("-inf"), 0, 0, 1),                        # -inf in
        # magnitudes that put the Stage A filter in its UNCERTAIN band
        (0, 0, 1e16, 1e16, 1e16, 1e16 + 2.0),
    ]
    out = [tuple(map(hx, c)) for c in curated]
    if curated_only:
        return out
    for _ in range(CASES_PER_MODE):
        scale = rng.choice([1.0, 1e-8, 1e8, 2.0 ** 27, 2.0 ** 60])
        c = [rng.uniform(-1.0, 1.0) * scale for _ in range(6)]
        if rng.random() < 0.35:  # force near-collinearity
            c[4] = c[0] + (c[2] - c[0]) * 2.0
            c[5] = c[1] + (c[3] - c[1]) * 2.0 + rng.choice([0.0, 1e-9, -1e-9])
        out.append(tuple(map(hx, c)))
    return out


mode(
    "ORIENT_FILTERED", 6,
    lambda v: ["ORIENT_FILTERED"] + pts(v, 3),
    norm_sign_and_value(ORIENT_CODE),
    norm_probe_int_and_value,
    gen_orient,
)

mode(
    "ORIENT", 6,
    lambda v: ["ORIENT"] + pts(v, 3),
    norm_sign_and_value(ORIENT_CODE),
    norm_probe_int_and_value,
    gen_orient,
)


def gen_orient_exact(rng, curated_only=False):
    """Adversarial corpus for the EXACT full-plane sign: everything the
    filtered corpus has, plus cases that only bite once mantissas are
    aligned to a common exponent (huge binade spreads, all-subnormal
    triangles, one-ulp perturbations at the top of the range)."""
    out = gen_orient(rng, curated_only=True)
    extra = [
        # exact collinearity across a ~2000-binade exponent spread: the
        # shifted integer mantissas are ~2000-bit on both sides
        (0, 0, 2.0 ** -1000, 2.0 ** -1000, 2.0 ** 1000, 2.0 ** 1000),
        (0, 0, 5e-324, 5e-324, 1e308, 1e308),          # min subnormal -> near max
        (5e-324, 0, 0, 5e-324, -5e-324, 0),            # all-subnormal triangle
        # smallest representable CCW / CW perturbations at 2^1000
        (0, 0, 2.0 ** 1000, 2.0 ** 1000, 2.0 ** 1000, 2.0 ** 1000 + 2.0 ** 948),
        (0, 0, 2.0 ** 1000, 2.0 ** 1000 + 2.0 ** 948, 2.0 ** 1000, 2.0 ** 1000),
        (float("inf"), float("inf"), float("-inf"), float("-inf"),
         float("nan"), float("nan")),                  # all-non-finite
    ]
    out += [tuple(map(hx, c)) for c in extra]
    if curated_only:
        return out
    scales = [1.0, 1e-8, 1e8, 2.0 ** 27, 2.0 ** 60,
              2.0 ** -300, 2.0 ** 300, 2.0 ** -1022]
    for _ in range(CASES_PER_MODE):
        # per-coordinate scales stress the min-exponent alignment
        c = [rng.uniform(-1.0, 1.0) * rng.choice(scales) for _ in range(6)]
        if rng.random() < 0.35:  # force (near-)collinearity
            c[4] = c[0] + (c[2] - c[0]) * 2.0
            c[5] = c[1] + (c[3] - c[1]) * 2.0 + rng.choice([0.0, 1e-9, -1e-9])
        out.append(tuple(map(hx, c)))
    return out


# nts_rocq_orient_sign_exact vs the zarith ORIENT_EXACT mode: the two sides
# share NO arithmetic (frexp + zarith bignums vs extracted Coq Z plus the
# bit-level decode overrides), so this pairing is a genuine differential
# correctness check, not just marshalling parity.
mode(
    "ORIENT_EXACT", 6,
    lambda v: ["ORIENT_EXACT"] + pts(v, 3),
    norm_code_only(ORIENT_CODE),
    norm_probe_int_only,
    gen_orient_exact,
)

# ... and vs ORIENT_EXACT_EXTRACTED, which routes through the same extracted
# symbol the FFI calls: this half IS the marshalling-parity gate.
mode(
    "ORIENT_EXACT_EXTRACTED", 6,
    lambda v: ["ORIENT_EXACT_EXTRACTED"] + pts(v, 3),
    norm_code_only(ORIENT_CODE),
    norm_probe_int_only,
    gen_orient_exact,
    probe_mode="ORIENT_EXACT",
)


# ---- Phase 1 --------------------------------------------------------------


def gen_intersect(rng, curated_only=False):
    curated = [
        (0, 0, 2, 2, 0, 2, 2, 0),          # proper cross at (1,1)
        (0, 0, 1, 0, 2, 0, 3, 0),          # collinear disjoint
        (0, 0, 1, 0, 0.5, 0, 2, 0),        # collinear overlapping
        (0, 0, 1, 1, 2, 2, 3, 3),          # collinear along y=x
        (0, 0, 1, 0, 0, 1, 1, 1),          # parallel
        (0, 0, 1, 1, 1, 1, 2, 0),          # touching at an endpoint
        (0, 0, 0, 0, 1, 1, 1, 1),          # both degenerate
        (0, 0, 2, 2, 0, 2, 2, 0.0000001),  # barely-off cross
        (float("nan"), 0, 1, 1, 0, 1, 1, 0),
        (0, 0, float("inf"), 0, 0, 1, 1, 1),
        (0.0, -0.0, 1.0, -0.0, 0.5, -1.0, 0.5, 1.0),
        (2.0 ** 512, 0, -(2.0 ** 512), 0, 0, 2.0 ** 512, 0, -(2.0 ** 512)),
    ]
    out = [tuple(map(hx, c)) for c in curated]
    if curated_only:
        return out
    for _ in range(CASES_PER_MODE):
        scale = rng.choice([1.0, 1e-6, 1e6, 2.0 ** 30])
        c = [rng.uniform(-1.0, 1.0) * scale for _ in range(8)]
        if rng.random() < 0.3:  # share an endpoint
            c[4], c[5] = c[2], c[3]
        out.append(tuple(map(hx, c)))
    return out


mode(
    "INTERSECT_FILTERED", 8,
    lambda v: ["INTERSECT_FILTERED"] + pts(v, 4),
    norm_code_only(INTERSECT_CODE),
    norm_probe_int_only,
    gen_intersect,
)


def norm_oracle_ipf(out):
    t = out.split()
    if t[0] == "NONE":
        return (0,)
    return (1, bits_of_token(t[1]), bits_of_token(t[2]))


def norm_probe_ipf(out):
    t = out.split()
    if t[0] == "0":
        return (0,)
    return (1, bits_of_probe(t[1]), bits_of_probe(t[2]))


mode(
    "INTERSECT_POINT_FILTERED", 8,
    lambda v: ["INTERSECT_POINT_FILTERED"] + pts(v, 4),
    norm_oracle_ipf,
    norm_probe_ipf,
    gen_intersect,
)


def norm_oracle_xy(out):
    t = out.split()
    return (bits_of_token(t[1]), bits_of_token(t[2]))


def norm_probe_xy(out):
    t = out.split()
    return (bits_of_probe(t[1]), bits_of_probe(t[2]))


mode(
    "INTERSECT_POINT_XY", 8,
    lambda v: ["INTERSECT_POINT_XY"] + pts(v, 4),
    norm_oracle_xy,
    norm_probe_xy,
    gen_intersect,
)


# ---- Phase 2 --------------------------------------------------------------


def gen_passes(rng, curated_only=False):
    curated = [
        (0, 0, 10, 10, 5, 5),              # diagonal through the centre
        (0, 0, 10, 0, 5, 0),               # along the x axis
        (0, 0, 10, 0, 5, 1),               # exactly one pixel above
        (0, 0, 10, 0, 5, 0.5),             # on the pixel boundary
        (0, 0, 10, 0, 5, -0.5),            # on the other boundary
        (0.5, 0.5, 0.5, 0.5, 0, 0),        # degenerate segment at a corner
        (0, 0, 1e-16, 1e-16, 0, 0),        # sub-ulp segment
        (float("nan"), 0, 1, 1, 0, 0),
        (0, 0, float("inf"), float("inf"), 3, 3),
        (-0.0, -0.0, 1.0, 1.0, -0.0, -0.0),
    ]
    out = [tuple(map(hx, c)) for c in curated]
    if curated_only:
        return out
    for _ in range(CASES_PER_MODE):
        cx, cy = float(rng.randint(-8, 8)), float(rng.randint(-8, 8))
        # aim segments at pixel boundaries, where the filter is most delicate
        jitter = rng.choice([0.0, 0.5, -0.5, 0.5 + 2.0 ** -30, 0.5 - 2.0 ** -30])
        c = [
            cx + rng.uniform(-4, 4), cy + rng.uniform(-4, 4),
            cx + rng.uniform(-4, 4), cy + jitter,
            cx, cy,
        ]
        out.append(tuple(map(hx, c)))
    return out


mode(
    "PASSES_THROUGH_FILTER", 6,
    lambda v: ["PASSES_THROUGH_FILTER"] + pts(v, 3),
    norm_code_only(BOOL_CODE),
    norm_probe_int_only,
    gen_passes,
)

mode(
    "PASSES_THROUGH_HALFOPEN", 6,
    lambda v: ["PASSES_THROUGH_HALFOPEN"] + pts(v, 3),
    norm_code_only(BOOL_CODE),
    norm_probe_int_only,
    gen_passes,
)


def gen_snap(rng, curated_only=False):
    curated = [
        (1, 0.5, 1.5),                     # both ties -> round half to even
        (1, -0.5, -1.5),
        (1, 2.5, 3.5),
        (4, 0.125, 0.375),                 # quarter grid
        (1024, 1.0 / 3.0, -1.0 / 7.0),
        (1, 0.0, -0.0),                    # signed zero through the grid
        (1, float("nan"), float("inf")),
        (2.0 ** 30, 2.0 ** -20, -(2.0 ** -20)),
    ]
    out = [tuple(map(hx, c)) for c in curated]
    if curated_only:
        return out
    for _ in range(CASES_PER_MODE):
        s = float(2 ** rng.randint(0, 20))
        out.append((hx(s), hx(rng.uniform(-1e6, 1e6)), hx(rng.uniform(-1e6, 1e6))))
    return out


mode(
    "SNAP_SCALED", 3,
    lambda v: ["SNAP_SCALED", v[0], f"{v[1]} {v[2]}"],
    lambda out: tuple(bits_of_token(t) for t in out.split()),
    lambda out: tuple(bits_of_probe(t) for t in out.split()[1:]),
    gen_snap,
)


# ---- Phase 3 --------------------------------------------------------------


def gen_edge(rng, curated_only=False):
    return [
        (hx(op), hx(left), hx(right))
        for op in range(4)
        for left in (0, 1)
        for right in (0, 1)
    ]


mode(
    "EDGE_IN_RESULT", 3,
    lambda v: [
        "EDGE_IN_RESULT",
        OP_NAME[int(float.fromhex(v[0]))],
        "true" if float.fromhex(v[1]) != 0 else "false",
        "true" if float.fromhex(v[2]) != 0 else "false",
    ],
    norm_code_only(BOOL_CODE),
    norm_probe_int_only,
    gen_edge,
)


# ---- Phase 4 --------------------------------------------------------------


def gen_incircle(rng, curated_only=False):
    curated = [
        (0, 0, 1, 0, 0, 1, 0.25, 0.25),        # strictly inside
        (0, 0, 1, 0, 0, 1, 5, 5),              # strictly outside
        (0, 0, 1, 0, 0, 1, 1, 1),              # exactly on the circle
        (0, 0, 1, 0, 2, 0, 3, 0),              # collinear defining points
        (0, 0, 0, 0, 0, 0, 0, 0),
        (0, 0, 1, 0, 0, 1, float("nan"), 0),
        (0, 0, 2.0 ** 200, 0, 0, 2.0 ** 200, 1, 1),
        (0.0, -0.0, 1.0, -0.0, -0.0, 1.0, 0.5, 0.5),
    ]
    out = [tuple(map(hx, c)) for c in curated]
    if curated_only:
        return out
    for _ in range(CASES_PER_MODE):
        scale = rng.choice([1.0, 1e-4, 1e4, 2.0 ** 20])
        out.append(tuple(hx(rng.uniform(-1, 1) * scale) for _ in range(8)))
    return out


mode(
    "INCIRCLE_SIGN", 8,
    lambda v: ["INCIRCLE_SIGN"] + pts(v, 4),
    lambda out: (bits_of_token(out.split()[1]),),
    lambda out: (bits_of_probe(out.split()[1]),),
    gen_incircle,
)


def gen_arc_chord(rng, curated_only=False):
    curated = [
        (1, 0, 0, 1, -1, 0, 0, -2, 0, 2),      # chord through the unit circle
        (1, 0, 0, 1, -1, 0, 2, 2, 3, 3),       # chord entirely outside
        (1, 0, 0, 1, -1, 0, 0, 0, 0.5, 0.5),   # chord entirely inside
        (1, 0, 0, 1, -1, 0, 1, 0, -1, 0),      # chord on the circle
        (0, 0, 1, 1, 2, 2, 0, 1, 1, 0),        # degenerate (collinear) arc
        (1, 0, 0, 1, -1, 0, float("nan"), 0, 1, 1),
    ]
    out = [tuple(map(hx, c)) for c in curated]
    if curated_only:
        return out
    for _ in range(CASES_PER_MODE):
        r = rng.uniform(0.5, 100.0)
        cx, cy = rng.uniform(-10, 10), rng.uniform(-10, 10)
        a0, a1, a2 = sorted(rng.uniform(0, 2 * math.pi) for _ in range(3))
        arc = []
        for a in (a0, a1, a2):
            arc += [cx + r * math.cos(a), cy + r * math.sin(a)]
        chord = [rng.uniform(-1, 1) * 2 * r + cx, rng.uniform(-1, 1) * 2 * r + cy,
                 rng.uniform(-1, 1) * 2 * r + cx, rng.uniform(-1, 1) * 2 * r + cy]
        out.append(tuple(map(hx, arc + chord)))
    return out


mode(
    "ARC_CHORD_CROSSES_CIRCLE", 10,
    lambda v: ["ARC_CHORD_CROSSES_CIRCLE"] + pts(v, 5),
    norm_code_only(BOOL_CODE),
    norm_probe_int_only,
    gen_arc_chord,
)

mode(
    "ARC_LINE_XY", 10,
    lambda v: ["ARC_LINE_XY"] + pts(v, 5),
    norm_oracle_xy,
    norm_probe_xy,
    gen_arc_chord,
)


def gen_arc_pixel(rng, curated_only=False):
    curated = [
        (1, 0, 0, 1, -1, 0, 0, 0, 1),          # unit circle through the origin pixel
        (1, 0, 0, 1, -1, 0, 5, 5, 1),          # far pixel
        (1, 0, 0, 1, -1, 0, 1, 0, 1),          # pixel at the arc start
        (1, 0, 0, 1, -1, 0, 0, 0, 1024),       # fine grid
        (0, 0, 1, 1, 2, 2, 1, 1, 1),           # degenerate arc
        (1, 0, 0, 1, -1, 0, float("nan"), 0, 1),
    ]
    out = [tuple(map(hx, c)) for c in curated]
    if curated_only:
        return out
    for _ in range(CASES_PER_MODE):
        r = rng.uniform(0.5, 20.0)
        cx, cy = rng.uniform(-5, 5), rng.uniform(-5, 5)
        a0, a1, a2 = sorted(rng.uniform(0, 2 * math.pi) for _ in range(3))
        arc = []
        for a in (a0, a1, a2):
            arc += [cx + r * math.cos(a), cy + r * math.sin(a)]
        scale = float(2 ** rng.randint(0, 8))
        arc += [float(rng.randint(-10, 10)), float(rng.randint(-10, 10)), scale]
        out.append(tuple(map(hx, arc)))
    return out


mode(
    "ARC_PASSES_THROUGH_PIXEL", 9,
    lambda v: ["ARC_PASSES_THROUGH_PIXEL"] + pts(v, 4) + [v[8]],
    norm_code_only(BOOL_CODE),
    norm_probe_int_only,
    gen_arc_pixel,
)


# ---- Stage D --------------------------------------------------------------


def gen_twosum(rng, curated_only=False):
    curated = [
        (1.0, 2.0 ** -60),                 # classic non-representable sum
        (1.0, -1.0),
        (0.0, -0.0),
        (2.0 ** 1000, 2.0 ** -1000),
        (5e-324, 5e-324),                  # subnormals
        (float("inf"), 1.0),
        (float("nan"), 1.0),
        (2.0 ** 1023, 2.0 ** 1023),        # overflow to inf
    ]
    out = [tuple(map(hx, c)) for c in curated]
    if curated_only:
        return out
    for _ in range(CASES_PER_MODE):
        e1, e2 = rng.randint(-80, 80), rng.randint(-80, 80)
        out.append((hx(rng.uniform(-1, 1) * 2.0 ** e1),
                    hx(rng.uniform(-1, 1) * 2.0 ** e2)))
    return out


mode(
    "TWOSUM", 2,
    lambda v: ["TWOSUM", v[0], v[1]],
    lambda out: (bits_of_token(out.split()[1]), bits_of_token(out.split()[3])),
    lambda out: tuple(bits_of_probe(t) for t in out.split()[1:]),
    gen_twosum,
)


def gen_grow(rng, curated_only=False):
    curated = [
        (1.0, 2.0 ** -60, 2.0 ** -120),
        (1.0, -1.0, 1.0),
        (0.0, 0.0),
        (2.0 ** 60, 1.0, 2.0 ** -60, 2.0 ** -120),
        (float("inf"), 1.0),
    ]
    out = [tuple(map(hx, c)) for c in curated]
    if curated_only:
        return out
    for _ in range(CASES_PER_MODE):
        n = rng.randint(1, 6)
        vals = [rng.uniform(-1, 1) * 2.0 ** rng.randint(-60, 60) for _ in range(n + 1)]
        out.append(tuple(map(hx, vals)))
    return out


def norm_oracle_grow(out):
    keys = []
    for line in out.splitlines():
        t = line.split()
        if t[0] in ("QFINAL", "H"):
            keys.append(bits_of_token(t[1]))
    return tuple(keys)


mode(
    "GROW_EXPANSION", None,
    lambda v: ["GROW_EXPANSION"] + list(v),
    norm_oracle_grow,
    lambda out: tuple(bits_of_probe(t) for t in out.split()[1:]),
    gen_grow,
)


# ---- Simplifier -----------------------------------------------------------


def gen_simplify(rng, curated_only=False):
    curated = [
        (1.0, 0, 0, 1, 0.1, 2, 0),                     # middle point within eps
        (0.01, 0, 0, 1, 0.1, 2, 0),                    # middle point kept
        (1.0, 0, 0),                                   # single point
        (1.0,),                                        # empty polyline
        (1.0, 0, 0, 0, 0, 0, 0),                       # repeated points
        (1.0, 0, 0, 1, 0, 2, 0, 3, 0, 4, 0),           # straight line
        (float("nan"), 0, 0, 1, 1, 2, 0),
        (1.0, 0, 0, 2.0 ** 60, 2.0 ** 60, 2.0 ** 61, 0),
    ]
    out = [tuple(map(hx, c)) for c in curated]
    if curated_only:
        return out
    for _ in range(CASES_PER_MODE):
        n = rng.randint(2, 12)
        vals = [rng.choice([0.001, 0.1, 1.0, 10.0])]
        for _ in range(n):
            vals += [rng.uniform(-10, 10), rng.uniform(-10, 10)]
        out.append(tuple(map(hx, vals)))
    return out


def norm_oracle_simplify(out):
    keys = []
    for line in out.splitlines():
        t = line.split()
        if len(t) == 2:
            keys += [bits_of_token(t[0]), bits_of_token(t[1])]
    return (len(keys) // 2,) + tuple(keys)


def norm_probe_simplify(out):
    t = out.split()
    return (int(t[0]),) + tuple(bits_of_probe(x) for x in t[1:])


mode(
    "SIMPLIFY", None,
    lambda v: ["SIMPLIFY", v[0]] + [f"{v[1 + 2 * i]} {v[2 + 2 * i]}"
                                    for i in range((len(v) - 1) // 2)],
    norm_oracle_simplify,
    norm_probe_simplify,
    gen_simplify,
)


# ---------------------------------------------------------------------------
# Driver.
# ---------------------------------------------------------------------------


def main():
    global checked

    for path, what in ((BIN, "oracle_bin"), (PROBE, "ffi_probe")):
        if not os.path.exists(path):
            emit(f"!! missing {what}: {path}")
            emit("!! build it with: make -C oracle && make -C oracle ffi")
            return 1

    emit("# FFI <-> oracle_bin parity (Phase 5)")
    emit("# libntsrocq in-process results vs the oracle_bin stdin/stdout protocol.")
    emit("# Doubles compared as raw IEEE 754 bit patterns; NaN == NaN, -0.0 != +0.0.")
    emit("#")

    rng = random.Random(SEED)
    for name, spec in MODES.items():
        cases = spec["gen"](rng)
        mismatches = 0
        for case in cases:
            oracle_out = run_oracle(spec["oracle_lines"](case))
            probe_out = run_probe(spec["probe_mode"], list(case))
            checked += 1
            if oracle_out is None or probe_out is None:
                fail(name, case, oracle_out, probe_out, "I2 TOTALITY: a side errored")
                mismatches += 1
                continue
            try:
                a = spec["norm_oracle"](oracle_out)
                b = spec["norm_probe"](probe_out)
            except (ValueError, IndexError, KeyError) as exc:
                fail(name, case, oracle_out, probe_out, f"unparsable output: {exc}")
                mismatches += 1
                continue
            if a != b:
                fail(name, case, oracle_out, probe_out, f"I1 PARITY: {a} != {b}")
                mismatches += 1
        status = "OK" if mismatches == 0 else f"{mismatches} MISMATCH"
        emit(f"{name:<26} {len(cases):>4} cases   {status}")

    emit("#")
    emit(f"# nts_rocq_snap_coord: no standalone oracle mode; covered via SNAP_SCALED.")
    emit(f"# total cases checked: {checked}")
    if violations:
        emit(f"!! {violations} parity violation(s)")
        return 1
    emit("# I1 PARITY ok, I2 TOTALITY ok, I3 ABI ok")
    return 0


if __name__ == "__main__":
    sys.exit(main())
