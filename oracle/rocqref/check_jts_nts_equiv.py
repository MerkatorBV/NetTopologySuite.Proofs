#!/usr/bin/env python3
"""Pin RocqRefRunner.refSign against the Qed formula.

This is the JTS ↔ NTS port gate for the integer-domain reference
(theories/RocqRefRunner.v : rocqref_refSign_eq_cross). It does not
call production Orientation.index and it does not spawn oracle_bin.

Every row of jts_nts_equiv_vectors.txt must match
    sgn((p1x-p0x)*(qy-p0y) - (qx-p0x)*(p1y-p0y))
with |coord| <= 2**25.
"""
from __future__ import annotations

import sys
from pathlib import Path

SAFE_BOUND = 1 << 25
VECTORS = Path(__file__).with_name("jts_nts_equiv_vectors.txt")


def ref_sign(p0x, p0y, p1x, p1y, qx, qy) -> int:
    det = (p1x - p0x) * (qy - p0y) - (qx - p0x) * (p1y - p0y)
    return (det > 0) - (det < 0)


def in_domain(c: int) -> bool:
    return -SAFE_BOUND <= c <= SAFE_BOUND


def load_rows(path: Path):
    rows = []
    for line_no, raw in enumerate(path.read_text().splitlines(), 1):
        s = raw.split("#", 1)[0].strip()
        if not s:
            continue
        parts = s.split()
        if len(parts) != 7:
            raise SystemExit(f"{path}:{line_no}: expected 7 fields, got {len(parts)}")
        coords = [int(x) for x in parts]
        rows.append((line_no, coords))
    return rows


def main() -> int:
    rows = load_rows(VECTORS)
    if not rows:
        print("no vectors", file=sys.stderr)
        return 2
    bad = 0
    for line_no, (p0x, p0y, p1x, p1y, qx, qy, expected) in rows:
        for c in (p0x, p0y, p1x, p1y, qx, qy):
            if not in_domain(c):
                print(f"{VECTORS}:{line_no}: coord {c} outside ±2^25", file=sys.stderr)
                bad += 1
        got = ref_sign(p0x, p0y, p1x, p1y, qx, qy)
        if got != expected:
            print(
                f"{VECTORS}:{line_no}: expected {expected} got {got} "
                f"for ({p0x},{p0y}) ({p1x},{p1y}) ({qx},{qy})",
                file=sys.stderr,
            )
            bad += 1
    if bad:
        print(f"FAIL {bad} mismatch(es) in {len(rows)} rows", file=sys.stderr)
        return 1
    print(f"ok {len(rows)} RocqRefRunner JTS↔NTS vectors match Z.sgn(idet)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
