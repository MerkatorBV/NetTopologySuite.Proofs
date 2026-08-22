#!/usr/bin/env python3
"""Module-split gate for the Rocq corpus.

A module must be split when BOTH hold:

  1. it is a monolith:        lines >= MONOLITH_LINES (1234)
  2. it is load-bearing:      (transitive dependents + 1) * lines >= GATE (3210)

The product is blast-weighted size: it orders the queue and, above the line
floor, decides urgency. The floor is what stops the product from selecting
small foundational modules -- `theories/Distance.v` is 402 lines with 455
transitive dependents (product 182910) and has no size problem whatsoever.

Splits use the established umbrella pattern: the original name stays as a
`Require Export` umbrella, the declaration set is byte-identical, and
`Print Assumptions` footers move verbatim to each declaration's new home. High
fan-in is therefore not a blocker -- importers cannot observe a split.

Usage:
    python docs/scout/split-metric.py            # queue + exemptions
    python docs/scout/split-metric.py --all      # full metric table
"""
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DIRS = ["theories", "theories-flocq"]
MONOLITH_LINES = 1234
GATE = 3210

REQUIRE = re.compile(
    r"^\s*(?:From\s+\S+\s+)?Require\s+(?:Import|Export)?\s*([^.]*)\.", re.M
)


def load():
    """module basename -> (relpath, line count)"""
    out = {}
    for d in DIRS:
        base = os.path.join(ROOT, d)
        if not os.path.isdir(base):
            continue
        for name in sorted(os.listdir(base)):
            if not name.endswith(".v"):
                continue
            with open(os.path.join(base, name), encoding="utf-8", errors="replace") as fh:
                out[name[:-2]] = (f"{d}/{name}", sum(1 for _ in fh))
    return out


def reverse_graph(files):
    """module -> set of modules that Require it directly"""
    rdeps = defaultdict(set)
    for mod, (rel, _) in files.items():
        with open(os.path.join(ROOT, rel), encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        for match in REQUIRE.finditer(text):
            for token in match.group(1).replace("\n", " ").split():
                dep = token.split(".")[-1]
                if dep in files and dep != mod:
                    rdeps[dep].add(mod)
    return rdeps


def blast(mod, rdeps):
    """Transitive dependents + 1 (self), so a leaf scores 1."""
    seen, stack = set(), list(rdeps[mod])
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(rdeps[cur] - seen)
    return len(seen) + 1


def main():
    files = load()
    rdeps = reverse_graph(files)
    rows = []
    for mod, (rel, lines) in files.items():
        b = blast(mod, rdeps)
        rows.append((b * lines, rel, lines, b))
    rows.sort(reverse=True)

    if "--all" in sys.argv:
        print(f"{'metric':>9} {'lines':>6} {'blast':>6}  file")
        for metric, rel, lines, b in rows:
            print(f"{metric:>9} {lines:>6} {b:>6}  {rel}")
        return 0

    monoliths = [r for r in rows if r[2] >= MONOLITH_LINES]
    queue = [r for r in monoliths if r[0] >= GATE]
    exempt = [r for r in monoliths if r[0] < GATE]

    print(f"modules={len(files)}  monolith>={MONOLITH_LINES}L  gate>={GATE}")
    print(f"\nSPLIT QUEUE ({len(queue)}) — highest blast-weighted size first:")
    for metric, rel, lines, b in queue:
        print(f"  {metric:>8}  {lines:>5}L x{b:<4} {rel}")
    print(f"\nMONOLITHS BELOW THE GATE ({len(exempt)}) — large but not load-bearing:")
    for metric, rel, lines, b in exempt:
        print(f"  {metric:>8}  {lines:>5}L x{b:<4} {rel}  ({GATE - metric} short)")

    watch = [r for r in rows if 800 <= r[2] < MONOLITH_LINES]
    print(f"\nWATCH (800..{MONOLITH_LINES - 1} lines, {len(watch)}) — not gated, drift candidates:")
    for metric, rel, lines, b in sorted(watch, key=lambda r: -r[2]):
        print(f"  {lines:>5}L x{b:<4} {rel}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
