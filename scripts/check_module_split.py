#!/usr/bin/env python3
# =============================================================================
# scripts/check_module_split.py
# -----------------------------------------------------------------------------
# Meso-scale size guard (see docs/macro-meso-micro.md "Module split gate").
#
# A module must be split when BOTH hold:
#   1. monolith:      lines >= MONOLITH_LINES (1234)
#   2. load-bearing:  (transitive dependents + 1) * lines >= GATE (3210)
#
# The line floor is load-bearing, not decoration: the blast-weighted product
# alone selects *foundational* modules rather than *giant* ones -- e.g.
# theories/Distance.v is 402 lines with 455 transitive dependents (product
# 182910) and has no size problem whatsoever.
#
# This is a RATCHET. Modules already over the gate are listed in
# docs/module-split-allowlist.txt with their line count at time of record; the
# list may shrink, never grow. Two rules follow:
#
#   * The allowlist records LINES, not the metric. Blast radius rises whenever
#     some *other* module starts requiring yours, so gating a listed module on
#     its metric would fail your build for an edit you did not make.
#   * A listed module that no longer trips the gate is a FAILURE: the split
#     landed, so the entry is stale and must be deleted in the same change.
#     That is what keeps the ratchet honest.
#
# Splits use the established umbrella pattern -- the original name stays as a
# `Require Export` umbrella, the declaration set is byte-identical, and
# `Print Assumptions` footers move verbatim to each declaration's new home.
# High fan-in is therefore not a reason to refuse a split: importers cannot
# observe one.
#
# Usage:
#   python3 scripts/check_module_split.py           # guard (CI)
#   python3 scripts/check_module_split.py --list     # queue + watch band
#   python3 scripts/check_module_split.py --all      # full metric table
#
# Exit codes:
#   0 -- gate holds (every gated module is listed and within headroom).
#   1 -- a new violation, a listed module grown past headroom, or a stale entry.
#   2 -- usage / file-access error.
# =============================================================================
import math
import os
import re
import sys
from collections import defaultdict

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE_DIRS = ["theories", "theories-flocq"]
ALLOWLIST = os.path.join(REPO_ROOT, "docs", "module-split-allowlist.txt")

MONOLITH_LINES = 1234
GATE = 3210
HEADROOM_FRACTION = 0.05  # 5% of the recorded line count, rounded up
WATCH_FLOOR = 800         # reported, never enforced

REQUIRE = re.compile(
    r"^\s*(?:From\s+\S+\s+)?Require\s+(?:Import|Export)?\s*([^.]*)\.", re.M
)


def load_modules():
    """module basename -> (repo-relative path, line count)"""
    modules = {}
    for directory in SOURCE_DIRS:
        base = os.path.join(REPO_ROOT, directory)
        if not os.path.isdir(base):
            continue
        for name in sorted(os.listdir(base)):
            if not name.endswith(".v"):
                continue
            path = os.path.join(base, name)
            with open(path, encoding="utf-8", errors="replace") as handle:
                lines = sum(1 for _ in handle)
            modules[name[:-2]] = (f"{directory}/{name}", lines)
    return modules


def direct_dependents(modules):
    """module -> set of modules that Require it directly"""
    rdeps = defaultdict(set)
    for module, (rel, _) in modules.items():
        with open(os.path.join(REPO_ROOT, rel), encoding="utf-8", errors="replace") as handle:
            text = handle.read()
        for match in REQUIRE.finditer(text):
            for token in match.group(1).replace("\n", " ").split():
                dep = token.split(".")[-1]
                if dep in modules and dep != module:
                    rdeps[dep].add(module)
    return rdeps


def blast_radius(module, rdeps):
    """Transitive dependents + 1 (self), so a leaf scores 1."""
    seen, stack = set(), list(rdeps[module])
    while stack:
        current = stack.pop()
        if current in seen:
            continue
        seen.add(current)
        stack.extend(rdeps[current] - seen)
    return len(seen) + 1


def metrics():
    modules = load_modules()
    rdeps = direct_dependents(modules)
    rows = []
    for module, (rel, lines) in modules.items():
        blast = blast_radius(module, rdeps)
        rows.append(
            {"path": rel, "lines": lines, "blast": blast, "metric": blast * lines}
        )
    rows.sort(key=lambda r: -r["metric"])
    return rows


def is_gated(row):
    return row["lines"] >= MONOLITH_LINES and row["metric"] >= GATE


def read_allowlist():
    """repo-relative path -> recorded line count"""
    if not os.access(ALLOWLIST, os.R_OK):
        print(f"[check_module_split] cannot read {ALLOWLIST}", file=sys.stderr)
        sys.exit(2)
    recorded = {}
    with open(ALLOWLIST, encoding="utf-8") as handle:
        for raw in handle:
            line = raw.split("#", 1)[0].strip()
            if not line:
                continue
            parts = [p.strip() for p in line.split("|")]
            if len(parts) < 2 or not parts[1].isdigit():
                print(
                    f"[check_module_split] malformed allowlist entry: {raw.rstrip()}",
                    file=sys.stderr,
                )
                sys.exit(2)
            recorded[parts[0].replace("\\", "/")] = int(parts[1])
    return recorded


def headroom(recorded_lines):
    return math.ceil(recorded_lines * HEADROOM_FRACTION)


def report(rows, full=False):
    if full:
        print(f"{'metric':>9} {'lines':>6} {'blast':>6}  file")
        for row in rows:
            print(f"{row['metric']:>9} {row['lines']:>6} {row['blast']:>6}  {row['path']}")
        return 0

    queue = [r for r in rows if is_gated(r)]
    below = [
        r for r in rows if r["lines"] >= MONOLITH_LINES and r["metric"] < GATE
    ]
    watch = [r for r in rows if WATCH_FLOOR <= r["lines"] < MONOLITH_LINES]

    print(f"monolith >= {MONOLITH_LINES} lines · gate >= {GATE} blast-weighted")
    print(f"\nSPLIT QUEUE ({len(queue)}) — highest blast-weighted size first:")
    for row in queue:
        print(f"  {row['metric']:>8}  {row['lines']:>5}L x{row['blast']:<4} {row['path']}")
    print(f"\nMONOLITHS BELOW THE GATE ({len(below)}) — large but not load-bearing:")
    for row in below:
        print(
            f"  {row['metric']:>8}  {row['lines']:>5}L x{row['blast']:<4} {row['path']}"
            f"  ({GATE - row['metric']} short)"
        )
    print(f"\nWATCH ({WATCH_FLOOR}..{MONOLITH_LINES - 1} lines, {len(watch)}) — not gated:")
    for row in sorted(watch, key=lambda r: -r["lines"]):
        print(f"  {row['lines']:>5}L x{row['blast']:<4} {row['path']}")
    return 0


def guard(rows):
    recorded = read_allowlist()
    gated = {r["path"]: r for r in rows if is_gated(r)}
    failures = []

    for path, row in sorted(gated.items()):
        if path not in recorded:
            failures.append(
                f"NEW VIOLATION  {path}: {row['lines']} lines x{row['blast']} "
                f"= {row['metric']} >= {GATE}.\n"
                f"    Split it (umbrella re-export pattern), or shrink it below "
                f"{MONOLITH_LINES} lines. The allowlist may not grow."
            )
            continue
        limit = recorded[path] + headroom(recorded[path])
        if row["lines"] > limit:
            failures.append(
                f"GREW PAST HEADROOM  {path}: {row['lines']} lines, "
                f"recorded {recorded[path]} + {headroom(recorded[path])} headroom = {limit}."
            )

    for path in sorted(recorded):
        if path not in gated:
            failures.append(
                f"STALE ENTRY  {path} no longer trips the gate — delete its "
                f"allowlist line in the same change that split it."
            )

    if failures:
        print("[check_module_split] gate FAILED:\n")
        for failure in failures:
            print(f"  - {failure}")
        print(
            f"\n  See docs/macro-meso-micro.md (Module split gate) and "
            f"docs/module-split-allowlist.txt."
        )
        return 1

    listed = len(recorded)
    print(
        f"[check_module_split] gate holds: {len(gated)} gated module(s), "
        f"all {listed} allowlisted and within headroom."
    )
    return 0


def main(argv):
    if "--help" in argv or "-h" in argv:
        print(__doc__ or "")
        return 0
    rows = metrics()
    if "--all" in argv:
        return report(rows, full=True)
    if "--list" in argv:
        return report(rows)
    return guard(rows)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
