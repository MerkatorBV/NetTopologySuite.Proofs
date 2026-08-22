#!/usr/bin/env python3
"""Compute the module-split gate metric: transitive_dependents+1 times lines."""
import os
import re
import sys
from collections import defaultdict

ROOT = r"C:\com\github\grootstebozewolf\NetTopologySuite.Proofs"
DIRS = ["theories", "theories-flocq", "eval"]
THRESHOLD = 3210

files = {}          # module basename -> (relpath, lines)
for d in DIRS:
    base = os.path.join(ROOT, d)
    if not os.path.isdir(base):
        continue
    for name in os.listdir(base):
        if not name.endswith(".v"):
            continue
        path = os.path.join(base, name)
        with open(path, "r", encoding="utf-8", errors="replace") as fh:
            n = sum(1 for _ in fh)
        files[name[:-2]] = (f"{d}/{name}", n)

# direct deps: module -> set(modules it Requires)
req_re = re.compile(r"^\s*(?:From\s+\S+\s+)?Require\s+(?:Import|Export)?\s*([^.]*)\.", re.M)
deps = defaultdict(set)
for mod, (rel, _) in files.items():
    with open(os.path.join(ROOT, rel), "r", encoding="utf-8", errors="replace") as fh:
        text = fh.read()
    for match in req_re.finditer(text):
        for token in match.group(1).replace("\n", " ").split():
            name = token.split(".")[-1]
            if name in files and name != mod:
                deps[mod].add(name)

# reverse graph, then transitive dependents per module
rdeps = defaultdict(set)
for mod, ds in deps.items():
    for d in ds:
        rdeps[d].add(mod)

def transitive_dependents(mod):
    seen, stack = set(), list(rdeps[mod])
    while stack:
        cur = stack.pop()
        if cur in seen:
            continue
        seen.add(cur)
        stack.extend(rdeps[cur] - seen)
    return seen

rows = []
for mod, (rel, lines) in files.items():
    blast = len(transitive_dependents(mod)) + 1
    rows.append((blast * lines, rel, lines, blast))
rows.sort(reverse=True)

gated = [r for r in rows if r[0] >= THRESHOLD]
print(f"modules={len(files)}  threshold={THRESHOLD}  gated={len(gated)}")
print(f"{'metric':>9} {'lines':>6} {'blast':>6}  file")
for metric, rel, lines, blast in gated[:40]:
    print(f"{metric:>9} {lines:>6} {blast:>6}  {rel}")

small = [r for r in gated if r[2] < 800]
print(f"\ngated but under 800 lines: {len(small)}")
for metric, rel, lines, blast in small[:15]:
    print(f"{metric:>9} {lines:>6} {blast:>6}  {rel}")

tiny = [r for r in gated if r[2] < 300]
print(f"\ngated but under 300 lines: {len(tiny)}")
for metric, rel, lines, blast in tiny[:10]:
    print(f"{metric:>9} {lines:>6} {blast:>6}  {rel}")
