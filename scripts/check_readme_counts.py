#!/usr/bin/env python3
"""README / Reading-Guide <-> _CoqProject module-count consistency check.

The README and the Reading Guide both quote how many modules each lane
builds.  Nothing kept those numbers honest, and they rotted: the README
claimed 47 host modules and 520 registered ones while `_CoqProject` listed
51 and `_CoqProject.full` listed 567.  A reader checking the corpus against
its own front page found two wrong numbers before reaching a theorem.

This script recomputes the counts from the build inputs and fails when the
prose disagrees.  It reads counts, never writes them: the fix for a failure
is to correct the sentence, which is the sentence a human is claiming.

Anchors, matched case-sensitively anywhere in the checked documents.
Any run of whitespace matches, so a claim may wrap across lines:

    <N> modules in `_CoqProject`      -> module lines in _CoqProject
    <N> registered modules            -> module lines in _CoqProject.full
    <N> registered under `theories/`       -> that lane in _CoqProject.full
    <N> registered under `theories-flocq/` -> that lane in _CoqProject.full

Every occurrence must match, and README.md must carry at least one of each.

One claim is checked as a bound rather than an equality:

    over <N> Qed-closed theorems      -> must not exceed the real Qed count

`over N` is honest while N is below the truth, so this only fails on an
overstatement.

Exit 0 = prose matches the build inputs.  Exit 1 = it does not.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DOCS = ["README.md", os.path.join("docs", "READING-GUIDE.md")]
REQUIRED_IN = "README.md"

MODULE_LINE = re.compile(r"(\S+\.v)\s*$")


def module_lines(coqproject, lane_prefix=None):
    """Count `.v` module lines in a _CoqProject file, ignoring comments."""
    path = os.path.join(ROOT, coqproject)
    n = 0
    with open(path, encoding="utf-8", errors="replace") as fh:
        for raw in fh:
            line = raw.split("#", 1)[0].strip()
            m = MODULE_LINE.search(line)
            if not m:
                continue
            if lane_prefix and not m.group(1).startswith(lane_prefix):
                continue
            n += 1
    return n


def qed_count():
    n = 0
    for lane in ("theories", "theories-flocq"):
        base = os.path.join(ROOT, lane)
        if not os.path.isdir(base):
            continue
        for fn in sorted(os.listdir(base)):
            if not fn.endswith(".v"):
                continue
            with open(os.path.join(base, fn), encoding="utf-8",
                      errors="replace") as fh:
                for line in fh:
                    if line.strip() == "Qed.":
                        n += 1
    return n


def as_int(text):
    return int(text.replace(",", ""))


def main():
    checks = [
        ("host modules",
         re.compile(r"([0-9][0-9,]*)\s+modules\s+in\s+`_CoqProject`"),
         module_lines("_CoqProject"),
         "eq"),
        ("registered modules",
         re.compile(r"([0-9][0-9,]*)\s+registered\s+modules"),
         module_lines("_CoqProject.full"),
         "eq"),
        ("theories/ modules",
         re.compile(r"([0-9][0-9,]*)\s+registered\s+under\s+`theories/`"),
         module_lines("_CoqProject.full", "theories/"),
         "eq"),
        ("theories-flocq/ modules",
         re.compile(r"([0-9][0-9,]*)\s+registered\s+under\s+`theories-flocq/`"),
         module_lines("_CoqProject.full", "theories-flocq/"),
         "eq"),
        ("Qed-closed theorems",
         re.compile(r"over\s+([0-9][0-9,]*)\s+Qed-closed\s+theorems"),
         qed_count(),
         "le"),
    ]

    text = {}
    for rel in DOCS:
        path = os.path.join(ROOT, rel)
        if not os.path.exists(path):
            print("[readme-counts] cannot read %s" % rel)
            return 1
        with open(path, encoding="utf-8", errors="replace") as fh:
            text[rel] = fh.read()

    failures = []
    for label, pattern, actual, mode in checks:
        seen_in_readme = False
        for rel in DOCS:
            for m in pattern.finditer(text[rel]):
                claimed = as_int(m.group(1))
                if rel == REQUIRED_IN:
                    seen_in_readme = True
                if mode == "eq" and claimed != actual:
                    failures.append(
                        "%s: %s claims %d, build inputs say %d"
                        % (rel, label, claimed, actual))
                elif mode == "le" and claimed > actual:
                    failures.append(
                        "%s: %s claims over %d, but only %d exist"
                        % (rel, label, claimed, actual))
        if mode == "eq" and not seen_in_readme:
            failures.append(
                "%s: no '%s' claim found; the anchor phrase was edited away"
                % (REQUIRED_IN, label))

    if failures:
        print("[readme-counts] FAIL")
        for f in failures:
            print("  " + f)
        print("")
        print("Recompute from the build inputs and correct the prose:")
        print("  host modules            = %d" % module_lines("_CoqProject"))
        print("  registered modules      = %d" % module_lines("_CoqProject.full"))
        print("  under theories/         = %d"
              % module_lines("_CoqProject.full", "theories/"))
        print("  under theories-flocq/   = %d"
              % module_lines("_CoqProject.full", "theories-flocq/"))
        print("  Qed-closed theorems     = %d" % qed_count())
        return 1

    print("[readme-counts] OK: README and Reading Guide agree with "
          "_CoqProject / _CoqProject.full.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
