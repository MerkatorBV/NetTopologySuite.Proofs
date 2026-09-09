#!/usr/bin/env python3
"""ADR status <-> prose consistency check.

An ADR's status lives in one place: the `| **Status** |` row of its own file
under `docs/adr/`.  Prose elsewhere repeats it, and the repeats rot.  When
ADR-0007 was accepted on 2026-09-07 a commit titled "finish Proposed ->
Accepted wording sweep" left eight places still calling it Proposed --
including `CONTEXT.md`, `docs/verified-claims.md`, ADR-0006's own decision
section, and a header comment in `theories/Adr0007NodingEpic.v`.  A reader
could pick either answer depending on which file they opened.

This script reads each ADR's declared status and fails on any prose
elsewhere that asserts a different one.

WHAT COUNTS AS AN ASSERTION.  Only phrasings that state a status, so that
ordinary discussion of an ADR is untouched:

    ADR-0007 stays Proposed              <- same line names the ADR
    ADR-0007 is **Accepted**
    ADR-0007 remains Proposed
    (ADR-0007, Proposed)                 <- parenthetical tag
    ## ADR-0007 - ... (Proposed)         <- heading tag
    Status stays Proposed                <- inherits the nearest heading
                                            above it that names an ADR

Deliberately NOT assertions: the `Status lifecycle: Proposed -> Accepted`
line every ADR carries, and authorship phrasings like "proposed by Jeroen"
(lowercase `proposed` is never a status here).

Exit 0 = every status assertion matches its ADR.  Exit 1 = at least one
disagrees.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ADR_DIR = os.path.join(ROOT, "docs", "adr")
SCAN_EXT = (".md", ".txt", ".v")
SKIP_DIRS = {".git", "node_modules", "_build", ".vo", "dashboard"}

STATUSES = ("Proposed", "Accepted", "Rejected", "Superseded")

ADR_IN_NAME = re.compile(r"ADR-(\d{4})")
STATUS_ROW = re.compile(r"^\|\s*\*\*Status\*\*\s*\|\s*(.*?)\s*\|\s*$")

# "ADR-0007 stays Proposed" / "ADR-0007 is **Accepted**"
SAME_LINE = re.compile(
    r"ADR-(\d{4})\b[^.\n]{0,60}?\b(?:stays|is|remains)\s+\**(%s)\**"
    % "|".join(STATUSES))
# "(ADR-0007, Proposed)"
PAREN_TAG = re.compile(r"\(ADR-(\d{4}),\s*\**(%s)\**" % "|".join(STATUSES))
# a bare status assertion, which inherits the nearest ADR-naming heading
BARE = re.compile(r"\b(?:Status|status)\s+(?:stays|is|remains)\s+\**(%s)\**"
                  % "|".join(STATUSES))
# "## ADR-0007 - sheet / hen / cook ... (Proposed)"
HEADING_TAG = re.compile(r"\((%s)\)" % "|".join(STATUSES))
HEADING = re.compile(r"^#+\s+(.*)$")

# Lines that mention a status without asserting one.
BENIGN = re.compile(r"Status lifecycle|proposed by|Superseded by")


def declared_statuses():
    out = {}
    if not os.path.isdir(ADR_DIR):
        return out
    for fn in sorted(os.listdir(ADR_DIR)):
        m = ADR_IN_NAME.match(fn)
        if not fn.endswith(".md") or not m:
            continue
        path = os.path.join(ADR_DIR, fn)
        with open(path, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                row = STATUS_ROW.match(line)
                if not row:
                    continue
                for st in STATUSES:
                    if st in row.group(1):
                        out[m.group(1)] = st
                        break
                break
    return out


def scan_files():
    for base, dirs, files in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for fn in sorted(files):
            if fn.endswith(SCAN_EXT):
                yield os.path.relpath(os.path.join(base, fn), ROOT)


def main():
    declared = declared_statuses()
    if not declared:
        print("[adr-status] no ADR status rows found under docs/adr/")
        return 1

    failures = []
    for rel in scan_files():
        own = ADR_IN_NAME.search(os.path.basename(rel))
        own_adr = own.group(1) if rel.startswith(os.path.join("docs", "adr")) \
            and own else None
        with open(os.path.join(ROOT, rel), encoding="utf-8",
                  errors="replace") as fh:
            lines = fh.readlines()

        heading_adr = None
        for i, line in enumerate(lines, 1):
            h = HEADING.match(line)
            if h:
                hm = ADR_IN_NAME.search(h.group(1))
                heading_adr = hm.group(1) if hm else None

            if BENIGN.search(line):
                continue

            # A heading may tag its status as a bare `(Accepted)`; every line,
            # heading or not, may name the ADR and its status together.
            claims = [(m.group(1), m.group(2)) for m in SAME_LINE.finditer(line)]
            claims += [(m.group(1), m.group(2)) for m in PAREN_TAG.finditer(line)]
            if h and heading_adr and not claims:
                tag = HEADING_TAG.search(h.group(1))
                if tag:
                    claims.append((heading_adr, tag.group(1)))
            if not claims:
                for m in BARE.finditer(line):
                    target = heading_adr or own_adr
                    if target:
                        claims.append((target, m.group(1)))

            for adr, said in claims:
                want = declared.get(adr)
                if want and said != want:
                    failures.append((rel, i, adr, said, want, line.strip()))

    if failures:
        print("[adr-status] FAIL: prose disagrees with the ADR's own Status row.")
        for rel, ln, adr, said, want, text in failures:
            print("  %s:%d  ADR-%s is %s, prose says %s"
                  % (rel, ln, adr, want, said))
            print("      %s" % (text[:120] + ("..." if len(text) > 120 else "")))
        print("")
        print("The Status row in docs/adr/ADR-<n>-*.md is the single source of")
        print("truth.  Update the prose, or change the ADR if the status really")
        print("moved.")
        return 1

    print("[adr-status] OK: %d ADR(s), prose agrees with every Status row."
          % len(declared))
    return 0


if __name__ == "__main__":
    sys.exit(main())
