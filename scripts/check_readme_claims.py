#!/usr/bin/env python3
"""Front-page claim and self-URL guard.

`scripts/check_readme_counts.py` keeps the README's *numbers* honest.  It
does not keep its *sentences* honest, and that gap has already cost us once.

On 2026-09-07 commit c4d850e ("Port overlay-under-G + span-gamma stack (fork
#676-#682)") copied the fork's README over this one.  The counts guard caught
the stale numbers and two follow-up commits fixed them.  Nothing caught the
rest of the port, so `main` silently went back to:

  * badge and dashboard URLs pointing at `grootstebozewolf/`, undoing the
    organisation migration to MerkatorBV;
  * "The corpus introduces exactly three axioms of its own", which
    contradicts the next clause calling them Rocq's own trio;
  * "the three above are a floor on what a given module rests on, not a
    ceiling", which is false -- `Distance.dist_sq_nonneg` rests on two.

This script guards the sentences.  Two kinds of rule:

  FORBIDDEN  a phrase that is wrong wherever it appears.
  REQUIRED   a phrase the front page must keep, so that deleting the
             correction is a failure rather than a silent regression.

SELF-URLS.  Links to this repository must use the MerkatorBV org.  Links to
`grootstebozewolf/NetTopologySuite.Proofs` are allowed only for `/issues/`
and `/pull/` paths, because the issue tracker did not migrate -- MerkatorBV
returns 404 on issue numbers that resolve under grootstebozewolf.  Other
`grootstebozewolf/*` repositories (`jts`, `GEOS`, `clothoid-halley-coq`,
`NetTopologySuite`, `NetTopologySuite.Curve`) are separate projects and are
not touched.

Exit 0 = every rule holds.  Exit 1 = at least one does not.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# --- claim rules, per file ------------------------------------------------

FORBIDDEN = [
    ("README.md",
     re.compile(r"a floor on what a given module rests on"),
     "the three-axiom allowlist is a CEILING, not a floor: "
     "Distance.dist_sq_nonneg rests on two of the three"),
    ("README.md",
     re.compile(r"introduces exactly three axioms of its own"),
     "the corpus declares none of the three; they ship with Rocq's Stdlib"),
    ("README.md",
     re.compile(r"corpus-introduced\*? axiom set"),
     "same claim: the axioms are Stdlib's, not the corpus's"),
]

REQUIRED = [
    ("README.md",
     re.compile(r"is a \*\*ceiling\*\*, not a floor"),
     "the corrected axiom claim"),
    ("README.md",
     re.compile(r"none of them closes a theorem"),
     "the note that every `Defined.` closes a Definition, not a theorem"),
    ("README.md",
     re.compile(r"docs/audit-exceptions\.txt"),
     "the pointer to the named axiom exceptions"),
]

# --- self-URL rules ------------------------------------------------------

FORK_SELF = re.compile(
    r"grootstebozewolf(?:\.github\.io/NetTopologySuite\.Proofs"
    r"|/NetTopologySuite\.Proofs(?P<path>/[^\s)\]]*)?)")

SCAN_EXT = (".md", ".txt", ".yml", ".yaml", ".json")
SKIP_DIRS = {".git", "node_modules", "_build", ".ci-artifacts"}

# Files where a fork self-reference is the subject, not a link to follow.
URL_EXEMPT = {
    os.path.join("docs", "agents", "issue-tracker.md"),   # tracker did not move
    os.path.join("docs", "geos-oracle-rung-2026-08.md"),  # local clone path
    os.path.join("scripts", "check_readme_claims.py"),
}


def read(rel):
    with open(os.path.join(ROOT, rel), encoding="utf-8", errors="replace") as fh:
        return fh.read()


def scan_files():
    for base, dirs, files in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for fn in sorted(files):
            if fn.endswith(SCAN_EXT):
                yield os.path.relpath(os.path.join(base, fn), ROOT)


def main():
    failures = []

    for rel, pattern, why in FORBIDDEN:
        if not os.path.exists(os.path.join(ROOT, rel)):
            failures.append("%s: file missing" % rel)
            continue
        for i, line in enumerate(read(rel).splitlines(), 1):
            if pattern.search(line):
                failures.append("%s:%d forbidden claim -- %s\n      %s"
                                 % (rel, i, why, line.strip()[:110]))

    for rel, pattern, what in REQUIRED:
        if not pattern.search(read(rel)):
            failures.append("%s: required claim is gone -- %s" % (rel, what))

    for rel in scan_files():
        if rel.replace("/", os.sep) in URL_EXEMPT:
            continue
        for i, line in enumerate(read(rel).splitlines(), 1):
            for m in FORK_SELF.finditer(line):
                path = m.group("path") or ""
                if path.startswith("/issues/") or path.startswith("/pull/"):
                    continue
                failures.append(
                    "%s:%d self-URL still on the fork org -- use MerkatorBV\n"
                    "      %s" % (rel, i, line.strip()[:110]))

    if failures:
        print("[readme-claims] FAIL")
        for f in failures:
            print("  " + f)
        print("")
        print("These are claims and links about this corpus, not numbers.")
        print("If a port reintroduced them, take the correction, not the port.")
        return 1

    print("[readme-claims] OK: %d forbidden, %d required, self-URLs clean."
          % (len(FORBIDDEN), len(REQUIRED)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
