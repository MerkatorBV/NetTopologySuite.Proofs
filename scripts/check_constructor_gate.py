#!/usr/bin/env python3
"""Constructor gate (ADR-0007).

Mutation testing answers "does this sentence weigh anything".  It cannot
answer "is this sentence about the input we accepted", because an ABSENT
constructor is not a mutation of any existing term: mutate `fully_intersected`
in `fully_intersected G -> snap_ok G` and the proof breaks, so a mutation
checker reports the hypothesis as load-bearing.  It is.  That is the problem.
The weight sits on a premise that says "the cook already ran".

This gate is the other half.  A headline that talks about arrangements --
overlay, snapping, faces, noding, relate -- must PRODUCE nodedness in its
conclusion, not consume it as a hypothesis.  Anything that consumes it is
filed as a lemma-under-constructor: still true, still Qed, but it does not
count towards a claim about the geometry a caller handed in.

The gate does not break the build on existing debt.  It freezes it:
docs/lemmas-under-constructor.txt is the checked-in inventory, and this script
fails when reality diverges from it -- a new lemma-under-constructor that is
not listed, or a listed one that has since been discharged.

Exit 0 = registry matches the tree.  Exit 1 = registry is stale.
"""

import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REGISTRY = os.path.join(ROOT, "docs", "lemmas-under-constructor.txt")
LANES = ("theories", "theories-flocq")

DECL = re.compile(r"^\s*(Theorem|Lemma|Corollary|Proposition)\s+([A-Za-z0-9_']+)\s*:")

# A statement is arrangement-facing when it or its name mentions one of these.
ARRANGEMENT = (
    "fully_intersected", "pairwise_nodable", "noded",
    "overlay", "snap_round", "snap_ok",
    "extract_faces", "face_", "arrangement",
)

# Predicates that assert "the arrangement is already noded".
NODEDNESS = ("fully_intersected", "pairwise_nodable")


def statements(path):
    """Yield (name, statement_text) for each top-level declaration."""
    with open(path, encoding="utf-8", errors="replace") as fh:
        lines = fh.readlines()
    i = 0
    while i < len(lines):
        m = DECL.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group(2)
        body = [lines[i].split(":", 1)[1]]
        depth = body[0].count("(") - body[0].count(")")
        j = i + 1
        while j < len(lines):
            if depth <= 0 and re.search(r"\.\s*$", body[-1]) and body[-1].strip():
                break
            body.append(lines[j])
            depth += lines[j].count("(") - lines[j].count(")")
            if depth <= 0 and re.search(r"\.\s*$", lines[j].rstrip()):
                j += 1
                break
            j += 1
        yield name, " ".join(x.strip() for x in body)
        i = max(j, i + 1)


def strip_comments(text):
    out, depth, k = [], 0, 0
    while k < len(text):
        if text.startswith("(*", k):
            depth += 1
            k += 2
        elif text.startswith("*)", k) and depth:
            depth -= 1
            k += 2
        else:
            if not depth:
                out.append(text[k])
            k += 1
    return "".join(out)


def conclusion_of(stmt):
    """Text after the last top-level `->`."""
    depth, last = 0, 0
    k = 0
    while k < len(stmt) - 1:
        c = stmt[k]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif depth == 0 and stmt[k:k + 2] == "->":
            last = k + 2
            k += 1
        k += 1
    return stmt[last:]


def classify():
    found = []
    for lane in LANES:
        base = os.path.join(ROOT, lane)
        if not os.path.isdir(base):
            continue
        for fn in sorted(os.listdir(base)):
            if not fn.endswith(".v"):
                continue
            rel = "%s/%s" % (lane, fn)
            for name, raw in statements(os.path.join(base, fn)):
                stmt = strip_comments(raw)
                hay = (name + " " + stmt).lower()
                if not any(w in hay for w in ARRANGEMENT):
                    continue
                concl = conclusion_of(stmt)
                hyps = stmt.replace(concl, "", 1)
                # Consuming nodedness as a hypothesis is disqualifying on its
                # own.  Concluding it as well does NOT excuse it: Hobby 4.1 is
                # exactly `fully_intersected G -> fully_intersected (snap G)`,
                # the archetype of a theorem whose input nodedness was assumed.
                if any(w in hyps for w in NODEDNESS):
                    found.append("%s :: %s" % (rel, name))
    return sorted(set(found))


def read_registry():
    if not os.path.exists(REGISTRY):
        return None
    entries = []
    with open(REGISTRY, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line and not line.startswith("#"):
                entries.append(line)
    return sorted(set(entries))


def main():
    found = classify()
    listed = read_registry()

    if listed is None:
        print("[constructor-gate] registry missing: docs/lemmas-under-constructor.txt")
        for e in found:
            print("  " + e)
        return 1

    new = [e for e in found if e not in listed]
    gone = [e for e in listed if e not in found]

    if not new and not gone:
        print("[constructor-gate] %d lemma(s) under constructor; registry matches."
              % len(found))
        return 0

    for e in new:
        print("[constructor-gate] NEW lemma under constructor, not in registry:")
        print("  " + e)
    for e in gone:
        print("[constructor-gate] registry lists a lemma that no longer consumes")
        print("  nodedness as a hypothesis (discharged? renamed?):")
        print("  " + e)
    print("")
    print("A lemma under constructor consumes `fully_intersected` or")
    print("`pairwise_nodable` as a HYPOTHESIS.  Under ADR-0007 that premise is")
    print("the statement that the cook already ran, so the lemma is not about")
    print("the input the library accepted.  Either produce nodedness in the")
    print("conclusion (see theories/ChordCook.v for the first rung), or add the")
    print("entry to docs/lemmas-under-constructor.txt with a justification.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
