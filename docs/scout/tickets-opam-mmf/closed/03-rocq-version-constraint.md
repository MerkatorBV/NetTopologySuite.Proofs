# Decide the Rocq version constraint

**Type:** grilling · **Map:** [An MMF release bar for the opam packages](../map-opam-mmf-release-bar.md)
**Blocked by:** nothing — takeable

## Question

Both packages declare `rocq-core {>= "9.0"}` (and `spatial-algebra` also
`rocq-stdlib {>= "9.0"}`), while CI builds only the repo's pinned **9.2.0**. The
lower bound is an untested claim, and this map's whole posture is that untested
claims do not ship.

This question was raised while charting and left unanswered, so it is a real
open decision, not a formality.

Decide between:

1. **Tighten to what is tested** — declare `>= 9.2` and widen later if someone
   asks. Cheapest, honest immediately, and reversible in the easy direction.
   Costs reach: a user on 9.0 or 9.1 is locked out of a package that might well
   build for them.
2. **Test the lower bound** — add a 9.0 job to CI so the declared constraint is
   earned. Costs a build matrix and pins a second toolchain image, and someone
   has to keep it green.
3. **Constrain per package.** `spatial-algebra` is two Stdlib-only files with
   zero axioms and plausibly builds on anything ≥ 9.0; `robust-predicates` is 21
   files on Flocq and much likelier to be version-sensitive. The honest bounds
   may genuinely differ, in which case one bar line reads differently per
   package — which the map already allows.

Also settle:

- **The `coq-flocq {>= "4.2.0"}` bound**, which has the same problem: the repo
  pins 4.2.2 and the archive carries 4.1.4 through 4.2.2. Same question, same
  three options.
- **Whether the bar states a tested-versions line at all**, distinct from the
  dependency constraint. "Built and tested on X" is a different claim from
  "requires ≥ Y", and a consumer wants both.

---

## Resolution

**Match `rocq-bignums`, not `coq-fourcolor`.** Instruction was to match fourcolor;
looking at it produced a better comparator and a third answer, so the reasoning
is recorded rather than the instruction followed blindly.

`coq-fourcolor.1.4.3` declares **no core constraint at all**:

```
depends: [
  "coq-mathcomp-algebra"
  "coq-fourcolor-reals" {= version}
]
```

It can afford that because `coq-mathcomp-algebra` carries the core bound
transitively. **Our packages have no such intermediary** — `spatial-algebra`
depends only on `rocq-core` and `rocq-stdlib` — so copying fourcolor's looseness
would leave it genuinely unconstrained. fourcolor is also a legacy `coq-*` name
whose last release was 2025-04, so it is not a current-convention exemplar.

`rocq-bignums.9.0.0+rocq9.2` is our shape exactly — a small library depending
directly on the core:

```
depends: [
  "ocaml"
  "rocq-core" {>= "9.2" & < "9.4~"}
  "rocq-stdlib"
]
```

Adopted, five parts:

1. **Bounded interval on the core, matching what CI tests:**
   `rocq-core {>= "9.2" & < "9.4~"}`. This replaces the untested open
   `>= "9.0"`. Note it answers the ticket's option 1 (tighten) but adds an
   **upper** bound, which neither charted option proposed — an unbounded upper
   is its own untested claim.
2. **Leave `rocq-stdlib` unconstrained**, as bignums does; the core pins it.
   Two bounds where one suffices is two things to keep true.
3. **Multi-version support is separate published versions, not a wider
   constraint.** bignums ships `9.0.0+rocq9.0`, `+rocq9.1`, `+rocq9.2` — same
   source, one opam version per Rocq version, each tightly bounded. So if 9.0 or
   9.1 support is ever wanted it arrives as additional tested versions. We never
   declare a bound we have not built. This retires the ticket's option 2 (add a
   9.0 CI job to earn a wide bound) as the wrong shape for this archive.
4. **`coq-flocq` keeps its `coq-` name** — `rocq-flocq` does not exist in the
   archive (4.1.4 through 4.2.2, all `coq-flocq`). A `rocq-robust-predicates`
   depending on `coq-flocq` is normal and unavoidable. Tighten to
   `{>= "4.2.2" & < "4.3~"}`: the corpus pins 4.2.2, so anything looser is
   untested.
5. **A tested-on marker distinct from the constraint.** fourcolor carries a
   `date:2025-04-16` tag; adopt the same idiom so a consumer can see *when* the
   claim was earned, not only which versions it permits. This settles the
   ticket's third sub-question: the bar states both, and they are different
   claims.

Option 3 of the ticket (per-package constraints) is **not** needed: both packages
land on the same core interval. Their dependency lines still differ, because only
`robust-predicates` needs Flocq — a difference in dependencies, not in policy.

### Carried to other tickets

- **Ticket 01** gains hard evidence: the released archive holds **6424** packages,
  **1111** `rocq-*` against **5302** `coq-*`. So `rocq-*` is the convention for
  new and maintained packages — `rocq-core`, `rocq-stdlib` and `rocq-bignums` are
  all `rocq-`-named — while the `coq-*` majority is largely legacy. The rename is
  well-supported, not merely tolerated.
- **Ticket 01** also gains a version idiom: `+rocqX.Y` suffixes mean a renamed
  package could take `0.1.4+rocq9.2` as its first upstream version, which
  sidesteps the reset-or-continue question by making the Rocq version part of the
  label.
- **Ticket 06** inherits three bar lines: the declared interval equals the tested
  interval; the tested-on date is published; and a new Rocq release is handled by
  publishing a version, never by widening a bound.
