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
