# Collect the community verdict on the `rocq-*` rename

**Type:** task · **Map:** [An MMF release bar for the opam packages](../map-opam-mmf-release-bar.md)
**Blocked by:** nothing — takeable

## Question

The rename question is already out with the community. This ticket collects the
verdict and records what follows from it. Nothing here is a fresh decision: the
map settled *rename if nobody objects*.

Find the thread and read it. The likely venue is the Rocq Zulip — the
`#Rocq community devs & users` channel, topic **"Project showcase:
NetTopologySuite.Proofs (JTS/NTS companion)"** — which is also the subject of a
standing request to set up monitoring; that monitor does not exist yet and
reading the thread needs a Zulip credential, so this ticket may have to be
resolved by hand.

Record three things:

1. **The verdict.** Objection, no objection, or no response after a stated
   waiting period. "No response" is a real outcome and needs its own rule — decide
   how long silence counts as consent, and say so.
2. **The resulting names.** Either `rocq-spatial-algebra` /
   `rocq-robust-predicates`, or the `coq-*` names retained. Note that the
   packaging *directories* are already `packaging/rocq-*` while the opam files are
   `coq-*.opam`, so one of the two is wrong either way and the inconsistency gets
   fixed by this ticket's answer.
3. **What happens to the version numbers.** An opam rename is a **new package**,
   not a version bump — a renamed package has no 0.1.3 to succeed. So if the
   rename lands, decide whether the first upstream version is `0.1.4` /
   `0.1.3` (continuing the GitHub-release lineage) or resets. This is the part
   that decides whether "mint 0.1.4" is even the right label, so it is the
   answer the rest of the map waits on.

Also worth capturing while in the thread: any archive-convention guidance for a
Rocq 9 library that bears on the bar — required metadata fields, naming rules,
or `logpath` expectations.
