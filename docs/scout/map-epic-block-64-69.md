# Map — Retire the epic block #64–#69

A wayfinder map. Tickets live in [`tickets/`](tickets/) and are worked one per
session. Charted 2026-08-22.

> **Tracker exception.** `docs/agents/issue-tracker.md` puts wayfinder maps on
> GitHub. This map is local markdown instead, for one reason: its destination is
> an *emptier issue tracker*, and a map that must delete itself to succeed does
> not belong in the thing being emptied. This exception applies to this map only.

## Destination

**The early epic block — #64, #65, #66, #67, #68, #69 — reaches zero open.**
Each of the six either closes with an evidence pointer, or its live residue is
re-expressed as a subtask or a clearly-stated new epic before it closes.

Anything numbered above that block is by definition **not** legacy: #423
(metrics), #424 (hulls) and #425 (coverage) stand on their own as clearly-stated
new epics, and #482 is a subtask. #69's umbrella role ends with the block.

## Notes

**Domain.** A Rocq/Coq proof corpus for NetTopologySuite, plus the differential
tooling that gates real engines against the extracted oracle. Read
[`CONTEXT.md`](../../CONTEXT.md) and [`docs/agents/domain.md`](../agents/domain.md)
before exploring; `TRIAGE_NTS_JTS_ISSUES.md` is the declared status source of
record, and `docs/verified-claims.md` is the claims register.

**Skills every session.** `/grilling` and `/domain-modeling`. Issue operations
follow [`docs/agents/issue-tracker.md`](../agents/issue-tracker.md) (`gh` CLI).

**Standing preferences (the maintainer's, recorded as given).**

- Rocq is the foundation; **lemmas** are the building blocks; **modules** are the
  architectural seams. Keep modules small enough and the optimisation becomes
  natural.
- Optimise for **maintainability → soundness → performance**, in that order —
  *except* the laser program, where performance was deliberately gated as the
  metric that starts the chord-based vs arc-based implementation work.
- When cleaning house, start from the top: ascending through the block from #64,
  with #482 taken first as a freebie.

**This map executes, it does not only advise.** Resolving a ticket performs its
closure — `gh issue close` with the evidence comment, plus creating any residue
issues. Every act is reversible with `gh issue reopen`.

**Closure bar.** Near-horizon epics (#64/#67 Immediate, #65/#66 Urgent) get their
residue carved into subtasks or clearly-stated new epics. An epic closes when its
ask is satisfied *by the corpus* — judged against the tree, never against its own
body, which is stale everywhere (all six bodies date from 2026-07-04).

**Evidence convention for a closure comment.** Cite (1) the `docs/verified-claims.md`
row(s), (2) `file:line` pointers to the Qed'd statements, and (3) the status line
in the relevant lane doc. Name what is *not* covered and where it went.

**The module-split gate (new policy, derived not judged).** A module over
**1234 lines** whose blast-weighted size — `(transitive dependents + 1) × lines`
— reaches **3210** must be split, using the established umbrella pattern: keep
the original name as a `Require Export` umbrella, byte-identical declaration set,
`Print Assumptions` footers carried verbatim to each declaration's new home.
Enforced as a **ratchet** guard with a shrink-only allowlist carrying headroom,
alongside the existing `make ci-guards` checks. Chore cadence: one split per
session, chosen from the queue by the day's seed (e.g. `20260822`) — the same
seeded-sample convention as `docs/geos-open-issues-triage-2026-08.md`.

As computed 2026-08-22, the gate selects three modules —
`theories-flocq/Orient_b64_exact.v` (1270 × 72), `theories-flocq/HotPixel_b64.v`
(2604 × 32), `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v` (2293 × 9) —
and `theories-flocq/ArcLineIntersect_b64_exact.v` is honestly exempt at 1516
lines (product 3032, 178 short).

**Body resync comes last**, and only for issues that survive: it waits until the
split queue is empty, because a module that is about to be split will invalidate
whatever its epic's body says about it.

## Decisions so far

<!-- one line per closed ticket: gist, then zoom the link for detail -->

_None yet — charted this session; charting resolves nothing._

## Not yet specified

- **How #69's umbrella role formally ends.** Whether #423/#424/#425 need a
  replacement umbrella, a project board, or nothing at all, cannot be settled
  until the block's closures reveal what residue lands where.
- **#66's parked items.** C2 off-grid completeness and the arc Hobby analog were
  parked by decision; whether each becomes a documented non-goal or a new epic
  depends on how #66's ticket reads the parking.
- **#67's DE-9IM capstone residue.** The full 9-cell `geom_de9im_pointset` is
  deferred on a half-open ring-inclusion question; whether that is one issue or
  several is not visible from outside the ticket.
- **A standing freshness re-run.** Whether "no stale issue bodies" becomes a
  quarterly chore like the split queue, once this map has walked it once.

## Out of scope

- **The module splits themselves.** Governance is in scope (the gate, the guard,
  the queue); performing the splits is a clearly-stated new epic plus a
  maintainer chore, with its own per-module gauntlet.
- **The programs above the block** — #423 metrics, #424 hulls, #425 coverage.
  They are new epics, not legacy, and the audit found them genuinely unstarted
  (no convex-hull code exists at all; coverage is one of six asks at witness
  scope).
- **Upstream filing.** #482's counterexample is a corpus-postcondition disproof,
  not a Shewchuk-1997 refutation, so nothing is owed upstream; deciding otherwise
  is a separate effort.
- **The laser program's chord-vs-arc implementation.** Gated on performance by
  its own decision; unrelated to issue hygiene.
