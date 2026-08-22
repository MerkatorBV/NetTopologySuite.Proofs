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

- [Close #482 — Shewchuk half-ulp counterexample retip](tickets/closed/01-close-shewchuk-counterexample-subtask.md)
  — satisfied and closed with evidence; the missing claims-register row is a
  separate micro (#503), because refutations *are* citable by convention here
  (`hobby_lemma_4_3_no_proper` carries a "**Refuted:**" row) and nothing checks
  source-negative → claims.
- [Write the module-split gate: policy and ratchet guard](tickets/closed/02-module-split-gate-policy-and-guard.md)
  — policy in `docs/macro-meso-micro.md`, `scripts/check_module_split.py` in
  `make ci-guards`, three entries in `docs/module-split-allowlist.txt`; headroom
  is 5 % of recorded **lines** (not the metric, since another module's `Require`
  must not fail your build), and stale entries fail so the ratchet only shrinks.
- [Open the module-split queue epic](tickets/closed/03-open-module-split-queue-epic.md)
  — live as #506; no audit-doc B-row folds into it, because checking premises
  showed B2 already satisfied by side effect (`CornerCorridorBridge.v` is 138
  lines, its worked example now in `BaseToTipSample.v`), B5 therefore unblocked
  and still real at 0 claims rows, and B3 is build-lane hygiene.
- [Retire #64 — arc primitives](tickets/closed/04-retire-64-arc-primitives.md)
  — **closed on circular-arc scope** (3 of 4 round-2 items had landed, including
  the quartic it called its deepest open work). Residue → #508 zoo-wide exact
  length (Bible §4.2 puts `length()` on the thin protocol; the `LENGTH_UNIFIED`
  oracle already exists but has no Coq companion and refuses `E`/`B` tokens),
  #509 V-CP Jordan, #510 the three arc conditionals, #511 the elliptic no-op,
  #503 register accuracy. The float-mode caveat was already documented per-mode;
  only `oracle/CONSUMERS.md` lacked a pointer, now added.

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
- **CurvePolygon kit completeness.** The maintainer asked for proof that the
  kits are complete in combination with CUP / CAP / XOR / SUB and a T-in / T-out
  Dim9 extension. `doc/EXACT_CURVE_BIBLE.md` §8 settles that "kits" means the
  **laser kits** (OverlayNGCurve, CurveExact, MIC/LEC, metrics, DE-9IM) rather
  than the corpus's seven `*Kit*.v` JCT modules — but two things block a sharp
  ticket. **T-in / T-out is vocabulary this corpus does not have** (exhaustive
  grep finds no directed touch notion; `theories/Tin.v` is Triangulated
  Irregular Networks, a false friend), and **"complete" has a refuted
  ancestor**: `OverlayTouchRow.v:225 phase0_relation_complete_hypothesis_refuted`
  proves the 7-row Phase-0 family incomplete because the external kiss is a
  genuine 8th row, with `seven_row_not_candidate_complete` alongside. Note also
  that `grep curve_polygon × (union|intersection|difference|symmetric|cup|cap|
  xor|sub)` over `theories/` is **empty** — the four ops are proven only on the
  abstract `OSet` carrier (`OverlayNGCurve.v:194`, axiom-free) and concretely
  only for two discs (`DiscOverlay.v`), so the centre of the ask is unbuilt.
  Graduates once the directed-touch definition and the intended row set exist.
- **A standing freshness re-run.** Whether "no stale issue bodies" becomes a
  quarterly chore like the split queue, once this map has walked it once.
- **Whether allowlist *growth* needs its own check.** `check_module_split.py`
  cannot see history, so it catches a new violation but not someone quietly
  adding a line to `docs/module-split-allowlist.txt`. The review gate already
  reports an "audit exceptions delta — no exception-list growth" for the older
  registry; whether it covers this new file, or whether CI needs an explicit
  `git diff` check, is not yet visible from here.

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
