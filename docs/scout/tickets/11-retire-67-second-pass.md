# Retire #67 — second pass

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** three of the four preconditions below — ADR-0003 unconsumed by the capstone, **ticket 523** open (grilled + specced, not accepted; [`map-523.md`](../map-523.md), [`spec-523.md`](../spec-523.md)), **#503**'s four defects uncorrected. Precondition 1 is largely met by **#530**. See [Retire #67 — RelateNG](closed/07-retire-67-relateng.md) for why the first pass declined to close.

> **Note, 2026-08-22.** #67 was briefly closed by accident: the ticket-07 commit's
> subject line contained the substring `close #67` (in the phrase "decide NOT to
> close #67"), which GitHub read as a directive. Reopened, with the convention
> recorded in [`docs/agents/issue-tracker.md`](../../agents/issue-tracker.md).
> The decision to keep it open was never revisited.

## Question

The first pass decided **not** to close #67: its compute path returns confidently
wrong matrices with no marker, and four classifiers are `Prop := True`. Closing
then would have been an overclaim. This ticket asks the same question once the
blocking defects are gone: **does #67 close, and where does its residue go?**

Preconditions to check before re-deciding — each is a specific, checkable fact:

1. **#522 honesty + wired triangle bars** — *met as of 2026-08-30; wrap-up
   is [`docs/scout/522-closing-summary.md`](../522-closing-summary.md). Living
   frontier: [`docs/scout/map-522.md`](../map-522.md). Epic #522 stays open
   until owner sign-off.*
   - ✔ Fallthrough is `im_unsupported` (`RelateNGCore.v : relate_unsupported_no_predicate`).
   - ✔ Overlapping triangles classify overlap, not disjoint
     (`RelateNGOverlap.v : triangle_pair_regime_overlap`).
   - ✔ The four `Prop := True` classifiers are gone
     (`RelateMatrixTriangle.v : regime_predicates_pairwise_exclusive`).
   - ✔ Cache-consulting `evaluate`
     (`RelatePrepared.v : prepared_evaluate_cache_short_circuit`).
   - ✔ Bar 2 gtri cells on the wired regimes (disjoint / contains /
     touch-edge / overlap `*_ogc`). Classifier pins are **not** reminted.
   - ✔ Completeness is false (T-junction; obtuse-at-v)
     (`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`).
   - ~ Residue that is **not** a #522 honesty hole: fill remints, leftover
     certificates, `TPR_TouchEdge` exclusivity (#567 carve), nine-cell
     `geom_de9im_pointset`.
2. **ADR-0003 actually consumed.** The two-tier model is declared; check that the
   nine-cell capstone work uses it — BI and side-E\* specified against the *open*
   interior and reached through the bridge, rather than re-deferred. Today: 3/9
   cells for triangle touch (II `RelateNGTouchCells.v:204` guarded, BB `:337`, EE
   `:54`), 2/9 for rect touch (EE `RelateNGRect.v:160`, II `:305`).
3. **#523 resolved or explicitly accepted.** *Grilled 2026-08-30
   ([`map-523.md`](../map-523.md), ticket 12). Spec written
   ([`spec-523.md`](../spec-523.md), ticket 13). Still open. Not
   accepted.* The three F-without-empty claims still hold
   (`RelateCurveMatrix.v : cell_none_iff_empty` is the Coq emptiness;
   the oracle prints `F` for E/B `[]`, undistinguished lineal cells, and
   an 80×80 grid miss). The second half of this precondition — record
   that the geometry-compute mode cannot yet be used as a differential
   reference — is now written on that map. That is documentation of the
   defect, not acceptance. The spec does not change this precondition's
   language. Ticket 523 itself still blocks this ticket.
4. **The four documentation defects** from #503 corrected, since two of them
   *understated* what is proven and would make the closure evidence look
   thinner than it is. The stale S15l+ "regime DEFERRED" row lived in the
   pre-#530 triage; that file is archived (`docs/history/issue-67-relateng-triage.md`)
   and the living citation is `touch_triangles_regime_cells_ii_bb_ee` on
   [`docs/relate-ng-status.md`](../../relate-ng-status.md). The other register
   defects remain #503's.

Residue that will still need placing at that point, none of it blocking:

- The nine-cell capstone remainder, whatever ADR-0003 leaves.
- Multi-geometry / mixed-dimension relate — nothing exists beyond
  `RelateNodingLineLineCollection.v`'s `list Segment2` cross-products, and
  `RelateNGCore.v:337` is the general case.
- `DE9IM.v`'s recorded incompleteness witness
  (`disjoint_intersects3_example_holds:458` — one matrix satisfies both `disjoint`
  and `intersects₃`). Decide whether that is a permanent caution or an ask.

Do **not** re-litigate: the II-cell guard is maximal (`RelateNGTouchRED.v:170`,
Qed) and `touch_int_ext_exclusion` (`RelateNGTouch.v:200`) is unconditional. Both
are results.
