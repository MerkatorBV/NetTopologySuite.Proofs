# Retire #67 — second pass

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** **#522** (the `relate` wrong-answer fallthrough) must be fixed — see [Retire #67 — RelateNG](closed/07-retire-67-relateng.md) for why the first pass declined to close

## Question

The first pass decided **not** to close #67: its compute path returns confidently
wrong matrices with no marker, and four classifiers are `Prop := True`. Closing
then would have been an overclaim. This ticket asks the same question once the
blocking defects are gone: **does #67 close, and where does its residue go?**

Preconditions to check before re-deciding — each is a specific, checkable fact:

1. **#522 fixed.** `RelateNGCore.v:337` no longer answers `ll_matrix_disjoint` for
   unsupported pairs; `triangle_pair_regime` either emits `TPR_Overlap` or returns
   an explicit unsupported sentinel; the four `Prop := True` classifiers in
   `RelateMatrixTriangle.v:89-94` are real predicates or gone. And
   `RelatePrepared.v:48 prepared_evaluate_agrees` says something — it is currently
   Qed by `reflexivity` over the stub.
2. **ADR-0003 actually consumed.** The two-tier model is declared; check that the
   nine-cell capstone work uses it — BI and side-E\* specified against the *open*
   interior and reached through the bridge, rather than re-deferred. Today: 3/9
   cells for triangle touch (II `RelateNGTouchCells.v:204` guarded, BB `:337`, EE
   `:54`), 2/9 for rect touch (EE `RelateNGRect.v:160`, II `:305`).
3. **#523 resolved or explicitly accepted.** `CURVE_RELATE_MATRIX` distinguishes
   `F` (proven empty) from not-computed, or the epic records that its one
   geometry-compute mode cannot yet be used as a differential reference.
4. **The four documentation defects** from #503 corrected, since two of them
   (`issue-67-relateng-triage.md:296`, `verified-claims.md:851`) *understate* what
   is proven and would make the closure evidence look thinner than it is.

Residue that will still need placing at that point, none of it blocking:

- The nine-cell capstone remainder, whatever ADR-0003 leaves.
- Multi-geometry / mixed-dimension relate — nothing exists beyond
  `RelateNodingLineLineCollection.v`'s `list Segment2` cross-products, and
  `RelateNGCore.v:337` is the general case.
- A cache-*consulting* prepared `evaluate` (ask #5).
- `DE9IM.v`'s recorded incompleteness witness
  (`disjoint_intersects3_example_holds:458` — one matrix satisfies both `disjoint`
  and `intersects₃`). Decide whether that is a permanent caution or an ask.

Do **not** re-litigate: the II-cell guard is maximal (`RelateNGTouchRED.v:170`,
Qed) and `touch_int_ext_exclusion` (`RelateNGTouch.v:200`) is unconditional. Both
are results.
