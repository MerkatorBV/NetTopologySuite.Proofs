# Retire #67 — RelateNG matrix and boundary handling

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** —

## Question

#67 (Immediate) asks for the DE-9IM matrix, predicates, MOD2 boundary handling,
prepared mode and oracle modes. The audit reads **MOSTLY**: both named round-2
blockers are now Qed. Does it close, and where does its residue go?

Satisfied (verify then cite): `theories/RelateNGTouchCells.v:75 touch_triangle_pair_ii_cell`
and `RelateNGTouch.v:166/200 touch_int_ext_exclusion`; the JCT seam lift
`gtri_point_in_ring_imp_pos` annotated **DISCHARGED (was Admitted)**, with the
guard-free form refuted by `touch_triangle_ii_separation_not_unconditional`; the
regime→cell triple `touch_triangles_regime_cells_ii_bb_ee` (2026-07-20,
`docs/issue-67-relateng-triage.md` §S15l); asks 1/2/3a green via `DE9IM.v` and
`RelateLineLine.v`; oracle `RELATE_MATRIX`, `RELATE_PREDICATE`,
`CURVE_RELATE_MATRIX` present. `RelateNG.v` split into six layers 2026-08-15
(`docs/audit-meso-sample-2026-08.md` B6 = DONE).

Residue to place:

1. The full nine-cell `geom_de9im_pointset` capstone — BI and side-E\* cells
   mismatch the hand-specified F values because of half-open ring inclusion on
   shared edges; still marked DEFERRED in `docs/issue-67-relateng-triage.md`. Is
   this one issue or several? (This is the fog patch the map names.)
2. `TPR_Overlap` and the remaining regimes — defined in
   `RelateMatrixTriangle.v:28/100`, no sound cheap test yet.
3. Multi-geometry / compound-input pipeline.
4. Prepared-cache end-to-end `evaluate` hook.
5. An oracle geometry-**compute** mode; today's modes are pinned-catalog only.

Also settle a convention question this epic raises: the sibling GEOS rung doc
(`docs/geos-oracle-rung-2026-08.md`) records six warns as "soft boundary/DE-9IM
convention notes" with no decision recorded on the convention itself. That
half-open-inclusion convention is the same one blocking residue item 1 — decide
whether it is one decision serving both, and record it once.
