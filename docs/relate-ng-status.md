# RelateNG / DE-9IM — living status (Scholar Sam)

Successor of the archived pre-#530 triage
(`docs/history/issue-67-relateng-triage.md`). Cite theorems by **name**.
Do not cite line numbers. Session counts and S-rung labels in the archive
are chronology.

Cross-epic source of record for batch status remains
[`TRIAGE_NTS_JTS_ISSUES.md`](../TRIAGE_NTS_JTS_ISSUES.md). The #522
children have their own live gate: [`docs/scout/map-522.md`](scout/map-522.md).

## What to open

| Question | Surface |
|---|---|
| Is this theorem in the corpus? | [`verified-claims.md`](verified-claims.md) `#67` / `#522` rows |
| What is the specified interior? | [ADR-0003](adr/ADR-0003-two-tier-interior-spec-parity-computation.md) |
| What is the next #522 grab? | [`scout/map-522.md`](scout/map-522.md) |
| Does #67 itself retire? | [`scout/tickets/11-retire-67-second-pass.md`](scout/tickets/11-retire-67-second-pass.md) |
| Rect + triangle touch cells | [`rect-triangle-touch-milestone.md`](rect-triangle-touch-milestone.md) |
| Clothoid leftovers | [`clothoid-open-questions-triage.md`](clothoid-open-questions-triage.md) |
| Why the triage was written | [`history/issue-67-relateng-triage.md`](history/issue-67-relateng-triage.md) |

## Proven (gated names)

These are the facts Scholar Sam still needs from the old triage. Each
name is a ledger row (or a sibling listed next to one). If a name is
missing from `verified-claims.md`, that is a #503 defect, not a hole in
the mathematics.

**Honesty / decline**

- `im_unsupported_no_predicate` — sentinel supports no `RelatePredicate`
- `relate_unsupported_no_predicate` — general-case fallthrough declines
- `relate_tjunction_pair_no_predicate` — leftover decline pin is the T-junction
- `triangle_unsupported_token` / `relate_tjunction_wire_unsupported` — wire token `UNSUPPORTED` (draft #588 / `522-f`; not necessarily on `main` yet)

**Regime predicates and bar 1**

- `regime_predicates_pairwise_exclusive` — the four former `True` arms are geometry
- `contains_b_ccw_implies_closed_containment` — detector → closed containment
- `triangle_pair_regime_overlap` / `triangle_pair_regime_disjoint` / `triangle_pair_regime_touchvertex`
- `triangles_touch_on_shared_edge` — frozen shared-edge predicate (not reminted)

**Bar 2 beachhead and ring inclusion**

- `gtri_strict_pos_open_disk` / `dim1_on_nondeg_segment` / `sentinel_ie_has_dim2`
- `sentinel_disjoint_ogc_gtri_cells` — nine specified-interior cells of FF2FF1212
- `ogc_disjoint_fill_not_im_disjoint` — Qex: `pat_disjoint` rejects that fill

**Completeness is false**

- `triangle_pair_regime_incomplete_tjunction`
- `triangle_pair_regime_ccw_incomplete_not_tjunction`

**Touch cells (the row the archive understated)**

- `touch_triangles_regime_cells_ii_bb_ee` — II + BB + EE `cell_ok` under `TPR_TouchEdge`
- `touch_int_ext_exclusion` — unconditional specified-interior exclusion
- `touch_triangle_ii_separation_not_unconditional` — guard-free II is false
- `relate_on_rects_dispatches` / `touch_regime_exterior_row_pinned` / `touch_rect_pair_ii_cell`
- `ii_cell_dim2_sound_gtri`

**Line×line noding (67-c and the S15 pipeline)**

- `line_collection_test10_de9im_pointset` / `line_collection_matrix_fold_sound`
- `line_pair_fill_disjoint_ie_not_true_dim` — S8 fill honesty gap
- Exterior-row true-dim pin lives in `RelateNodingLineLineExtPinned.v` (ledger #67-c)

**Prepared hook (still a stub)**

- `prepared_evaluate_agrees` — holds of the stub
- `evaluate_ignores_cache` — tripwire; #574 / `522-e` is the real evaluate

**Curve-polygon × point / S10b–S12**

- `arc_chord_dist_sq_via_sweep`
- `point_in_rect_curve_geometry_iff_polygon`
- `point_in_rect_curve_geometry_characterisation`

## Still open (not a theorem)

Carved off the archive's "still open" list. None of these is a decline
disguised as disjointness — that was #530.

- **Full RelateNG noding** for arbitrary (point / line / area / collection)
  geometry. Today's `relate` declines off the rect and triangle dispatch.
  Not a #522 child.
- **Nine-cell `geom_de9im_pointset` capstone** — BI and side-E\* vs hand-specified
  `F`, because parity `point_set` is half-open. ADR-0003 is the convention;
  #576 / `522-h` is the remaining triangle bar-2 work; ticket 11 tracks
  whether the capstone consumed the ADR.
- **Touches-vs-Share `LPR_Touches` fill split** (line×line). Companion of
  `line_pair_fill_share_ii_not_pinned_int_bnd_only`.
- **Cache-consulting `evaluate`** — #574 / `522-e`.
- **`F` vs not-computed** on `CURVE_RELATE_MATRIX` — sibling #523, not a #522 child.
- **Empty/empty `relate`** — parked on the #522 epic (declines; ISO 13249-3
  if revisited).
- **`TPR_TouchEdge` exclusivity** vs the four gtri predicates — named leftover
  on #567 / `522-a`, not a predicate rewrite.
- **Disjoint fill remint** (FFFFFFFFF → FF2FF1212) — unnamed. Not `522-f`.
- **T-junction / obtuse certificates** — unnamed. Completeness tickets
  recorded the findings and stopped. Leftover letter `522-n` if minted.
- **Inherited JCT seam** for general-polygon Contains (not the rectangle
  special case). `point_in_ring_correct` remains conditional.

Volatile counts (how many cells, how many S-rungs) stay in the archive or
wait for the #578 prose gate. This page names theorems and tickets only.

## External pins the archive still got right

- JTS#1175 (`computeLineEnds` skipping disjoint line-component ends) is
  fixed upstream (JTS#1200). The corpus pin is the JTS#1175 class in
  `RelateBoundary.v` / `jts1175_*` ledger rows.
- NTS#819 prepared A-L cache is a performance issue; the proof obligation
  is result-independence of the cache path (`evaluate_ignores_cache` today,
  #574 tomorrow).
