# #522 closing summary — owner sign-off requested

claimId: `522-l` · witness: `522-l-wrap-up`

This is the wrap-up letter for
[#522](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/522).
It does **not** retire the epic. Owner review retires it.

## Destination (met for the wired triangle regimes)

Bar 1: an emitted regime is true geometry against the specified interior
(`0 < gtri`, ADR-0003). Bar 2: each of the nine cells is the true DE-9IM
value for that geometry (gtri vocabulary, not `geom_de9im_pointset`).

A decline stays a decline: `im_unsupported` in Coq, token `UNSUPPORTED` on
the oracle wire. Never a confident `FFFFFFFFF` for an unclassified pair.

## What landed

| Ask | Result | Pin |
|---|---|---|
| Honesty fallthrough | `im_unsupported` | `RelateNGCore.v : relate_unsupported_no_predicate` |
| Overlap bar 1 | classified | `RelateNGOverlap.v : triangle_pair_regime_overlap` |
| Disjoint bar 1 | classified | `RelateNGDisjoint.v : triangle_pair_regime_disjoint` |
| Vertex-touch bar 1 | classified | `RelateNGTouchVertexRegime.v : triangle_pair_regime_touchvertex` |
| Contains bar 1 | detector → closed containment | `RelateNGContainsBridge.v : contains_b_ccw_implies_closed_containment` |
| Completeness | **false** (T-junction; obtuse-at-v) | `RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction` |
| Disjoint bar 2 gtri | FF2FF1212 | `RelateNGDisjointCells.v : sentinel_disjoint_ogc_gtri_cells` |
| Contains bar 2 gtri | 212FF1FF2 | `RelateNGContainsCells.v : contains_pair_ogc_gtri_cells` |
| Touch-edge bar 2 gtri | FF2F11212 | `RelateNGTouchEdgeCells.v : touch_edge_pair_ogc_gtri_cells` |
| Overlap bar 2 gtri | 212101212 | `RelateNGOverlapCells.v : overlap_pair_ogc_gtri_cells` |
| Wire token | `UNSUPPORTED` | `RelateNGOracleSurface.v : triangle_unsupported_token` |
| Prepared evaluate | cache-consulting | `RelatePrepared.v : prepared_evaluate_cache_short_circuit` |

Classifier fills are **not** reminted. The shared pins stay FFFFFFFFF /
2FFF1FFF2 / 2FFFFFFF2 / FFFF1FFF2. The OGC nine-cell names are `*_ogc`.

Honest decline golden vector is the T-junction, not the #530 pair (that
pair is classified disjoint).

## Named, not proved / not a #522 child

These are not holes in the original honesty ask. Chart:
[`map-522-leftovers.md`](map-522-leftovers.md). New leftover ids are
Roman numerals. Do **not** mint `522-n`.

- **TouchEdge exclusivity** vs the four gtri predicates — named, not
  proved. Carved on `main` via #597.
- **Fill remints** (classifier pointer → OGC `*_ogc`). Unnamed. Shared
  with the rect lane. Not `522-f`.
- **T-junction / partial-edge kiss** — leftover `Ⅰ` bar 1 landed
  (`RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`).
  Completeness recorded the finding and leftover `Ⅰ` classified the
  pair. Fill stays `im_unsupported`.
- **Obtuse-at-v certificate** — leftover `Ⅱ`. Finding
  `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`.
  Separate from `Ⅰ`. Detector not invented.
- **Nine-cell `geom_de9im_pointset`**, full noding, Touches-vs-Share —
  #67 / ticket 11, not #522 children.
- **`#523` `F` vs not-computed** — sibling. Grilled 2026-08-30
  ([`map-523.md`](map-523.md), [`spec-523.md`](spec-523.md)).
  Children `523-a` / `523-b` / `523-c` (#603 #604 #605) landed;
  ticket 523 still open, not accepted. Do not steal leftover `Ⅲ`.
  Leftover `Ⅳ` is the interior-side stem (named only).
- **Empty/empty relate** — parked on the epic.

## Surfaces that must agree

- TRIAGE row: `TRIAGE_NTS_JTS_ISSUES.md` `#522`
- Ledger: `docs/verified-claims.md` `#522` catalog + split paragraphs
- Living map: `docs/scout/map-522.md`
- Scholar Sam: `docs/relate-ng-status.md`
- Ticket 11 precondition 1: `docs/scout/tickets/11-retire-67-second-pass.md`

Prose gate: `scripts/validate-claims.sh` over `docs/gated-prose-docs.txt`.
