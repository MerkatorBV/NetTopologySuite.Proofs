# Map — swap-nest certificate

A wayfinder map. Charted 2026-08-31; compiled 2026-08-31. This is **not**
a GitHub child, **not** a remint of `522-j` / `522-m` / `522-h`, and
**not** leftover `Ⅸ`'s nest pair
(`map-nest-cert.md`).

> Closed ticket ids (`522-a` … `522-m`) stay historical. This letter
> mints board claimId **`522-n`** as leftover **`Ⅹ`** (owner
> override of ADR-0004 for this letter only). Leftover ids stay
> precomposed Roman numerals. Do not swap `Ⅹ` with `Ⅸ`. Do not
> remint ADR-0004 for later leftovers. This map does not mint a
> GitHub child. Do not mint leftover `Ⅺ`.

topics: relate
claimId: 522-n
witness: 522-n-swap-cex
board: leftover-Ⅹ

## Destination

**Classify the leftover-Ⅸ completeness residue as leftover `Ⅹ` /
`522-n` without reminting `nest_b` / `inside_b` / `contains_b` /
`touch_edge_b`.**

Ticket #577 asked either completeness (QED) or a documented counterexample
(QEX). That stop is now a theorem:
`RelateNGTouchSwapNest.v : triangle_pair_regime_ccw_stop` (discharged QEX).
The filtered sibling is
`RelateNGTouchSwapNest.v : triangle_pair_regime_ccw_stop_not_tjunction`.
Completeness is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). The
filtered retry is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
The live cex is an unnamed identical CCW pair (not leftover
`Ⅺ`). Leftover `Ⅹ` itself is QED
(`RelateNGTouchSwapNest.v : leftover_x_qed_or_qex`).

## The pair (compiled)

A = `(0,0)(4,0)(1,1)`, B = `(0,0)(4,0)(0,4)`.

Classifies `TPR_SwapNest`:
`RelateNGNestCex.v : swap_pair_swapnest`.
Headline: `RelateNGTouchSwapNest.v : triangle_pair_regime_swapnest`.

Both CCW. Shared full edge `(0,0)-(4,0)`. Thirds same side of that
edge, so `touch_edge_b` misses. A's third vertex `(1,1)` is strictly
interior to B (`gtri B = 4`). Two shared vertices, so the cone
detectors miss. `nest_b` misses (B-in-A only; `(0,4)` is outside
small A). `inside_b` misses (A verts on B's boundary). `contains_b`
misses (B verts on A's boundary). `overlap_b` misses (no B vertex
strictly interior to A).

Detector `RelateNGCore.v : swap_nest_b` is both CCW plus some shared
edge plus some A vertex strictly interior to B. Not a remint of
`nest_b` / `inside_b` / `contains_b` / `touch_edge_b`.

Constructor `TPR_SwapNest` stays on `im_unsupported`
(`RelateMatrixTriangle.v : triangle_pair_fill_touch_swapnest_eq`;
`RelateNGOracleSurface.v : triangle_touch_swapnest_wire`). Do not emit
`2FFFFFFF2` or `FF2F11212`. `classify_triangle_pair` arm is `True`.

Oracle / harness: `oracle/de9im_triangle_vectors.txt` `REGIME SWAPNEST`
(fill still `UNSUPPORTED`). Decline golden is the unnamed identical
pair A = B = `(0,0)(4,0)(0,4)`.

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(0,0)(4,0)(0,4)` vs `(0,0)(4,0)(1,1)` | Leftover `Ⅸ`. Classified **`TPR_Nest`**. Shared edge; B-in-A. `RelateNGNestCex.v : nest_pair_nest`. | steal leftover `Ⅸ` |
| `(1,1)(2,1)(1,2)` vs `(0,0)(4,0)(0,4)` | Leftover `Ⅷ`. Classified **`TPR_Inside`**. No shared edge. | steal leftover `Ⅷ` |
| `(0,0)(1,0)(0,1)` vs `(1,0)(1,1)(0,1)` | #567 touch-edge. Classified **`TPR_TouchEdge`**. Opposite sides. | remint `touch_edge_b` / emit `FF2F11212` |
| `(0,0)(4,0)(0,4)` vs `(0,0)(4,0)(0,4)` | Unnamed completeness cex. Identical CCW pair. `RelateNGNestCex.v : unnamed_ccw_pair_unsupported`. | mint leftover `Ⅺ` |

Do not mint leftover `Ⅺ`. Epic `#522` stays OPEN.
