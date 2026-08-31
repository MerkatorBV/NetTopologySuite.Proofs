# Map — nest certificate

A wayfinder map. Charted 2026-08-31; compiled 2026-08-31. This is **not**
a GitHub child, **not** a remint of `522-j` / `522-m` / `522-h`, and
**not** leftover `Ⅷ`'s inside pair
(`map-inside-cert.md`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals. This leftover is **`Ⅸ`**. Do not swap it with `Ⅷ`.
> Do not remint ADR-0004. This map does not mint a GitHub child.
> Do not mint leftover `Ⅹ`.

topics: relate
claimId: Ⅸ
witness: Ⅸ-nest-cex

## Destination

**Classify the leftover-Ⅷ completeness residue as leftover `Ⅸ`
without reminting `touch_edge_b` / `contains_b` / `overlap_b`.**

Ticket #577 asked either completeness (QED) or a documented counterexample
(QEX). That stop is now a theorem:
`RelateNGTouchNest.v : triangle_pair_regime_ccw_stop` (discharged QEX).
The filtered sibling is
`RelateNGTouchNest.v : triangle_pair_regime_ccw_stop_not_tjunction`.
Completeness is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). The
filtered retry is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
The live cex after leftover `Ⅸ` was the swap (now leftover
`Ⅹ` / `522-n`). Leftover `Ⅸ` itself is QED
(`RelateNGTouchNest.v : leftover_ix_qed_or_qex`).

## The pair (compiled)

A = `(0,0)(4,0)(0,4)`, B = `(0,0)(4,0)(1,1)`.

Classifies `TPR_Nest`:
`RelateNGNestCex.v : nest_pair_nest`.
Headline: `RelateNGTouchNest.v : triangle_pair_regime_nest`.

Both CCW. Shared full edge `(0,0)-(4,0)`. Thirds same side of that
edge, so `touch_edge_b` misses. B's third vertex `(1,1)` is strictly
interior to A (`gtri A = 4`). Two shared vertices, so the cone
detectors miss. `contains_b` misses (B verts on A's boundary).
`overlap_b` misses (no B vertex strictly exterior). `inside_b`
misses (A verts not all interior to B).

Detector `RelateNGCore.v : nest_b` is both CCW plus some shared
edge plus some B vertex strictly interior to A. Not a remint of
`touch_edge_b` / `contains_b` / `overlap_b`.

Constructor `TPR_Nest` stays on `im_unsupported`
(`RelateMatrixTriangle.v : triangle_pair_fill_touch_nest_eq`;
`RelateNGOracleSurface.v : triangle_touch_nest_wire`). Do not emit
`2FFFFFFF2` or `FF2F11212`. `classify_triangle_pair` arm is `True`.

Oracle / harness: `oracle/de9im_triangle_vectors.txt` `REGIME NEST`
(fill still `UNSUPPORTED`). Decline golden is the unnamed swap
A = `(0,0)(4,0)(1,1)`, B = `(0,0)(4,0)(0,4)`.

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(1,1)(2,1)(1,2)` vs `(0,0)(4,0)(0,4)` | Leftover `Ⅷ`. Classified **`TPR_Inside`**. No shared edge. | steal leftover `Ⅷ` |
| `(0,0)(1,0)(0,1)` vs `(1,0)(1,1)(0,1)` | #567 touch-edge. Classified **`TPR_TouchEdge`**. Opposite sides. | remint `touch_edge_b` / emit `FF2F11212` |
| `(0,0)(4,0)(1,1)` vs `(0,0)(4,0)(0,4)` | Leftover `Ⅹ` / `522-n`. Classified **`TPR_SwapNest`**. Swap; A-in-B. `RelateNGNestCex.v : swap_pair_swapnest`. | steal leftover `Ⅹ` / `522-n` |

Leftover `Ⅹ` / `522-n` classified the swap. Do not mint leftover
`Ⅺ`. Epic `#522` stays OPEN.
