# Map — inside certificate

A wayfinder map. Charted 2026-08-31; compiled 2026-08-31. This is **not**
a GitHub child, **not** a remint of `522-j` / `522-m` / `522-h`, and
**not** leftover `Ⅶ`'s lens
(`map-lens-cert.md`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Leftover `Ⅹ` is board claimId **`522-n`**. Leftover
> ids are precomposed Roman numerals. This leftover is **`Ⅷ`**.
> Do not swap it with `Ⅶ`. Do not remint ADR-0004 for later
> leftovers. This map does not mint a GitHub child.
> Leftover `Ⅸ` classified the nest (`map-nest-cert.md`).
> Leftover `Ⅹ` classified the swap (`map-swap-nest-cert.md`).
> Do not mint leftover `Ⅺ`.

topics: relate
claimId: Ⅷ
witness: Ⅷ-inside-cex

## Destination

**Classify the leftover-Ⅶ completeness residue as leftover `Ⅷ`
without reminting `contains_b` / `aa_matrix_contains`.**

Ticket #577 asked either completeness (QED) or a documented counterexample
(QEX). That stop is now a theorem:
`RelateNGTouchInside.v : triangle_pair_regime_ccw_stop` (discharged QEX).
The filtered sibling is
`RelateNGTouchInside.v : triangle_pair_regime_ccw_stop_not_tjunction`.
Completeness is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). The
filtered retry is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
The live cex is an unnamed identical CCW pair after leftover `Ⅹ`
(not leftover `Ⅺ`). Leftover `Ⅷ` itself is QED
(`RelateNGTouchInside.v : leftover_viii_qed_or_qex`).

## The pair (compiled)

A = `(1,1)(2,1)(1,2)`, B = `(0,0)(4,0)(0,4)`.

Classifies `TPR_Inside`:
`RelateNGUnnamedCex.v : inside_pair_inside`.
Headline: `RelateNGTouchInside.v : triangle_pair_regime_inside`.

Both CCW (`gdbl` 1 and 16). Every A vertex is strictly interior to B
(`gtri B = 4`). No B vertex in A. No shared vertex. No edge crossings.
`contains_b` misses (that detector is B-in-A). `overlap_b` misses (no
B-vertex stab).

Detector `RelateNGCore.v : inside_b` is B CCW plus all three A vertices
strictly interior to B. Not a remint of `contains_b`.

Constructor `TPR_Inside` stays on `im_unsupported`
(`RelateMatrixTriangle.v : triangle_pair_fill_touch_inside_eq`;
`RelateNGOracleSurface.v : triangle_touch_inside_wire`). Do not emit
`2FFFFFFF2`. `classify_triangle_pair` arm is `True`.

Oracle / harness: `oracle/de9im_triangle_vectors.txt` `REGIME INSIDE`
(fill still `UNSUPPORTED`). Decline golden is the unnamed identical
CCW pair A = B = `(0,0)(4,0)(0,4)`.

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(0,0)(3,0)(0,3)` vs `(2,-1)(2,2)(-1,2)` | Leftover `Ⅶ`. Classified **`TPR_Lens`**. Proper edge-cross. `RelateNGUnnamedCex.v : lens_pair_lens`. | steal leftover `Ⅶ` |
| `(0,0)(1,0)(0,1)` vs `(1/4,1/4)(1/2,1/4)(1/4,1/2)` | #567 contains. Classified **`TPR_Contains`**. B-in-A. | remint `contains_b` / emit `2FFFFFFF2` |
| `(0,0)(4,0)(0,4)` vs `(0,0)(4,0)(1,1)` | Leftover `Ⅸ`. Classified **`TPR_Nest`**. Shared edge; B-in-A. `RelateNGNestCex.v : nest_pair_nest`. | steal leftover `Ⅸ` |
| `(0,0)(4,0)(1,1)` vs `(0,0)(4,0)(0,4)` | Leftover `Ⅹ` / `522-n`. Classified **`TPR_SwapNest`**. Shared edge; A-in-B. `RelateNGNestCex.v : swap_pair_swapnest`. | steal leftover `Ⅹ` |

Do not mint leftover `Ⅺ`. Epic `#522` stays OPEN.
