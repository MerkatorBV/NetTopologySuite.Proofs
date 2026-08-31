# Map — same-cone certificate

A wayfinder map. Charted 2026-08-30; compiled 2026-08-30. This is **not**
a GitHub child, **not** a remint of `522-j` / `522-m` / `522-i`, and
**not** leftover `Ⅴ`'s opposite-sign cone
(`map-mixed-cone-cert.md`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals. This leftover is **`Ⅵ`**. Do not swap it with `Ⅴ`.
> Do not remint ADR-0004. This map does not mint a GitHub child.
> Leftover `Ⅶ` is the lens letter (`map-lens-cert.md`).
> Leftover `Ⅷ` is the inside pair (`map-inside-cert.md`).
> Leftover `Ⅸ` classified the nest (`map-nest-cert.md`).
> Do not mint leftover `Ⅹ`.

topics: relate
claimId: Ⅵ
witness: Ⅵ-same-cone-cex

## Destination

**Classify the leftover-Ⅴ completeness residue as leftover `Ⅵ`
without reminting `cone_separates_b` / `mixed_cone_vertex_b`.**

Ticket #577 asked either completeness (QED) or a documented counterexample
(QEX). That stop is now a theorem:
`RelateNGTouchSameCone.v : triangle_pair_regime_ccw_stop` (discharged QEX).
The filtered sibling is
`RelateNGTouchSameCone.v : triangle_pair_regime_ccw_stop_not_tjunction`.
Completeness is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). The
filtered retry is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
The live cex is an unnamed swapped nest pair after leftover
`Ⅸ` (`RelateNGNestCex.v : unnamed_ccw_pair_unsupported`). Leftover
`Ⅵ` itself is QED (`RelateNGTouchSameCone.v : leftover_vi_qed_or_qex`).

## The pair (compiled)

A = `(0,0)(2,0)(0,2)`, B = `(0,0)(3,1)(1,3)`.

Classifies `TPR_SameCone`:
`RelateNGUnnamedCex.v : same_cone_pair_samecone`.
Headline: `RelateNGTouchSameCone.v : triangle_pair_regime_samecone`.

Same A as leftover `Ⅴ`, leftover `Ⅱ`, and #572 / `522-i`. Leftover
`Ⅴ` moves B's third vertex to `(−1,−1)` (opposite-sign `side_dot`).
This leftover puts both remaining B-vertices on the **same** side of
`nA = (2,2)`: `side_dot(3,1) = 8`, `side_dot(1,3) = 8`. Both remaining
A-vertices are likewise both-pos vs `nB`. Interiors meet at `(0.5,0.5)`;
`overlap_b` misses (no vertex strictly inside the other).

Detector `RelateNGCore.v : same_cone_vertex_b` is both-strict-pos plus
`negb cone_separates_b` plus `negb closed_cone_separates_b` plus
`negb mixed_cone_from_v`. Not a remint of #572, leftover `Ⅱ`, or
leftover `Ⅴ`.

Constructor `TPR_SameCone` stays on `im_unsupported`
(`RelateMatrixTriangle.v : triangle_pair_fill_touch_samecone_eq`;
`RelateNGOracleSurface.v : triangle_touch_samecone_wire`). Do not emit
`2FFF1FFF2`. `classify_triangle_pair` arm is `True`.

Oracle / harness: `oracle/de9im_triangle_vectors.txt` `REGIME SAME_CONE`
(fill still `UNSUPPORTED`). Decline golden is the unnamed same-side
shared-edge pair A = `(0,0)(4,0)(0,4)`, B = `(0,0)(4,0)(1,1)`. The
lens pair is leftover `Ⅶ` (`RelateNGUnnamedCex.v : lens_pair_lens`).
The inside pair is leftover `Ⅷ` (`RelateNGUnnamedCex.v : inside_pair_inside`).

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(0,0)(2,0)(0,2)` vs `(0,0)(-1,-1)(3,1)` | Leftover `Ⅴ`. Classified **`TPR_MixedCone`**. Opposite-sign `side_dot`. `RelateNGComplete.v : mixed_cone_pair_mixedcone`. | remint `mixed_cone_vertex_b` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)` | Leftover `Ⅱ`. Classified **`TPR_TouchObtuse`**. Product of `side_dot`s is 0. | remint `touch_obtuse_vertex_b` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(0,-2)` | #572 / `522-i`. Classified **`TPR_TouchVertex`**. Same-sign opposite cone. | remint `cone_separates_b` / steal `522-i` |
| `(0,0)(3,0)(0,3)` vs `(2,-1)(2,2)(-1,2)` | Leftover `Ⅶ` lens. Classified **`TPR_Lens`**. `RelateNGUnnamedCex.v : lens_pair_lens`. | steal leftover `Ⅶ` |
| `(1,1)(2,1)(1,2)` vs `(0,0)(4,0)(0,4)` | Leftover `Ⅷ`. Classified **`TPR_Inside`**. A strictly inside B. `RelateNGUnnamedCex.v : inside_pair_inside`. | steal leftover `Ⅷ` |
| `(0,0)(4,0)(0,4)` vs `(0,0)(4,0)(1,1)` | Leftover `Ⅸ`. Classified **`TPR_Nest`**. Shared edge; B-in-A. `RelateNGNestCex.v : nest_pair_nest`. | steal leftover `Ⅸ` |
| `(0,0)(4,0)(1,1)` vs `(0,0)(4,0)(0,4)` | Leftover `Ⅹ` / `522-n`. Classified **`TPR_SwapNest`**. Swap; A-in-B. `RelateNGNestCex.v : swap_pair_swapnest`. | steal leftover `Ⅹ` / `522-n` |

Do not mint leftover `Ⅹ`. Epic `#522` stays OPEN.
