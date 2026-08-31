# Map — lens certificate

A wayfinder map. Charted 2026-08-30; compiled 2026-08-30. This is **not**
a GitHub child, **not** a remint of `522-j` / `522-m` / `522-b`, and
**not** leftover `Ⅵ`'s same-cone
(`map-same-cone-cert.md`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals. This leftover is **`Ⅶ`**. Do not swap it with `Ⅵ`.
> Do not remint ADR-0004. This map does not mint a GitHub child.
> Do not mint leftover `Ⅷ`.

topics: relate
claimId: Ⅶ
witness: Ⅶ-lens-cex

## Destination

**Classify the leftover-Ⅵ completeness residue as leftover `Ⅶ`
without reminting `segments_proper_cross` / `overlap_b`.**

Ticket #577 asked either completeness (QED) or a documented counterexample
(QEX). That stop is now a theorem:
`RelateNGTouchLens.v : triangle_pair_regime_ccw_stop` (discharged QEX).
The filtered sibling is
`RelateNGTouchLens.v : triangle_pair_regime_ccw_stop_not_tjunction`.
Completeness is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). The
filtered retry is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
The live cex is an unnamed inside pair (not leftover `Ⅷ`). Leftover
`Ⅶ` itself is QED (`RelateNGTouchLens.v : leftover_vii_qed_or_qex`).

## The pair (compiled)

A = `(0,0)(3,0)(0,3)`, B = `(2,-1)(2,2)(-1,2)`.

Classifies `TPR_Lens`:
`RelateNGUnnamedCex.v : lens_pair_lens`.
Headline: `RelateNGTouchLens.v : triangle_pair_regime_lens`.

Both CCW (`gdbl` 9 and 9). `(1,1)` is strictly in both interiors.
No shared vertex — cone / obtuse / mixed / same-cone miss.
All B verts sit outside A; all A verts sit outside B — `overlap_b`
misses. A's hypotenuse `x+y=3` crosses B's vertical `x=2` at `(2,1)`.

Detector `RelateNGCore.v : lens_edges_cross_b` is a boolean proper-cross
of some A-edge with some B-edge (`opposite_sides_b` both ways). Not a
remint of the noding-lane Prop `segments_proper_cross`.

Constructor `TPR_Lens` stays on `im_unsupported`
(`RelateMatrixTriangle.v : triangle_pair_fill_touch_lens_eq`;
`RelateNGOracleSurface.v : triangle_touch_lens_wire`). Do not emit
`2FFF1FFF2`. `classify_triangle_pair` arm is `True`.

Oracle / harness: `oracle/de9im_triangle_vectors.txt` `REGIME LENS`
(fill still `UNSUPPORTED`). Decline golden is the unnamed inside pair
A = `(1,1)(2,1)(1,2)`, B = `(0,0)(4,0)(0,4)`.

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(0,0)(2,0)(0,2)` vs `(0,0)(3,1)(1,3)` | Leftover `Ⅵ`. Classified **`TPR_SameCone`**. Same-sign spill. `RelateNGUnnamedCex.v : same_cone_pair_samecone`. | steal leftover `Ⅵ` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-1,-1)(3,1)` | Leftover `Ⅴ`. Classified **`TPR_MixedCone`**. Opposite-sign `side_dot`. | remint `mixed_cone_vertex_b` |
| `(0,0)(1,0)(0,1)` vs `(1/4,1/4)(5/4,1/4)(1/4,5/4)` | #570 / `522-b`. Classified **`TPR_Overlap`**. Vertex stab. | remint `overlap_b` / emit `2FFF1FFF2` |
| `(1,1)(2,1)(1,2)` vs `(0,0)(4,0)(0,4)` | Unnamed completeness cex. A strictly inside B; no edge crossings. `RelateNGUnnamedCex.v : unnamed_ccw_pair_unsupported`. | mint leftover `Ⅷ` |

Do not mint leftover `Ⅷ`. Epic `#522` stays OPEN.
