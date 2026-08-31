# Map — leftover `Ⅶ` edge-cross residue

A wayfinder map. Charted 2026-08-30; compiled 2026-08-30. This is **not**
a GitHub child, **not** a remint of `522-j` / `522-m` / `522-b`, and
**not** leftover `Ⅵ`'s same-cone
(`map-same-cone-cert.md`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals. This leftover is **`Ⅶ`**. Do not swap it with `Ⅵ`.
> Do not remint ADR-0004. This map does not mint a GitHub child.
> Do not mint leftover `Ⅷ` in this letter.

topics: relate
claimId: Ⅶ
witness: Ⅶ-lens-cex

## Destination

**Name the leftover-Ⅵ completeness residue as leftover `Ⅶ`.**
Accept as leftover-Ⅶ classification. Reject as a lens theorem or
an overlap theorem.

Ticket #577 asked either completeness (QED) or a documented counterexample
(QEX). Relocating
`RelateNGTouchLens.v : triangle_pair_regime_ccw_stop` here does **not**
move epic #522 closer to QED — one more named bucket. The stop is the
same disjunction already proved in the leftover-Ⅴ / leftover-Ⅵ files,
discharged QEX. Completeness is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). The
filtered retry is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
The live cex is nested containment (A strictly inside B;
`contains_b` is one-sided). Not leftover `Ⅷ` in this letter.
`leftover_vii_qed_or_qex` is classified ∨ declined on the pair this
letter just classified.

## The pair (compiled)

A = `(0,0)(3,0)(0,3)`, B = `(2,-1)(2,2)(-1,2)`.

Inhabits `TPR_Lens`:
`RelateNGUnnamedCex.v : lens_pair_lens`.
Headline: `RelateNGTouchLens.v : triangle_pair_regime_lens`
(inhabitance, not soundness).

Both CCW (`gdbl` 9 and 9). `(1,1)` is strictly in both interiors.
No shared vertex — cone / obtuse / mixed / same-cone miss.
All B verts sit outside A; all A verts sit outside B — `overlap_b`
is still a vertex-stab certificate and misses. A's hypotenuse
`x+y=3` crosses B's vertical `x=2` at `(2,1)`. That is the missing
`overlap_b` clause; this letter parks the residue on `TPR_Lens`
instead of widening the certificate.

Detector `RelateNGCore.v : lens_edges_cross_b` is both-CCW plus a
transversal edge pair (`opposite_sides_b` both ways). It does not
mention interiors, lenses, or area-2 II. On convex triangles a
relative-interior edge cross implies interior overlap, so the
compiled pair is a lens. The predicate is not.
Leftover `Ⅰ` / leftover `Ⅴ` / leftover `Ⅵ` and the hard overlap
pair also have proper edge crosses; they stay off `TPR_Lens`
because they fire earlier. Order is exclusive, not the boolean.
`segments_proper_cross_b` is the remint the honesty clause allowed
under a `_b` suffix; the noding-lane Prop `segments_proper_cross`
is identifier-untouched only.

Constructor `TPR_Lens` stays on `im_unsupported`
(`RelateMatrixTriangle.v : triangle_pair_fill_touch_lens_eq`;
`RelateNGOracleSurface.v : triangle_touch_lens_wire`). Do not emit
`2FFF1FFF2`. `classify_triangle_pair` arm is `True` — no denotation.

Oracle / harness: `oracle/de9im_triangle_vectors.txt` `REGIME LENS`
(fill still `UNSUPPORTED`). Decline golden is the nested pair
A = `(1,1)(2,1)(1,2)`, B = `(0,0)(4,0)(0,4)` — contains in the
other direction, not an unnamed mystery.

`classified_hard_pairs_still_lens` is misnamed: those pairs stay
Disjoint / Overlap / TouchVertex / TouchEdge.

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(0,0)(2,0)(0,2)` vs `(0,0)(3,1)(1,3)` | Leftover `Ⅵ`. Classified **`TPR_SameCone`**. Same-sign spill. `RelateNGUnnamedCex.v : same_cone_pair_samecone`. | steal leftover `Ⅵ` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-1,-1)(3,1)` | Leftover `Ⅴ`. Classified **`TPR_MixedCone`**. Opposite-sign `side_dot`. | remint `mixed_cone_vertex_b` |
| `(0,0)(1,0)(0,1)` vs `(1/4,1/4)(5/4,1/4)(1/4,5/4)` | #570 / `522-b`. Classified **`TPR_Overlap`**. Vertex stab. | remint `overlap_b` / emit `2FFF1FFF2` |
| `(1,1)(2,1)(1,2)` vs `(0,0)(4,0)(0,4)` | Nested containment cex. A strictly inside B; no edge crossings. `RelateNGUnnamedCex.v : unnamed_ccw_pair_unsupported`. | mint leftover `Ⅷ` in this letter |

Do not mint leftover `Ⅷ` in this letter. Epic `#522` stays OPEN.
Do not merge this letter to `main` without the leftover-`Ⅵ` stack.
