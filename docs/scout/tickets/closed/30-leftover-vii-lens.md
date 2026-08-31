# Leftover `Ⅶ` — classify the lens pair

**Type:** task
**Blocked by:** leftover `Ⅵ` (ticket 29 / PR #640)
**Spec:** [`map-lens-cert.md`](../../map-lens-cert.md)
**claimId:** `Ⅶ` · **GitHub:** none · **witness:** `Ⅶ-lens-cex`

## Ask

Classify the leftover-`Ⅵ` completeness residue
A = `(0,0)(3,0)(0,3)`, B = `(2,-1)(2,2)(-1,2)` as leftover `Ⅶ`.
Do not remint `segments_proper_cross` / `overlap_b` /
`same_cone_vertex_b`. Do not emit `2FFF1FFF2` or
`FFFF1FFF2`. Do not steal `522-j` / `522-m`. Do not mint leftover
`Ⅷ`. Do not merge leftover `Ⅴ` / leftover `Ⅵ` unless asked.

## Resolution

Classified. Detector `RelateNGCore.v : lens_edges_cross_b` is a
boolean proper-cross of some A-edge with some B-edge
(`opposite_sides_b` both ways) — not a remint of the noding-lane
Prop `segments_proper_cross`. Classifier reaches `TPR_Lens`
(`RelateNGUnnamedCex.v : lens_pair_lens`;
`RelateNGTouchLens.v : triangle_pair_regime_lens`). Fill
stays `im_unsupported`. `classify_triangle_pair` arm is `True`.
Epic #522 stop is QED ∨ QEX
(`RelateNGTouchLens.v : triangle_pair_regime_ccw_stop`),
discharged QEX on an unnamed inside pair
(`RelateNGNestCex.v : unnamed_ccw_pair_unsupported`). Leftover
`Ⅶ` itself is QED (`RelateNGTouchLens.v : leftover_vii_qed_or_qex`).

Do not remint leftover
`Ⅰ` / `Ⅱ` / `Ⅲ` / `Ⅳ` / `Ⅴ` / `Ⅵ` / `522-j` / `522-m` / `522-f` /
`522-i`. Do not mint `522-n` / `Ⅷ`.
