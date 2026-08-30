# Leftover `Ⅵ` — classify the same-cone pair

**Type:** task
**Blocked by:** leftover `Ⅴ` (ticket 28 / PR #638)
**Spec:** [`map-same-cone-cert.md`](../../map-same-cone-cert.md)
**claimId:** `Ⅵ` · **GitHub:** none · **witness:** `Ⅵ-same-cone-cex`

## Ask

Classify the leftover-`Ⅴ` completeness residue
A = `(0,0)(2,0)(0,2)`, B = `(0,0)(3,1)(1,3)` as leftover `Ⅵ`.
Do not remint `cone_separates_b` / `mixed_cone_vertex_b` /
`touch_obtuse_vertex_b` / `overlap_b`. Do not emit `2FFF1FFF2` or
`FFFF1FFF2`. Do not steal `522-j` / `522-m`. Do not mint leftover
`Ⅶ`. Do not merge leftover `Ⅴ` unless asked.

## Resolution

Classified. Detector `RelateNGCore.v : same_cone_vertex_b` is
both-strict-pos plus `negb` of both cones and of
`mixed_cone_from_v`. Classifier reaches `TPR_SameCone`
(`RelateNGUnnamedCex.v : same_cone_pair_samecone`;
`RelateNGTouchSameCone.v : triangle_pair_regime_samecone`). Fill
stays `im_unsupported`. `classify_triangle_pair` arm is `True`.
Epic #522 stop is QED ∨ QEX
(`RelateNGTouchSameCone.v : triangle_pair_regime_ccw_stop`),
discharged QEX on an unnamed lens
(`RelateNGUnnamedCex.v : unnamed_ccw_pair_unsupported`). Leftover
`Ⅵ` itself is QED (`RelateNGTouchSameCone.v : leftover_vi_qed_or_qex`).

Do not remint leftover
`Ⅰ` / `Ⅱ` / `Ⅲ` / `Ⅳ` / `Ⅴ` / `522-j` / `522-m` / `522-f` /
`522-i`. Do not mint `522-n` / `Ⅶ`.
