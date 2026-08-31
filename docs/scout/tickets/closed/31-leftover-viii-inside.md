# Leftover `Ⅷ` — classify the inside pair

**Type:** task
**Blocked by:** leftover `Ⅶ` (ticket 30 / PR #642)
**Spec:** [`map-inside-cert.md`](../../map-inside-cert.md)
**claimId:** `Ⅷ` · **GitHub:** none · **witness:** `Ⅷ-inside-cex`

## Ask

Classify the leftover-`Ⅶ` completeness residue
A = `(1,1)(2,1)(1,2)`, B = `(0,0)(4,0)(0,4)` as leftover `Ⅷ`.
Do not remint `contains_b` / `aa_matrix_contains` /
`lens_edges_cross_b`. Do not emit `2FFFFFFF2` or
`2FFF1FFF2`. Do not steal `522-j` / `522-m`. Do not mint leftover
`Ⅸ`. Do not merge leftover `Ⅵ` / leftover `Ⅶ` unless asked.

## Resolution

Classified. Detector `RelateNGCore.v : inside_b` is B CCW plus all
three A vertices strictly interior to B — not a remint of
`contains_b`. Classifier reaches `TPR_Inside`
(`RelateNGUnnamedCex.v : inside_pair_inside`;
`RelateNGTouchInside.v : triangle_pair_regime_inside`). Fill
stays `im_unsupported`. `classify_triangle_pair` arm is `True`.
Epic #522 stop is QED ∨ QEX
(`RelateNGTouchInside.v : triangle_pair_regime_ccw_stop`),
discharged QEX on an unnamed same-side shared-edge pair
(`RelateNGNestCex.v : unnamed_ccw_pair_unsupported`). Leftover
`Ⅷ` itself is QED (`RelateNGTouchInside.v : leftover_viii_qed_or_qex`).

Do not remint leftover
`Ⅰ` / `Ⅱ` / `Ⅲ` / `Ⅳ` / `Ⅴ` / `Ⅵ` / `Ⅶ` / `522-j` / `522-m` / `522-f` /
`522-i`. Do not mint `522-n` / `Ⅸ`.
