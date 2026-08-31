# Leftover `Ⅸ` — classify the nest pair

**Type:** task
**Blocked by:** leftover `Ⅷ` (ticket 31 / PR #644)
**Spec:** [`map-nest-cert.md`](../../map-nest-cert.md)
**claimId:** `Ⅸ` · **GitHub:** none · **witness:** `Ⅸ-nest-cex`

## Ask

Classify the leftover-`Ⅷ` completeness residue
A = `(0,0)(4,0)(0,4)`, B = `(0,0)(4,0)(1,1)` as leftover `Ⅸ`.
Do not remint `touch_edge_b` / `contains_b` / `overlap_b` /
`inside_b`. Do not emit `2FFFFFFF2` or `FF2F11212`. Do not steal
`522-j` / `522-m`. Do not mint leftover `Ⅹ`. Do not merge leftover
`Ⅵ` / leftover `Ⅶ` / leftover `Ⅷ` unless asked.

## Resolution

Classified. Detector `RelateNGCore.v : nest_b` is both CCW plus
some shared edge plus some B vertex strictly interior to A — not
a remint of `touch_edge_b`. Classifier reaches `TPR_Nest`
(`RelateNGNestCex.v : nest_pair_nest`;
`RelateNGTouchNest.v : triangle_pair_regime_nest`). Fill
stays `im_unsupported`. `classify_triangle_pair` arm is `True`.
Epic #522 stop is QED ∨ QEX
(`RelateNGTouchNest.v : triangle_pair_regime_ccw_stop`),
discharged QEX on an unnamed swapped nest pair
(`RelateNGNestCex.v : unnamed_ccw_pair_unsupported`). Leftover
`Ⅸ` itself is QED (`RelateNGTouchNest.v : leftover_ix_qed_or_qex`).

Do not remint leftover
`Ⅰ` / `Ⅱ` / `Ⅲ` / `Ⅳ` / `Ⅴ` / `Ⅵ` / `Ⅶ` / `Ⅷ` / `522-j` / `522-m` / `522-f` /
`522-i`. Do not mint `522-n` / `Ⅹ`.
