# Leftover `Ⅹ` / `522-n` — classify the swap nest pair

**Type:** task
**Blocked by:** leftover `Ⅸ` (ticket 32 / PR #645)
**Spec:** [`map-swap-nest-cert.md`](../../map-swap-nest-cert.md)
**claimId:** `522-n` · **GitHub:** none · **witness:** `522-n-swap-cex`
**board:** leftover-Ⅹ

## Ask

Classify the leftover-`Ⅸ` completeness residue
A = `(0,0)(4,0)(1,1)`, B = `(0,0)(4,0)(0,4)` as leftover `Ⅹ`.
Mint board claimId `522-n` as that leftover (owner override of
ADR-0004 for this letter only). Do not remint `nest_b` /
`inside_b` / `contains_b` / `touch_edge_b`. Do not emit
`2FFFFFFF2` or `FF2F11212`. Do not steal `522-j` / `522-m`.
Do not mint leftover `Ⅺ`. Do not merge leftover
`Ⅵ` / leftover `Ⅶ` / leftover `Ⅷ` / leftover `Ⅸ` unless asked.

## Resolution

Classified. Detector `RelateNGCore.v : swap_nest_b` is both CCW plus
some shared edge plus some A vertex strictly interior to B — not
a remint of `nest_b`. Classifier reaches `TPR_SwapNest`
(`RelateNGNestCex.v : swap_pair_swapnest`;
`RelateNGTouchSwapNest.v : triangle_pair_regime_swapnest`). Fill
stays `im_unsupported`. `classify_triangle_pair` arm is `True`.
Epic #522 stop is QED ∨ QEX
(`RelateNGTouchSwapNest.v : triangle_pair_regime_ccw_stop`),
discharged QEX on an unnamed identical CCW pair
(`RelateNGNestCex.v : unnamed_ccw_pair_unsupported`). Leftover
`Ⅹ` itself is QED (`RelateNGTouchSwapNest.v : leftover_x_qed_or_qex`).

Do not remint leftover
`Ⅰ` / `Ⅱ` / `Ⅲ` / `Ⅳ` / `Ⅴ` / `Ⅵ` / `Ⅶ` / `Ⅷ` / `Ⅸ` /
`522-j` / `522-m` / `522-f` / `522-i`. Do not mint leftover `Ⅺ`.
