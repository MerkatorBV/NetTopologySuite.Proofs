# Map — #522 leftovers (after wrap-up)

A wayfinder map. Charted 2026-08-30. This is **not** a second copy of
[`map-522.md`](map-522.md) and it is **not** a `wayfinder:map` GitHub
issue. The epic comment stays the design of record. #589 stays closed.

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are precomposed
> Roman numerals (`Ⅰ`, `Ⅱ`, `Ⅲ`, `Ⅳ`, …), not `522-*` letters
> and not repeated `Ⅰ` marks. Do not remint ADR-0004. Do not mint
> GitHub children from this map.

topics: relate
claimId: none
witness: none

## Destination

**Name the residue so the next `/implement` cannot steal a closed
`522-*` letter or invent `522-n`.**

The #522 honesty ask and wired-triangle bar 1 → bar 2 are done
([`522-closing-summary.md`](522-closing-summary.md)). What remains is
**named leftover work** (`Ⅰ` sliver bar 1; `Ⅱ` live cex, no
detector; `Ⅲ∨Ⅳ` xor with two compiled witnesses; `Ⅳ` residue pair),
#67 / sibling residue, or owner sign-off on the epic. After this
letter the residue is not “unnamed proof work, leftover `Ⅰ`.”

## Notes

**#522 children.** Wrap-up #596 closed #576 and #578. Harness #595
closed #575. Carve #597 is **on `main`**: it closed #567 without
proving TouchEdge exclusivity. Every child is closed. The epic stays
open for owner sign-off.

**Shared classifier pins.** `triangle_pair_fill` and `rect_pair_fill`
share `aa_matrix_disjoint` (FFFFFFFFF), `aa_matrix_partial_overlap`
(2FFF1FFF2), `aa_matrix_contains` (2FFFFFFF2), `aa_matrix_touch_vertical`
(FFFF1FFF2). The OGC gtri names (`*_ogc`) are **separate** definitions.
A remint of a shared pin moves the rect lane too. `DE9IM.v` `pat_disjoint`
rejects FF2FF1212 (`RelateNGDisjointCells.v : ogc_disjoint_fill_not_im_disjoint`).

**Frozen anchors.** `touch_int_ext_exclusion`,
`touch_triangle_ii_separation_not_unconditional`,
`triangles_touch_on_shared_edge`. Ray parity enters only via ADR-0003.

**#589.** Closed / red. Do not merge or reopen. This file is the leftovers
chart; `map-522.md` stays the child-ticket freshness layer.

**Leftover ids.** Precomposed Roman numerals (`Ⅰ`, `Ⅱ`, `Ⅲ`,
`Ⅳ`, …), not `522-*` letters and not repeated `Ⅰ` marks. `Ⅰ` is
the mutual vertex-in-open-edge sliver (II = 2, BB = 1). `Ⅱ` is the
obtuse-at-v certificate (live completeness cex; no detector). `Ⅲ` is
the exterior-side one-sided T (compiled pair; II empty). `Ⅳ` is the
interior-side stem (compiled residue pair; II nonempty). The xor
(`RelateNGCore.v : touch_onesided_t_b`) is a `Ⅲ∨Ⅳ` configuration
class with two compiled witnesses; it is not a leftover-`Ⅲ`
detector. Completeness-false-on-`Ⅱ` is true: `Ⅱ` has no detector.
Do not swap them. Next unused is `Ⅴ` — ask before assigning.

## Leftover table

Parks follow ADR-0002 (`CONTEXT.md`): sequencing / research / technique.
Value and priority are orthogonal.

| Id | Leftover | Kind | Park | Status | Do not |
|---|---|---|---|---|---|
| `Ⅰ` | Mutual vertex-in-open-edge sliver | #522-adjacent | research | Bar 1 landed. Chart: [`map-tjunction-cert.md`](map-tjunction-cert.md). Headline `RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`. Pair `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)`. Compiled pair is II = 2, BB = 1 — a sliver, not a kiss. Fill stays `im_unsupported`. | steal `522-j` / `522-m` / `522-f`; remint fills; bucket obtuse under `Ⅰ`; mint `522-n` |
| — | TouchEdge exclusivity vs the four gtri predicates | #522-adjacent | technique | Named leftover, no numeral. Carved by #597 (`522-a-touch-edge-carve`), not proved. | treat the carve as exclusivity; remint frozen anchors |
| — | Classifier fill remints (`aa_matrix_*` → `*_ogc`) | #522-adjacent | sequencing | Unnamed. Four shared pins; disjoint blocked by `pat_disjoint`. Not `522-f`. | remint in a harness letter; steal `522-f` / `522-d` / `522-h` |
| `Ⅱ` | Obtuse-at-v certificate | #522-adjacent | research | Named. Finding `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`. Pair `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)`. Shared vertex; cone `side_dot = 0`. No detector. Live completeness cex. | invent the detector; steal `522-m`; bucket under `Ⅰ` |
| `Ⅲ` | Exterior-side one-sided T | #522-adjacent | research | Exterior-side pair compiled. Headline `RelateNGTouchOnesided.v : triangle_pair_regime_onesided`. Pair `(0,0)(2,0)(0,1)` vs `(1,0)(1/2,-1)(3/2,-1)`. Contact `(1,0)` is collinear with A's base `y = 0`. II empty (`RelateNGComplete.v : onesided_t_ii_empty`) — not a compiled BB-dim-0 cell; there is no `onesided_t_bb_dim0`. Xor is `Ⅲ∨Ⅳ` with two compiled witnesses. Fill token is load-bearing (`im_unsupported`). `classify_triangle_pair` arm is `True` — leftover `Ⅰ` honesty, not CONTEXT Bar 1. Completeness stays false on leftover `Ⅱ`. | remint leftover `Ⅰ`; invent leftover `Ⅱ`; remint leftover `Ⅳ`; emit `FFFFFFFFF` / `FFFF1FFF2` / `FF2F11212`; claim Bar 1; claim a leftover-`Ⅲ` detector; mint `522-n` / `Ⅴ` |
| `Ⅳ` | Interior-side stem | #522-adjacent | research | Residue pair compiled. Headline `RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`. Pair `(0,0)(2,0)(0,1)` vs `(1,0)(5/4,1/4)(3/4,1/4)`. Same A and contact as leftover `Ⅲ`; remaining B vertices sit on the interior side of `y = 0` (`RelateNGComplete.v : interior_side_same_side`). `overlap_b` false (`RelateNGComplete.v : interior_side_overlap_b_false`) — no exterior B-vertex. II nonempty (`RelateNGComplete.v : interior_side_ii_nonempty`). Inhabitance `RelateNGComplete.v : interior_side_pair_inhabits`. Boolean is not side-aware. Looks like overlap; leftover `Ⅲ` looks like areal Touches. One constructor, one `True` arm, one `im_unsupported` — fill token keeps those families from mixing. Not CONTEXT Bar 1. | invent a side-distinguishing detector; remint the fill; steal leftover `Ⅲ`; emit `FFFFFFFFF` / `FFFF1FFF2` / `FF2F11212`; claim Bar 1; mint `522-n` / `Ⅴ` |
| — | Nine-cell `geom_de9im_pointset` | #67 / ticket 11 | technique | ADR-0003 half-open leftover. | mint as a #522 child |
| — | Full RelateNG noding + Touches-vs-Share | #67 | sequencing | Off-dispatch `relate` already declines honestly. | mint as a #522 child |
| — | `F` vs not-computed on `CURVE_RELATE_MATRIX` | sibling #523 | sequencing | Ticket 11 precondition 3. | steal a closed `522-*` letter |
| — | Empty/empty `relate` | parked on #522 | sequencing | Declines today; ISO 13249-3 if revisited. | treat as a decline bug |

## Decisions so far

- Honesty sentinel — #530.
- Wired bar 1 — #580 #581 #582 + contains bridge #586.
- Completeness false — #583 / #584. Certificates not invented.
- Bar 2 gtri cells — #587 #592 #593 #594. Pins not reminted.
- Wire token + harness — #588 + #595. Decline vector was the T-junction;
  leftover `Ⅰ` moved `REGIME DECLINE` to obtuse-at-v.
- Wrap-up — #596. Owner sign-off still required.
- #567 DoD met; TouchEdge exclusivity carved on `main` via #597, not proved.
- #589 wayfinder PR stays closed.
- Leftover ids switch to precomposed Roman numerals. `Ⅰ` = mutual
  vertex-in-open-edge sliver. `Ⅱ` = obtuse-at-v. `Ⅲ` = exterior-side
  one-sided T (compiled pair; `Ⅲ∨Ⅳ` xor; two witnesses;
  fill token). `Ⅳ` = interior-side stem (compiled residue pair).
  Completeness still `Ⅱ`. `522-n` is not minted.

## Fog

- **Owner sign-off on #522** is paperwork on the epic, not a leftover
  proof. Closing summary: [`522-closing-summary.md`](522-closing-summary.md).
- **Remint order** if asked: disjoint is the sharpest (Qex already
  compiled); contains / touch / overlap follow the same pointer pattern
  and the same shared-pin caution.
- **`Ⅲ`** is compiled as an exterior-side stem
  (`RelateNGComplete.v : onesided_t_pair_inhabits`). The xor
  (`RelateNGTouchOnesided.v : triangle_pair_regime_onesided`) is
  `Ⅲ∨Ⅳ` with two compiled witnesses, not a leftover-`Ⅲ` detector.
  II empty is compiled. BB dim 0 is not. Fill stays `im_unsupported`.
- **`Ⅳ`** is the interior-side stem. Residue pair compiled
  (`RelateNGComplete.v : interior_side_pair_inhabits`;
  `RelateNGTouchOnesided.v : triangle_pair_regime_interior_side`).
  Chart: [`map-interior-side-cert.md`](map-interior-side-cert.md).
  Grill: [`map-interior-side-grill.md`](map-interior-side-grill.md).
  Spec: [`spec-interior-side.md`](spec-interior-side.md). Ticket 26
  closed. Fill stays `im_unsupported`. Next unused is `Ⅴ` — ask
  before assigning.

## Frontier

Leftover `Ⅰ` bar 1 is landed. Leftover `Ⅱ` is still named only.
Leftover `Ⅲ` and leftover `Ⅳ` are the two compiled witnesses of
a `Ⅲ∨Ⅳ` xor; fill stays `im_unsupported`. Completeness still `Ⅱ`.

```
#522 honesty + wired bar 1/2 ════════════════════ done (#596 wrap-up)

Ⅰ ──────── mutual vertex-in-open-edge sliver ── bar 1 ── TPR_TouchPartialEdge
Ⅱ ─────── obtuse-at-v certificate ── research ── finding #584 (live cex)
Ⅲ∨Ⅳ xor ── two witnesses ── TPR_TouchOnesided (fill token)
Ⅳ ───── interior-side stem ── residue pair ── TPR_TouchOnesided (fill token)
unnamed ── TouchEdge exclusivity ── technique ── carve #597 on main
unnamed ── fill remints (4 shared pins) ── sequencing ── not 522-f

#67 / 11 ── geom_de9im_pointset · noding · Touches-vs-Share
#523 ────── F vs not-computed
parked ──── empty/empty

522-n ── not minted
Ⅴ ── unused ── ask before assigning
```
