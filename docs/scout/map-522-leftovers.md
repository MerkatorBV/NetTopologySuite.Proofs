# Map — #522 leftovers (after wrap-up)

A wayfinder map. Charted 2026-08-30. This is **not** a second copy of
[`map-522.md`](map-522.md) and it is **not** a `wayfinder:map` GitHub
issue. The epic comment stays the design of record. #589 stays closed.

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. New leftover ids are repeated
> `Ⅰ` marks (`Ⅰ`, `ⅠⅠ`, `ⅠⅠⅠ`, …), not `522-*` letters and not
> `Ⅱ`. Do not remint ADR-0004. Do not mint GitHub children from this map.

topics: relate
claimId: none
witness: none

## Destination

**Name the residue so the next `/implement` cannot steal a closed
`522-*` letter or invent `522-n`.**

The #522 honesty ask and wired-triangle bar 1 → bar 2 are done
([`522-closing-summary.md`](522-closing-summary.md)). What remains is
unnamed proof work, leftover `Ⅰ`, #67 / sibling residue, or owner
sign-off on the epic.

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

**Leftover ids.** Repeated `Ⅰ` marks (`Ⅰ`, `ⅠⅠ`, `ⅠⅠⅠ`, …), not
`522-*` letters. `Ⅰ` is the T-junction / partial-edge kiss. `ⅠⅠ` is
the obtuse-at-v certificate. Do not swap them. Next unused is `ⅠⅠⅠ`
— do not assign it here.

## Leftover table

Parks follow ADR-0002 (`CONTEXT.md`): sequencing / research / technique.
Value and priority are orthogonal.

| Id | Leftover | Kind | Park | Status | Do not |
|---|---|---|---|---|---|
| `Ⅰ` | T-junction / partial-edge kiss | #522-adjacent | research | Named. Chart: [`map-tjunction-cert.md`](map-tjunction-cert.md). Grill: [`map-tjunction-grill.md`](map-tjunction-grill.md). Finding `RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`. Pair `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)`. Bar 1 in flight #609; not CONTEXT Bar 1. | restage the detector; steal `522-j` / `522-m`; bucket obtuse under `Ⅰ`; treat #609 as CONTEXT Bar 1 |
| — | TouchEdge exclusivity vs the four gtri predicates | #522-adjacent | technique | Named leftover, no numeral. Carved by #597 (`522-a-touch-edge-carve`), not proved. | treat the carve as exclusivity; remint frozen anchors |
| — | Classifier fill remints (`aa_matrix_*` → `*_ogc`) | #522-adjacent | sequencing | Unnamed. Four shared pins; disjoint blocked by `pat_disjoint`. Not `522-f`. | remint in a harness letter; steal `522-f` / `522-d` / `522-h` |
| `ⅠⅠ` | Obtuse-at-v certificate | #522-adjacent | research | Named. Finding `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`. Pair `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)`. Shared vertex; cone `side_dot = 0`. | invent the detector; steal `522-m`; bucket under `Ⅰ` |
| — | Nine-cell `geom_de9im_pointset` | #67 / ticket 11 | technique | ADR-0003 half-open leftover. | mint as a #522 child |
| — | Full RelateNG noding + Touches-vs-Share | #67 | sequencing | Off-dispatch `relate` already declines honestly. | mint as a #522 child |
| — | `F` vs not-computed on `CURVE_RELATE_MATRIX` | sibling #523 | sequencing | Ticket 11 precondition 3. | steal a closed `522-*` letter |
| — | Empty/empty `relate` | parked on #522 | sequencing | Declines today; ISO 13249-3 if revisited. | treat as a decline bug |

## Decisions so far

- Honesty sentinel — #530.
- Wired bar 1 — #580 #581 #582 + contains bridge #586.
- Completeness false — #583 / #584. Certificates not invented.
- Bar 2 gtri cells — #587 #592 #593 #594. Pins not reminted.
- Wire token + harness — #588 + #595. Decline vector is the T-junction.
- Wrap-up — #596. Owner sign-off still required.
- #567 DoD met; TouchEdge exclusivity carved on `main` via #597, not proved.
- #589 wayfinder PR stays closed.
- Leftover ids switch to repeated `Ⅰ` marks. `Ⅰ` = T-junction kiss.
  `ⅠⅠ` = obtuse-at-v. `522-n` is not minted.
- Leftover `Ⅰ` grill — [`map-tjunction-grill.md`](map-tjunction-grill.md).
  Spec holds. #609 is faithful. CONTEXT Bar 1 is not met
  (`RelateNGDisjoint.v : tjunction_pair_unsupported` on `main`).

## Fog

- **Owner sign-off on #522** is paperwork on the epic, not a leftover
  proof. Closing summary: [`522-closing-summary.md`](522-closing-summary.md).
- **Remint order** if asked: disjoint is the sharpest (Qex already
  compiled); contains / touch / overlap follow the same pointer pattern
  and the same shared-pin caution.
- **Two certificates are two leftovers.** T-junction is `Ⅰ`. Obtuse-at-v
  is `ⅠⅠ`.
- **`ⅠⅠⅠ`** is unused. Ask before assigning it.

## Frontier

Leftovers `Ⅰ` and `ⅠⅠ` are named. This map does not invent either
detector. `/implement` of either is a later letter.

```
#522 honesty + wired bar 1/2 ════════════════════ done (#596 wrap-up)

Ⅰ ──────── T-junction / partial-edge kiss ── research ── finding #577
           grill map-tjunction-grill.md ── not CONTEXT Bar 1
ⅠⅠ ─────── obtuse-at-v certificate ── research ── finding #584
unnamed ── TouchEdge exclusivity ── technique ── carve #597 on main
unnamed ── fill remints (4 shared pins) ── sequencing ── not 522-f

#67 / 11 ── geom_de9im_pointset · noding · Touches-vs-Share
#523 ────── F vs not-computed
parked ──── empty/empty

522-n ── not minted
ⅠⅠⅠ ──── unused ── ask before assigning
```
