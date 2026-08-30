# Map — #522 leftovers (after wrap-up)

A wayfinder map. Charted 2026-08-30. This is **not** a second copy of
[`map-522.md`](map-522.md) and it is **not** a `wayfinder:map` GitHub
issue. The epic comment stays the design of record. #589 stays closed.

> **Do not mint.** This map does not mint claimIds, GitHub children, or
> leftover letters. Official unused letter: **`522-n`** — **one** letter.
> Ask before assigning it to **exactly one** leftover. Do not bucket
> three leftovers under `522-n`. Do not steal closed letters
> (`522-a` … `522-m`). Do not remint ADR-0004.

topics: relate
claimId: none
witness: none

## Destination

**Name the residue so the next `/implement` cannot steal a letter.**

The #522 honesty ask and wired-triangle bar 1 → bar 2 are done
([`522-closing-summary.md`](522-closing-summary.md)). What remains is
either unnamed proof work, #67 / sibling residue, or owner sign-off on
the epic. None of that is takeable until the owner picks one leftover
and mints (or signs off).

## Notes

**#522 children.** Wrap-up #596 closed #576 and #578. Harness #595
closed #575. Carve #597 is **ready, not on `main`**: it closes #567
without proving TouchEdge exclusivity. After #597 lands, every child
is closed. The epic stays open for owner sign-off.

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

## Leftover table (unnamed)

Parks follow ADR-0002 (`CONTEXT.md`): sequencing / research / technique.
Value and priority are orthogonal. **claimId is blank until the owner
mints.**

| Leftover | Kind | Park | Why unnamed | Do not |
|---|---|---|---|---|
| TouchEdge exclusivity vs the four gtri predicates | #522-adjacent | technique | Statement exists; frozen shared-edge vocab is not a cheap `nra` consequence. Carved by #597 (`522-a-touch-edge-carve`), not proved. | treat the carve as exclusivity; remint frozen anchors |
| Classifier fill remints (`aa_matrix_*` → `*_ogc`) | #522-adjacent | sequencing | Four pointer flips, one shared pin each. Disjoint remint is blocked by `pat_disjoint` (EI=EB=F). Not `522-f`. | remint in a harness letter; steal `522-f` / `522-d` / `522-h` |
| T-junction certificate | #522-adjacent | research | Completeness recorded the finding (`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`) and stopped. Pair `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)`. | invent the certificate; steal `522-j` / `522-m` |
| Obtuse-at-v certificate | #522-adjacent | research | Filtered-completeness still false (`522-m`). Pair `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)`. Separate leftover from T-junction. | bucket with T-junction under one letter |
| Nine-cell `geom_de9im_pointset` | #67 / ticket 11 | technique | ADR-0003 half-open leftover. Bar-2 gtri cells are not this capstone. | mint as a #522 child |
| Full RelateNG noding + Touches-vs-Share | #67 | sequencing | Off-dispatch `relate` already declines honestly. | mint as a #522 child |
| `F` vs not-computed on `CURVE_RELATE_MATRIX` | sibling #523 | sequencing | Ticket 11 precondition 3. | steal a #522 letter |
| Empty/empty `relate` | parked on #522 | sequencing | Declines today; ISO 13249-3 if revisited. Epic out-of-scope unless the owner reopens it. | treat as a decline bug |

`522-n` may be given to **one** row in the first four, after the owner
asks. The other three stay unnamed or get **new** letters / a new child
of #522 — never a closed letter.

## Decisions so far

- Honesty sentinel — #530.
- Wired bar 1 — #580 #581 #582 + contains bridge #586.
- Completeness false — #583 / #584. Certificates not invented.
- Bar 2 gtri cells — #587 #592 #593 #594. Pins not reminted.
- Wire token + harness — #588 + #595. Decline vector is the T-junction.
- Wrap-up — #596. Owner sign-off still required.
- #567 DoD met; TouchEdge exclusivity carved (ready #597), not proved.
- #589 wayfinder PR stays closed.

## Fog

- **Owner sign-off on #522** is paperwork on the epic, not a leftover
  proof. Closing summary: [`522-closing-summary.md`](522-closing-summary.md).
- **Which leftover is first** is an owner call. This map does not pick.
- **Remint order** if asked: disjoint is the sharpest (Qex already
  compiled); contains / touch / overlap follow the same pointer pattern
  and the same shared-pin caution.
- **Two certificates are two leftovers.** T-junction ≠ obtuse-at-v.

## Frontier

Empty for `/implement` until the owner (1) signs off #522 or (2) names
exactly one leftover and a letter.

```
#522 honesty + wired bar 1/2 ════════════════════ done (#596 wrap-up)

unnamed ── TouchEdge exclusivity ── technique ── carve #597 ready
unnamed ── fill remints (4 shared pins) ── sequencing ── not 522-f
unnamed ── T-junction certificate ── research ── finding #577
unnamed ── obtuse-at-v certificate ── research ── finding #584

#67 / 11 ── geom_de9im_pointset · noding · Touches-vs-Share
#523 ────── F vs not-computed
parked ──── empty/empty

522-n ── one unused letter ── ask before assigning to exactly one row
```
