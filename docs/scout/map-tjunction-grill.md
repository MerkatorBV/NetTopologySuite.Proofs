# Grill — leftover `Ⅰ` (T-junction / partial-edge kiss)

A grilling record. Charted 2026-08-30. This is **not** leftover `ⅠⅠ`,
**not** a remint of `522-j` / `522-m` / `522-f`, and **not** a second
copy of [`map-tjunction-cert.md`](map-tjunction-cert.md). It does
**not** write a detector. It does **not** restage #609.

> Spec chart: [`map-tjunction-cert.md`](map-tjunction-cert.md) (#599).
> Bar 1 is in flight as #609 (CI green, not on `main`). Leftover `ⅠⅠ`
> is #611. This grill answers: leftover `Ⅰ` is specified and #609 is
> faithful to that spec; leftover `Ⅰ` is **not** CONTEXT Bar 1 and is
> **not** accepted as complete.

topics: relate
claimId: Ⅰ
witness: none

## Destination

**Verify leftover `Ⅰ` against the tree and against CONTEXT.** Name
what holds, park what does not. Do not invent a glossary term for
"classified regime, declined fill."

## Verdict

The #577 pair is leftover `Ⅰ`. On `main` it still declines
(`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`,
`RelateNGDisjoint.v : tjunction_pair_unsupported`). The wire is the
sentinel (`RelateNGOracleSurface.v : relate_tjunction_wire_unsupported`).
No named predicate holds
(`RelateNGDisjoint.v : relate_tjunction_pair_no_predicate`).

#609 (not on `main`) classifies the same 12-tuple as
`TPR_TouchPartialEdge` via a **mutual** vertex-in-open-edge boolean
and keeps the fill `im_unsupported`. That matches the spec chart:
detector, not a remint of `shares_edge_b`; new constructor; fill
unnamed; decline golden moves to obtuse-at-v; completeness stays
false. Frozen `shares_edge_b` is still endpoint-pair equality.

#609 is **not** CONTEXT Bar 1. CONTEXT Bar 1 is a classification
that is true geometry against the specified interior **and** a
designated witness matrix. #609 has neither a designated matrix nor
a real `classify_triangle_pair` arm (`True`, same denotation as
`TPR_Unsupported`). Leftover `Ⅰ` "bar 1" on that letter is
**witness-scoped regime reachability**. This grill does not invent
another bar name.

CONTEXT **Regime** selects one witness DE-9IM matrix. CONTEXT
**Decline** is `TPR_Unsupported` / the pair is not classified. #609
sits between those two entries. CONTEXT has no name for that
shape. This grill does not mint one.

## Claims grilled live

### 1. The spec pair is the compiled kiss

**Confirmed.** A = `(0,0)(2,0)(0,1)`, B = `(1,0)(3,0)(2,1)`. Both
CCW (`RelateNGComplete.v : tjunction_pair_both_ccw`). No shared
vertex. Bottoms collinear on `y = 0`. Not leftover `ⅠⅠ`
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
Not the #530 / #571 sentinel (`RelateNGComplete.v : classified_disjoint_pair`).
Not the #572 vertex-touch pin
(`RelateNGComplete.v : classified_touchvertex_pair`).

### 2. Every wired detector on `main` misses

**Confirmed.** Order (`RelateNGCore.v : triangle_pair_regime`):
`touch_edge_b` → `contains_b` → `overlap_b` → `separated_b` →
`touch_vertex_b` → `TPR_Unsupported`. No supporting edge
(`RelateNGDisjoint.v : tjunction_no_separator`). Hard pairs that do
classify stay classified (`RelateNGComplete.v : classified_hard_pairs`).

### 3. #609 is faithful and not a remint

**Confirmed from #609, not from this tree.** Mutual
`touch_partial_edge_b` (both directions). Constructor
`TPR_TouchPartialEdge`. Fill `im_unsupported`. After `touch_edge_b`
so a full shared edge still wins. False on the four hard pairs and
on obtuse-at-v. `shares_edge_b` not widened. `aa_matrix_*` not
reminted. Leftover `ⅠⅠ` not invented. `522-n` not minted.

Reusing `TPR_TouchEdge` would inherit `FFFF1FFF2`
(`aa_matrix_touch_vertical`) and fight the frozen TouchEdge leftover.
The new constructor is the honest owner call.

### 4. The wire stays a sentinel

**Confirmed.** On `main` and on #609,
`RelateNGOracleSurface.v : relate_tjunction_wire_unsupported` —
`UNSUPPORTED`, not a 9-char matrix
(`RelateNGOracleSurface.v : relate_tjunction_not_a_matrix`). After
#609 the harness golden for this pair is `REGIME TOUCH_PARTIAL` +
token `UNSUPPORTED`. Decline golden moves to leftover `ⅠⅠ`. Neither
letter emits `FFFFFFFFF`.

`tjunction_pair_unsupported` on #609 now means **fill**
`im_unsupported` after `TPR_TouchPartialEdge`. The name is
historical. The fact is still the sentinel.

### 5. Completeness stays false

**Confirmed.** Filtered retry
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`)
is leftover `ⅠⅠ`. Wiring leftover `Ⅰ` does not retire that finding.
Do not claim `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`
is obsolete.

### 6. CONTEXT Bar 1 is not met

**Confirmed miss.** `classify_triangle_pair` on #609 denotes
`TPR_TouchPartialEdge` as `True`. That is the same "no claim"
denotation as `TPR_Unsupported` (`RelateMatrixTriangle.v` on `main`
already uses `True` for the decline arm). A designated witness
matrix is not named. Interiors miss; the detector is collinear
open-edge, not `0 < gtri`. Leftover `Ⅰ` is therefore not CONTEXT
Bar 1 and not a 522-a exclusivity remint.

## Parks (ADR-0002)

- **Sequencing:** named fill for leftover `Ⅰ` (not a remint of
  `aa_matrix_touch_vertical` / `FFFF1FFF2`). Gate: a matrix that
  does not move the rect lane. Also: merge of #609 onto `main`.
- **Research:** geometric denotation of `TPR_TouchPartialEdge`
  (today `True`). Leftover `ⅠⅠ` (obtuse-at-v, chart #611). A
  one-sided dim-0 T if anyone wants it — that is `ⅠⅠⅠ`, unused,
  ask first.
- **Technique:** none. The leftover `Ⅰ` detector statement is
  compiled on #609.

## Not this leftover

Not leftover `ⅠⅠ`. Not #572 TouchVertex. Not line×line IB
(`RelateNodingLineLineMeet.v : segments_int_bnd_touches_ib_cell`).
Not a remint of `aa_matrix_*`. Not epic wrap-up. Do not mint
`522-n`. Do not mint `ⅠⅠⅠ`. Do not steal `522-j` / `522-m` /
`522-f` / `522-i`.

## If `/implement Ⅰ` is asked again

Do not restage #609. Do not pile onto #611 / #612 / a `508-*`
branch. Fill remint is a later leftover. Completeness stays false.

## Decisions so far

- Spec named — #599.
- Bar 1 in flight — #609 (CI green, not on `main`).
- Leftover `ⅠⅠ` named — #611.
- Leftover `Ⅰ` research refresh — #612.
- This grill — leftover `Ⅰ` is specified; #609 is faithful; CONTEXT
  Bar 1 is not met; leftover `Ⅰ` is not accepted as complete.

## Frontier

```
#577 finding ── triangle_pair_regime_incomplete_tjunction ── done

Ⅰ ── spec #599 ── bar 1 #609 ── this grill
     classified on #609; fill still sentinel
     not CONTEXT Bar 1

ⅠⅠ ── obtuse-at-v ── #611 ── not this leftover
fill remint ── sequencing ── not 522-f
classify denotation ── research ── True today

522-n ── not minted
ⅠⅠⅠ ──── unused
```
