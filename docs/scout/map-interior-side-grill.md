# Grill — leftover `Ⅳ` (interior-side stem)

A grilling record. Charted 2026-08-30. This is **not** leftover `Ⅰ`,
**not** leftover `Ⅱ`, **not** leftover `Ⅲ`, and **not** a second copy
of [`map-interior-side-cert.md`](map-interior-side-cert.md) (#629). It
does **not** invent a 12-tuple. It does **not** invent a
side-distinguishing detector. It does **not** remint
`RelateNGCore.v : touch_onesided_t_b`.

> Research chart: [`map-interior-side-cert.md`](map-interior-side-cert.md)
> (#629). Leftover `Ⅲ` compile is #628. This grill answers leftover
> `Ⅳ` against that compiled tree: named; uninhabited on the compiled
> tree; the xor is already a `Ⅲ∨Ⅳ` configuration class with one
> exterior witness; `overlap_b` may steal same-side stems. CONTEXT
> Bar 1 cannot apply. `/implement` compiles a residue witness or
> proves the residue empty. It does not write a second detector.

topics: relate
claimId: Ⅳ
witness: none

## Destination

**Verify leftover `Ⅳ` against the leftover-`Ⅲ` compile and against
CONTEXT.** Name what holds. Park what does not. Do not invent a
12-tuple. Do not invent a side-distinguishing detector.

## Verdict

The family is named. There is **no** compiled leftover-`Ⅳ` 12-tuple.
The compiled one-sided pair is leftover `Ⅲ`
(`RelateNGComplete.v : onesided_t_pair_inhabits`) — exterior-side,
II empty (`RelateNGComplete.v : onesided_t_ii_empty`). The xor
(`RelateNGCore.v : touch_onesided_t_b`) is a `Ⅲ∨Ⅳ` configuration
class with that one exterior witness
(`RelateNGTouchOnesided.v : triangle_pair_regime_onesided`). It is
not side-aware. Ticket 22's leftover-`Ⅲ` bar is met. “Detector for
leftover `Ⅲ`” is not, and this grill does not make it one.

`overlap_b` sits earlier (`RelateNGCore.v : overlap_b`;
`RelateNGCore.v : triangle_pair_regime`). A same-side stem with a
strict-interior B-vertex and a strict-exterior B-vertex is leftover
`522-b`, not this leftover. The residue is same-side xor-true pairs
that miss `overlap_b` / `contains_b` / leftover `Ⅰ`. Whether that
residue is inhabited is **open**. Completeness stays false on leftover
`Ⅱ` (`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`).
CONTEXT **Bar 1** needs a classified leftover-`Ⅳ` pair and a
designated witness matrix. There is neither. Fill stays
`im_unsupported` (`RelateNGTouchOnesided.v : onesided_fill_still_unsupported`).
This is a **research park** (ADR-0002).

This grill does not mint a pair and call it the spec.

## Claims grilled live

### 1. No compiled leftover-`Ⅳ` pair on this tree

**Confirmed.** The only onesided pair in `RelateNGComplete.v` is
leftover `Ⅲ`, exterior-side
(`RelateNGComplete.v : onesided_t_pair_inhabits`). There is no
interior-side 12-tuple. The other compiled leftovers are leftover `Ⅰ`
(`RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial`)
and leftover `Ⅱ`
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
`classified_hard_pairs` is four rows. None of those is this family.

### 2. Leftover `Ⅲ` is the opposite-side witness, not this leftover

**Confirmed.**

| Finding | Leftover | Why not `Ⅳ` |
|---|---|---|
| `RelateNGComplete.v : onesided_t_pair_inhabits` | `Ⅲ` | Exterior-side. Contact `(1,0)` on A's base `y = 0`. II empty (`RelateNGComplete.v : onesided_t_ii_empty`). There is no `onesided_t_bb_dim0`. |
| `RelateNGTouchPartialEdge.v : triangle_pair_regime_touchpartial` | `Ⅰ` | Mutual. Same-side sliver. II = 2, BB = 1. |
| `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction` | `Ⅱ` | Shared vertex; cone `side_dot = 0`. |

### 3. The xor is `Ⅲ∨Ⅳ`, not a leftover-`Ⅳ` detector

**Confirmed.** `RelateNGCore.v : touch_onesided_t_b` is
`xorb (some_vertex_on_open_edges A B) (some_vertex_on_open_edges B A)`.
No side test. True on leftover `Ⅲ`. Would be true on leftover `Ⅳ`
the moment someone writes the coords. Classifier order
(`RelateNGCore.v : triangle_pair_regime`) emits `TPR_TouchOnesided`
for any xor-true pair that missed the earlier arms. Do **not** remint
the xor. A side-distinguishing boolean, if asked later, tests the
side of the supporting line **after** the xor.

### 4. `overlap_b` may steal same-side stems

**Confirmed.** `RelateNGCore.v : overlap_b` needs a B-vertex with
`0 < gtri A` and a B-vertex with `gtri A < 0`, plus a vertex of A
strictly exterior to B. A same-side stem can fire that arm. Those
pairs are leftover `522-b`
(`RelateNGComplete.v : classified_overlap_pair`), not leftover `Ⅳ`.
The residue is same-side one-sided pairs that miss this arm.

| Detector | Why it is the wrong tool for leftover `Ⅳ` |
|---|---|
| `touch_edge_b` | `RelateNGCore.v : shares_edge_b` is endpoint-pair equality. A T is not a full shared edge. |
| `contains_b` | Needs `0 < gtri A` at every B-vertex. A stem on the supporting line has `gtri = 0`. |
| `overlap_b` | May fire. Those pairs are leftover `522-b`. |
| `separated_b` | A supporting-edge separator is a disjoint witness. A T is contact. |
| `touch_vertex_b` | Needs a shared vertex and `RelateNGCore.v : cone_separates_b`. This family has **no** shared vertex. |
| `touch_partial_edge_b` | Mutual. Leftover `Ⅰ`. This family is one-sided. |
| `touch_onesided_t_b` | True on leftover `Ⅲ` and leftover `Ⅳ`. No side test. |

### 5. CONTEXT Bar 1 is not applicable

**Confirmed miss — not a failed bar, an absent subject.** Bar 1 needs
a classified leftover-`Ⅳ` pair and a designated witness matrix.
There is no leftover-`Ⅳ` pair. The leftover-`Ⅲ` constructor is
already on `im_unsupported`. `classify_triangle_pair` arm for
`TPR_TouchOnesided` is `True` — leftover `Ⅰ` honesty, not CONTEXT
Bar 1. Nothing that mentions `TPR_TouchOnesided` may be proved
through `classify_triangle_pair`. Decline golden is leftover `Ⅱ`.
Do not emit `FFFFFFFFF`. Do not emit `FFFF1FFF2` or `FF2F11212` on
`TPR_TouchOnesided` — leftover `Ⅲ` looks like areal Touches,
leftover `Ⅳ` looks like overlap. The fill token is the only thing
keeping those families from mixing.

### 6. Uninhabited on the compiled tree

**Confirmed park — compiled tree, not geometry.** There is no
published leftover-`Ⅳ` pair. Whether a same-side stem reaches
`TPR_TouchOnesided` is open. Emptiness of that residue is allowed
and would mean every same-side one-sided T is already
`overlap_b` / `contains_b` / leftover `Ⅰ`. This grill does not mint
coordinates and call them the spec.

## Parks (ADR-0002)

- **Research:** uninhabited on the compiled tree. No published
  leftover-`Ⅳ` compiled statement. Gate: a cex in
  `RelateNGComplete.v`, or a residue-empty theorem.
- **Sequencing:** side-distinguishing detector, constructor split,
  fill. All gated on the research park **and** an owner ask. The xor
  is already compiled. Do not invent a second detector as the first
  implement letter.
- **Technique:** none. There is no leftover-`Ⅳ` detector statement
  to grill.

## Not this leftover

Not leftover `Ⅰ` / #609. Not leftover `Ⅱ` / #611. Not leftover
`Ⅲ` / #628. Not #570 overlap. Not #572 TouchVertex. Not line×line
IB. Not a remint of `aa_matrix_*`. Not a remint of
`touch_onesided_t_b`. Do not mint `522-n`. Do not mint `Ⅴ`. Do not
steal `522-j` / `522-m` / `522-f` / `522-i` / `522-b`.

## If `/implement Ⅳ` is asked

Read [`spec-interior-side.md`](spec-interior-side.md). First compile
a residue witness or prove the residue empty (ticket 26). Do not
invent a 12-tuple in prose and treat it as compiled. Do not remint
the xor. Do not remint the fill. Completeness stays false on leftover
`Ⅱ` until proved.

## Decisions so far

- Family named — #629 / [`map-interior-side-cert.md`](map-interior-side-cert.md).
- Leftover `Ⅲ` compile — #628 /
  `RelateNGTouchOnesided.v : triangle_pair_regime_onesided`.
  `Ⅲ∨Ⅳ` xor, one exterior witness, fill token, completeness still
  `Ⅱ`.
- This grill — named; uninhabited on the compiled tree; Bar 1 not
  applicable; residue inhabited-or-empty is open (ticket 26).
- Spec / tickets — [`spec-interior-side.md`](spec-interior-side.md);
  scout 23–25 closed; ticket 26 takeable.

## Frontier

```
family named ── #629 ── map-interior-side-cert.md
     no compiled leftover-Ⅳ 12-tuple
     this grill ── confirmed against the leftover-Ⅲ compile

Ⅳ ── research #629 ── grill (this file) ── spec-interior-side.md
     tickets 23–25 closed ── 26 compile residue or empty takeable
     xor already Ⅲ∨Ⅳ ── do not invent a detector
     /implement Ⅳ starts at ticket 26

Ⅰ ── mutual same-side sliver ── #609 ── not this leftover
Ⅱ ── obtuse-at-v ── #611 ── live completeness cex
Ⅲ ── exterior-side stem ── #628 ── Ⅲ∨Ⅳ xor, one exterior witness

522-n ── not minted
Ⅴ ── unused ── ask before assigning
```
