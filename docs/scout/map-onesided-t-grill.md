# Grill — leftover `ⅠⅠⅠ` (one-sided / non-collinear vertex-in-open-edge T)

A grilling record. Charted 2026-08-30. This is **not** leftover `Ⅰ`,
**not** leftover `ⅠⅠ`, and **not** a second copy of
[`map-onesided-t-cert.md`](map-onesided-t-cert.md) (#614). It does
**not** invent a 12-tuple. It does **not** invent a detector. It does
**not** restage #609 / #611 / #614.

> Research chart: [`map-onesided-t-cert.md`](map-onesided-t-cert.md)
> (#614, not on `main` until that letter lands). Leftover `Ⅰ` bar 1
> is in flight as #609. Leftover `ⅠⅠ` is #611. This grill answers:
> leftover `ⅠⅠⅠ` is named and **uninhabited on the compiled tree**;
> CONTEXT Bar 1 cannot apply; `/implement` must compile a cex or prove
> emptiness before a detector.

topics: relate
claimId: ⅠⅠⅠ
witness: none

## Destination

**Verify leftover `ⅠⅠⅠ` against the tree and against CONTEXT.** Name
what holds, park what does not. Do not invent a glossary term for
"named family, no pair."

## Verdict

The family is named. There is **no** compiled 12-tuple. Completeness
stays false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). The two
compiled decline cexes are leftover `Ⅰ`
(`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`) and
leftover `ⅠⅠ`
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
Neither is this family. Every wired detector on `main` is built for a
different contact. CONTEXT **Regime** selects a witness matrix for a
classified pair. CONTEXT **Bar 1** is a classification that is true
geometry against the specified interior **and** a designated witness
matrix. This leftover has neither a pair nor a matrix. It is a
**research park** (ADR-0002): no published compiled statement.

#609 (not on `main`) is leftover `Ⅰ`'s **mutual** detector. A
one-sided T stays `TPR_Unsupported` after that letter. Do not treat
#609 as this leftover. Do not widen `touch_partial_edge_b`.

This grill does not mint a pair and call it the spec.

## Claims grilled live

### 1. No compiled pair on this tree

**Confirmed.** There is no `onesided_t_pair_coords` (or any other
name) in `RelateNGComplete.v`. The compiled leftover coords are
`tjunction_pair_coords` (leftover `Ⅰ`) and the obtuse pair in
`triangle_pair_regime_ccw_incomplete_not_tjunction` (leftover `ⅠⅠ`).
`classified_hard_pairs` is four rows. None of those six 12-tuples is
this family.

### 2. The two decline cexes are the other leftovers

**Confirmed.**

| Finding | Leftover | Why not `ⅠⅠⅠ` |
|---|---|---|
| `RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction` | `Ⅰ` | Mutual collinear partial-edge. BB dim 1. |
| `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction` | `ⅠⅠ` | Shared vertex; cone `side_dot = 0`. |

### 3. Every wired detector on `main` is the wrong tool

**Confirmed.** Order (`RelateNGCore.v : triangle_pair_regime`):
`touch_edge_b` → `contains_b` → `overlap_b` → `separated_b` →
`touch_vertex_b` → `TPR_Unsupported`.

| Detector | Why it is the wrong tool |
|---|---|
| `touch_edge_b` | `RelateNGCore.v : shares_edge_b` is endpoint-pair equality. A T is not a full shared edge. |
| `contains_b` / `overlap_b` | Need a vertex with `0 < gtri`. A T on the boundary is not an interior hit. |
| `separated_b` | A supporting-edge separator is a disjoint witness. A T is contact. |
| `touch_vertex_b` | Needs a shared vertex and `RelateNGCore.v : cone_separates_b`. This family has **no** shared vertex. |

#609's `touch_partial_edge_b` (not on `main`) is **mutual**. This
family is one-sided. After #609 the family still declines.

### 4. Nearby compiled pairs are not this leftover

**Confirmed.** Same exclusion table as the research chart:

| Pair / object | What it is |
|---|---|
| `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)` | Leftover `Ⅰ`. Finding `triangle_pair_regime_incomplete_tjunction`. |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)` | Leftover `ⅠⅠ`. Finding `triangle_pair_regime_ccw_incomplete_not_tjunction`. |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(0,-2)` | #572 / `522-i`. `classified_touchvertex_pair`. |
| `(0,0)(1,0)(0,1)` vs `(2,0)(3,0)(2,1)` | #530 / #571. `classified_disjoint_pair`. |
| RelatePrepared CW 12-tuple | B is CW. Domain-boundary. |
| Line×line int×bnd | `RelateNodingLineLineMeet.v : segments_int_bnd_touches_ib_cell`. |
| Full shared edge | Frozen `TPR_TouchEdge`. |

### 5. CONTEXT Bar 1 is not applicable

**Confirmed miss — not a failed bar, an absent subject.** Bar 1 needs
a classified pair and a designated witness matrix. There is no pair.
There is no fill. Decline on `main` is leftover `Ⅰ`
(`RelateNGDisjoint.v : tjunction_pair_unsupported`;
`RelateNGOracleSurface.v : relate_tjunction_wire_unsupported`).
Wiring leftover `Ⅰ` (#609) moves that golden to leftover `ⅠⅠ`. This
family is not that golden. Do not emit `FFFFFFFFF`. Do not invent a
CONTEXT name for "named family, no pair."

### 6. Inhabited-or-empty is still open

**Confirmed park.** The research chart left this open. This grill
does not settle it. Settling it is the first implement rung, not a
prose 12-tuple.

## Parks (ADR-0002)

- **Research:** inhabited or empty among both-CCW triangles. No
  published compiled statement. Gate: a cex in
  `RelateNGComplete.v` **or** a proof of emptiness.
- **Sequencing:** detector, constructor, fill. All gated on the
  research park. #609 / #611 / #614 are other letters; do not pile
  onto them.
- **Technique:** none. There is no detector statement to grill.

## Not this leftover

Not leftover `Ⅰ` / #609. Not leftover `ⅠⅠ` / #611. Not #572
TouchVertex. Not line×line IB. Not a remint of `aa_matrix_*`. Not
epic wrap-up. Do not mint `522-n`. Do not mint `ⅠⅠⅠⅠ`. Do not
steal `522-j` / `522-m` / `522-f` / `522-i`.

## If `/implement ⅠⅠⅠ` is asked

Read [`spec-onesided-t.md`](spec-onesided-t.md). First compile a cex
or prove emptiness. Do not invent a 12-tuple in prose. Do not restage
#609. Do not pile onto #611 / #614 / a `508-*` branch. Completeness
stays false until proved.

## Decisions so far

- Family named — #614 / [`map-onesided-t-cert.md`](map-onesided-t-cert.md).
- Leftover `Ⅰ` bar 1 in flight — #609 (CI green, not on `main`).
- Leftover `ⅠⅠ` named — #611.
- This grill — named; no compiled pair; Bar 1 not applicable;
  inhabited-or-empty still open.
- Spec / tickets — [`spec-onesided-t.md`](spec-onesided-t.md);
  scout 18–20 closed; ticket 21 takeable.

## Frontier

```
family named ── #614 ── map-onesided-t-cert.md
     no compiled 12-tuple
     this grill ── confirmed against the tree

ⅠⅠⅠ ── research #614 ── grill (this file) ── spec-onesided-t.md
     tickets 18–20 closed ── 21 compile-or-empty takeable
     /implement ⅠⅠⅠ starts at ticket 21

Ⅰ ── T-junction / partial-edge kiss ── #609 ── not this leftover
ⅠⅠ ── obtuse-at-v ── #611 ── not this leftover

522-n ── not minted
ⅠⅠⅠⅠ ── unused ── ask before assigning
```
