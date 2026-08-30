# Map — one-sided / non-collinear vertex-in-open-edge T

A wayfinder map. Charted 2026-08-30. This is **not** a GitHub child, **not**
a remint of `522-j` / `522-m` / `522-i`, **not** leftover `Ⅰ`'s collinear
partial-edge kiss (`map-tjunction-cert.md`), and **not** leftover `ⅠⅠ`'s
obtuse-at-v certificate. It is **not** the line×line noding T-junction
(`RelateNodingLineLineMeet.v : segments_int_bnd_touches_ib_cell`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are repeated `Ⅰ`
> marks. This leftover is **`ⅠⅠⅠ`**. The T-junction / partial-edge kiss
> is **`Ⅰ`**. Obtuse-at-v is **`ⅠⅠ`**. Do not swap them. Do not remint
> ADR-0004. This map does not mint a GitHub child. Next unused is
> **`ⅠⅠⅠⅠ`** — ask before assigning. Do not mint `ⅠⅤ` / `Ⅳ`.

topics: relate
claimId: ⅠⅠⅠ
witness: none

## Destination

**Name the reserved family. There is no compiled pair.**

Leftover `Ⅰ` and leftover `ⅠⅠ` both reserved a third family: a
**one-sided or non-collinear vertex-in-open-edge T** (BB dimension 0,
no shared vertex). This map assigns leftover **`ⅠⅠⅠ`** to that family
and stops. It does **not** invent a 12-tuple. It does **not** invent a
detector. Completeness stays false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`).
`/implement` of `ⅠⅠⅠ` is a later letter, and that letter must first
compile a cex or prove the family empty among both-CCW triangles.

## The family (not a spec pair)

A vertex of one both-CCW triangle sits in the **open interior** of an
edge of the other. The contact is **not mutual**. The triangles share
**no vertex**. The shared set is a **point** (BB dimension 0), not
leftover `Ⅰ`'s positive-length collinear kiss.

That is a **family name**. It is not a compiled 12-tuple. There is no
`onesided_t_pair_coords` (or any other name) in `RelateNGComplete.v`.
The two compiled decline cexes on `main` are leftover `Ⅰ`
(`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`) and
leftover `ⅠⅠ`
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
Neither is this family. The oracle decline golden is leftover `Ⅰ`
(`oracle/de9im_triangle_vectors.txt` `REGIME DECLINE`;
`RelateNGOracleSurface.v : relate_tjunction_wire_unsupported`).

This map does not draw coordinates. Minting a pair here and calling it
the spec would invent the certificate's input.

The family is **uninhabited on the compiled tree**. An exterior-side
stem exists; compiling it is ticket 21. Do not let “inhabitance is
open” harden into “maybe no such triangles exist.” Emptiness would
be a surprise. This map does not mint coordinates and call them the
spec.

## Why leftover `Ⅰ` and leftover `ⅠⅠ` exclude it

Classifier order on `main` (`RelateNGCore.v : triangle_pair_regime`):
`touch_edge_b` → `contains_b` → `overlap_b` → `separated_b` →
`touch_vertex_b` → `TPR_Unsupported`.

Leftover `Ⅰ` is a **collinear mutual** partial-edge kiss. Both
bottoms share a positive-length open-closed segment. No vertex is
shared. Finding
`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`.
The in-flight leftover `Ⅰ` detector (`touch_partial_edge_b` on #609)
is **mutual**. A one-sided T stays `TPR_Unsupported` after that letter.
Do not treat #609 as on `main`
(`RelateNGDisjoint.v : tjunction_pair_unsupported`).

Leftover `ⅠⅠ` is a **shared-vertex** closed-cone miss. Pair
`(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)`. Finding
`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`.
`RelateNGCore.v : cone_separates_b` fails because `side_dot = 0`.
A vertex-in-open-edge T with no shared vertex is a different geometry.

On `main` every wired detector is built for a different contact:

| Detector | Why it is the wrong tool for this family |
|---|---|
| `touch_edge_b` | `RelateNGCore.v : shares_edge_b` is endpoint-pair equality. A T is not a full shared edge. |
| `contains_b` / `overlap_b` | Need a vertex with `0 < gtri`. A T on the boundary is not an interior hit. |
| `separated_b` | A supporting-edge separator is a disjoint witness. A T is contact. |
| `touch_vertex_b` | Needs a shared vertex and `RelateNGCore.v : cone_separates_b`. This family has **no** shared vertex. |

## Nearby pairs that are **not** this leftover

| Pair / object | What it is | Do not |
|---|---|---|
| `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)` | Leftover `Ⅰ` kiss. Mutual. BB dim 1. Finding `RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`. | steal leftover `Ⅰ` / restage #609 |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(1,-1)` | Leftover `ⅠⅠ` obtuse-at-v. Shared vertex; cone `side_dot = 0`. Finding `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`. | steal leftover `ⅠⅠ` |
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(0,-2)` | #572 / `522-i`. Classified **`TPR_TouchVertex`**. `RelateNGComplete.v : classified_touchvertex_pair`. | remint `cone_separates_b` / steal `522-i` |
| `(0,0)(1,0)(0,1)` vs `(2,0)(3,0)(2,1)` | #530 / #571 sentinel. Classified **disjoint**. `RelateNGComplete.v : classified_disjoint_pair`. | treat as the decline golden |
| `(0,0)(1,0)(0,1)` vs `(2,0)(2,1)(3,0)` | RelatePrepared decline 12-tuple. B is **CW** (`gdbl < 0`). Domain-boundary. | use as this family's spec |
| Line×line int×bnd | `RelateNodingLineLineMeet.v : segments_int_bnd_touches_ib_cell`. #67 / S15d. IB dim-0. | steal as the triangle certificate |
| Full shared edge `(0,0)(1,0)(0,1)` vs `(1,0)(1,1)(0,1)` | Frozen `TPR_TouchEdge` pin. | widen `shares_edge_b` |

The four wired hard pairs (`RelateNGComplete.v : classified_hard_pairs`)
classify. They are not this leftover.

## If `/implement ⅠⅠⅠ` is asked — implement rungs (not this map)

Park: **research** (ADR-0002). There is **no** published compiled
statement for this family.

1. **Compile a cex.** An exterior-side stem exists; compiling it is
   ticket 21. Do not invent a 12-tuple in prose and treat it as the
   spec. Emptiness would be a surprise. Only then write a detector.
2. **Detector, not a remint.** If a cex exists, a new boolean that is
   true on that 12-tuple and false on leftover `Ⅰ`, leftover `ⅠⅠ`,
   and the four wired hard pairs. Do **not** widen leftover `Ⅰ`'s
   mutual `touch_partial_edge_b` (#609, not on `main`). Do **not**
   invent leftover `ⅠⅠ`'s cone detector. Do **not** silently widen
   `RelateNGCore.v : cone_separates_b` / `touch_vertex_b`. Do **not**
   widen `shares_edge_b` / `touch_edge_b`. Do **not** remint
   `aa_matrix_*` pins.
3. **Constructor is an owner call.** This map does not pick reuse vs
   a new constructor. A new constructor can stay on `im_unsupported`
   until a fill is named.
4. **Bar 1 first, if inhabited.** Interiors miss; the shared set is a
   point. Do not claim bar-2 nine-cell gtri in the first letter unless
   asked.
5. **Harness golden.** On `main` the decline vector is leftover `Ⅰ`.
   After leftover `Ⅰ` (#609) it is leftover `ⅠⅠ`. Wiring this family
   (if inhabited) does not move that golden unless the golden pair
   itself classifies. Do not emit `FFFFFFFFF`. Do not assume
   completeness.
6. **Classifier order.** After leftover `Ⅰ`'s arm if that letter has
   landed, and after `touch_vertex_b`. Do not reorder the four wired
   certificates. Do not pile onto #609, #611, or a `508-*` branch.
7. **Completeness stays false until proved.** Naming this family does
   not prove CCW-completeness. Wiring leftover `Ⅰ` and leftover `ⅠⅠ`
   does not prove it either while this family is open. Do not claim
   `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete` or
   `triangle_pair_regime_ccw_incomplete_not_tjunction` is obsolete.
   Do not steal `522-j` / `522-m` / `522-i` / leftover `Ⅰ` / leftover
   `ⅠⅠ`.

## Decisions so far

- Completeness false on leftover `Ⅰ` — #583 / `522-j`.
- Filtered retry still false on leftover `ⅠⅠ` — #584 / `522-m`.
- Vertex-touch bar 1 on a sibling pair — #582 / `522-i`.
- Honest decline wire token is leftover `Ⅰ` on `main` — #588 + #595 /
  `522-f`. Leftover `Ⅰ` bar 1 is in flight as #609.
- Leftover `Ⅰ` named — #599 / `docs/scout/map-tjunction-cert.md`.
- Leftover `ⅠⅠ` named — #611 (chart not on `main`).
- Parent leftovers chart: #598 / `docs/scout/map-522-leftovers.md`.
- Leftover ids are Roman numerals. This leftover is `ⅠⅠⅠ`. `522-n`
  is not minted. `ⅠⅠⅠⅠ` is unused.
- Grill / spec / tickets — [`map-onesided-t-grill.md`](map-onesided-t-grill.md),
  [`spec-onesided-t.md`](spec-onesided-t.md), scout 18–20 closed.
  Ticket 21 (compile or empty) is takeable.

## Fog

- **Inhabited or empty.** Uninhabited on the compiled tree. An
  exterior-side stem exists; compiling it is ticket 21. Emptiness
  would be a surprise.
- **Constructor vs reuse.** Technique, not this map. The geometry of
  an exterior-side stem is a dim-0 boundary contact without a shared
  vertex.
- **Fill.** Exterior-side stem with II empty is areal Touches, BB
  dim 0. Interior-side stem is typically overlap. The designated
  TouchVertex / TouchEdge pin is still `FFFF1FFF2`. Remint is a
  different leftover. Fill stays `im_unsupported` until ticket 21
  picks a side.
- **Leftover `Ⅰ`.** In flight as #609. Mutual detector. Do not invent
  or widen that boolean here.
- **Leftover `ⅠⅠ`.** Shared-vertex cone. Do not invent that detector
  here. Do not swap the letters.
- **`ⅠⅠⅠⅠ`.** Unused. Ask before assigning it. Do not mint `ⅠⅤ` /
  `Ⅳ`.

## Frontier

Leftover `ⅠⅠⅠ` is named. There is no compiled pair. This map does
not invent a detector. Grill, spec, and scout tickets 18–20 are
closed. Ticket 21 is takeable.

```
family named ── one-sided / non-collinear vertex-in-open-edge T
     no compiled 12-tuple on main
     BB dim 0; not mutual; no shared vertex

ⅠⅠⅠ ── research ── destination met (name only)
     grill map-onesided-t-grill.md ── spec-onesided-t.md
     /implement ⅠⅠⅠ starts at ticket 21 (compile or empty)

Ⅰ ── T-junction / partial-edge kiss ── map-tjunction-cert.md ── not this leftover
ⅠⅠ ── obtuse-at-v ── #611 ── not this leftover
not this leftover ── #572 TouchVertex ── classified_touchvertex_pair
not this leftover ── #530 sentinel ── classified_disjoint_pair
not this leftover ── RelatePrepared CW 12-tuple
not this leftover ── line×line T ── #67
not this leftover ── widen shares_edge_b ── TouchEdge leftover
not this leftover ── fill remint ── four shared pins

522-n ── not minted
ⅠⅠⅠⅠ ── unused ── ask before assigning
```
