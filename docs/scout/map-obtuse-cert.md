# Map — obtuse-at-v certificate

A wayfinder map. Charted 2026-08-30. This is **not** a GitHub child, **not**
a remint of `522-j` / `522-m` / `522-i`, and **not** leftover `Ⅰ`'s
collinear partial-edge kiss (`map-tjunction-cert.md`).

> **Do not mint letters.** Closed ticket ids (`522-a` … `522-m`) stay
> historical. Do **not** mint `522-n`. Leftover ids are repeated `Ⅰ`
> marks. This leftover is **`ⅠⅠ`**. The T-junction / partial-edge kiss
> is **`Ⅰ`**. Do not swap them. Do not remint ADR-0004.
> This map does not mint a GitHub child. `ⅠⅠⅠ` is unused.

topics: relate
claimId: ⅠⅠ
witness: none

## Destination

**Name the #584 finding pair as leftover `ⅠⅠ`'s specification, without
inventing the certificate.**

Ticket #577 asked either completeness or a documented counterexample that
becomes the next certificate's spec. Completeness is false on the
T-junction (`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`).
The filtered retry is still false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
The compiled second pair is the spec. This map charts what that spec is,
what it is not, and what `/implement` of leftover `ⅠⅠ` must not steal.
It does **not** write a detector. `/implement` of `ⅠⅠ` is a later letter.

## The pair (the spec)

A = `(0,0)(2,0)(0,2)`, B = `(0,0)(-2,0)(1,-1)`.

Both-CCW: `RelateNGComplete.v : obtuse_pair_both_ccw`. Not the T-junction
12-tuple: `RelateNGComplete.v : obtuse_pair_not_tjunction`. Compiled
decline: `RelateNGComplete.v : obtuse_pair_unsupported`. Headline finding:
`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`.

Same A as the #572 / `522-i` vertex-touch pin
(`RelateNGComplete.v : classified_touchvertex_pair`): A vs
`(0,0)(-2,0)(0,-2)` classifies `TPR_TouchVertex`. This leftover only
moves B's third vertex from `(0,-2)` to `(1,-1)`.

```
        (0,2)
           *
          /|
         / |
   (0,0)*--+--*(2,0)
        |
        |     *(1,-1)
        |
   (-2,0)*
```

They share **exactly one vertex** — the origin. No full edge is shared
(`shares_edge_b` is endpoint-pair equality). A's bottom `[(0,0),(2,0)]`
and B's bottom `[(0,0),(-2,0)]` meet only at `(0,0)`.

The vertex-touch cone is constructed in `RelateNGCore.v : cone_separates_b`:
normal `nA = vec_sum_from v (2,0) (0,2) = (2,2)`. Then
`RelateNGCore.v : side_dot` of B's remaining vertex `(1,-1)` against
`nA` is `1·2 + (−1)·2 = 0`. The cone demands a **strict** sign on both
remaining B-vertices (`both_strict_neg_b` / `both_strict_pos_b`). A zero
fails. That is the compiled miss
(`RelateNGComplete.v : obtuse_pair_unsupported`).

The corpus nickname is **obtuse-at-v**. B's angle at the shared vertex
is obtuse: legs `(−2,0)` and `(1,−1)` have negative dot product. `(1,−1)`
sits on the supporting line of A's cone through `v` (the line `y = −x`).
The shared set is a **vertex** (BB dimension 0), not leftover `Ⅰ`'s
positive-length collinear kiss.

On `main` today the harness decline golden is still leftover `Ⅰ`
(`oracle/de9im_triangle_vectors.txt` `REGIME DECLINE` on the T-junction).
Leftover `Ⅰ` bar 1 is in flight as #609; that letter moves the decline
golden onto this pair. This map does not wait on #609.

## Why every wired detector misses

Classifier order on `main` (`RelateNGCore.v : triangle_pair_regime`):
`touch_edge_b` → `contains_b` → `overlap_b` → `separated_b` →
`touch_vertex_b` → `TPR_Unsupported`.

| Detector | Why false on this pair |
|---|---|
| `touch_edge_b` | No full shared edge. `(0,0)(2,0)` ≠ `(0,0)(−2,0)`. |
| `contains_b` | Needs `0 < gtri A` at every B-vertex. `(0,0)` is a vertex of A (`gtri ≤ 0`). |
| `overlap_b` | Needs a B-vertex with `0 < gtri A`. `(0,0)` and `(−2,0)` have `gtri A ≤ 0`; `(1,−1)` is strictly exterior. |
| `separated_b` | `RelateNGComplete.v : obtuse_no_separator` — the shared origin is an endpoint of every candidate edge. |
| `touch_vertex_b` | `exactly_one_shared_from_a` is **true**. `cone_separates_b` is **false** (`side_dot = 0` on `(1,−1)`). |

Leftover `Ⅰ`'s planned `touch_partial_edge_b` (in flight #609) is also
false on this pair: no vertex sits in an open edge. Do not treat that
arm as on `main` until #609 merges.

## Nearby pairs that are **not** this leftover

| Pair | What it is | Do not |
|---|---|---|
| `(0,0)(2,0)(0,2)` vs `(0,0)(-2,0)(0,-2)` | #572 / `522-i`. Classified **`TPR_TouchVertex`**. Same A; B's third vertex is strictly in the opposite cone. | remint `cone_separates_b` / steal `522-i` |
| `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)` | Leftover `Ⅰ` kiss. **No** shared vertex. Finding `RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`. | bucket under one letter |
| `(0,0)(1,0)(0,1)` vs `(2,0)(3,0)(2,1)` | #530 / #571 sentinel. Classified **disjoint**. | treat as the decline golden |
| `(0,0)(2,0)(0,2)` vs `(0,0)(1/2,1/2)(-2,0)` | Ticket nudge. `RelateNGTouchVertexRegime.v : touchvertex_nudge_off`. Remaining B-vertex sits on A's side of `nA` (overlap, not a closed cone). | treat as obtuse-at-v |
| `(0,0)(1,0)(0,1)` vs `(2,0)(2,1)(3,0)` | RelatePrepared decline 12-tuple. B is **CW** (`gdbl < 0`). Domain-boundary. | use as the obtuse spec |
| Line×line int×bnd | `RelateNodingLineLineMeet.v : segments_int_bnd_touches_ib_cell`. #67 / S15d. IB dim-0. | steal as the triangle certificate |
| Full shared edge `(0,0)(1,0)(0,1)` vs `(1,0)(1,1)(0,1)` | Frozen `TPR_TouchEdge` pin. | widen `shares_edge_b` |

A **non-collinear** vertex-in-open-edge T (BB dim 0, no shared vertex) is
not compiled. Leftover `Ⅰ` left that family unnamed. If a later letter
wants it, that is leftover `ⅠⅠⅠ` — unused, ask first. It is **not**
this leftover.

## If `/implement ⅠⅠ` is asked — implement rungs (not this map)

Park: **research** (ADR-0002). The finding is compiled; the detector is not.

1. **Detector, not a remint.** A boolean that is true on this 12-tuple
   and false on the four wired hard pairs
   (`RelateNGComplete.v : classified_hard_pairs`) and on leftover `Ⅰ`'s
   kiss. Working names only: a **closed** cone (allow `side_dot = 0`)
   versus a new predicate. Do **not** silently widen
   `RelateNGCore.v : cone_separates_b` / `touch_vertex_b` — that vocab
   is the #572 / `522-i` certificate. Do **not** widen `shares_edge_b` /
   `touch_edge_b`. Do **not** steal leftover `Ⅰ`'s
   `touch_partial_edge_b`. Do **not** remint `aa_matrix_*` pins.
2. **Constructor is an owner call.** Reuse `TPR_TouchVertex` vs add a
   constructor. Reuse inherits fill `FFFF1FFF2`
   (`aa_matrix_touch_vertical`) and is the same geometric family
   (vertex kiss, BB dim 0). A new constructor can stay on
   `im_unsupported` until a fill is named. This map does not pick.
3. **Bar 1 first.** Interiors miss; the shared set is a vertex. Do not
   claim bar-2 nine-cell gtri in the first letter unless asked. The
   designated TouchVertex pin is still the `aa_matrix_touch_vertical`
   starter — cite, do not rewire the classifier pointer.
4. **Harness golden.** On `main` the decline vector is leftover `Ⅰ`.
   After leftover `Ⅰ` (#609) the decline vector **is this pair**. If
   this pair classifies, `REGIME DECLINE` in
   `oracle/de9im_triangle_vectors.txt` and the hunt selfcheck notes must
   point at a still-unsupported pair, or record that no compiled decline
   remains. Do not turn the decline into a confident `FFFFFFFFF`. Do
   not assume completeness.
5. **Classifier order.** After `touch_vertex_b` (or as an owner-chosen
   relaxation of it). After leftover `Ⅰ`'s arm if that letter has
   landed. Do not reorder the four wired certificates. Do not pile
   onto #609 or a `508-*` branch.
6. **Completeness stays false until proved.** Wiring this pair does not
   prove CCW-completeness. A dim-0 T is unnamed. Do not claim
   `RelateNGComplete.v : triangle_pair_regime_ccw_incomplete` or
   `triangle_pair_regime_ccw_incomplete_not_tjunction` is obsolete.
   Do not steal `522-j` / `522-m` / `522-i` / leftover `Ⅰ`.

## Decisions so far

- Completeness false on the T-junction — #583 / `522-j`.
- Filtered retry still false on this pair — #584 / `522-m`.
- Vertex-touch bar 1 on the sibling pair — #582 / `522-i`.
- Honest decline wire token is leftover `Ⅰ` on `main` — #588 + #595 /
  `522-f`. Leftover `Ⅰ` bar 1 is in flight as #609.
- Certificates not invented in those letters.
- Parent leftovers chart: #598 / `docs/scout/map-522-leftovers.md`.
- Leftover `Ⅰ` detail chart: #599 / `docs/scout/map-tjunction-cert.md`.
- Leftover ids are Roman numerals. This leftover is `ⅠⅠ`. `522-n` is
  not minted. `ⅠⅠⅠ` is unused.

## Fog

- **Constructor vs reuse `TPR_TouchVertex`.** Technique, not this map.
  The geometry is a vertex kiss. The compiled miss is a **strict** cone.
- **Closed cone vs new boolean.** Widening `cone_separates_b` remints
  #572. A new boolean can stay off the #572 fill until named.
- **Fill.** Geometry of the kiss is areal Touches with BB dim 0. The
  designated TouchVertex pin is still `FFFF1FFF2`. Remint is a different
  leftover.
- **Family width.** This spec is the compiled closed-cone vertex kiss.
  A dim-0 T (vertex in an open edge, no shared vertex) is unnamed.
- **Leftover `Ⅰ`.** In flight as #609. Do not invent that detector
  here. Do not swap the letters.
- **`ⅠⅠⅠ`.** Unused. Ask before assigning it.

## Frontier

Leftover `ⅠⅠ` is named. This map does not invent the detector.

```
#584 finding ── triangle_pair_regime_ccw_incomplete_not_tjunction ── done

ⅠⅠ ── obtuse-at-v ── detector not invented
     pair (0,0)(2,0)(0,2) vs (0,0)(-2,0)(1,-1)
     shared vertex; cone side_dot = 0
     decline golden after leftover Ⅰ (#609); T-junction today on main

Ⅰ ── T-junction / partial-edge kiss ── map-tjunction-cert.md ── not this leftover
not this leftover ── #572 TouchVertex ── (0,-2) third vertex
not this leftover ── ticket nudge ── touchvertex_nudge_off
not this leftover ── line×line T ── #67
not this leftover ── widen cone_separates_b ── steal 522-i
not this leftover ── widen shares_edge_b ── TouchEdge leftover
not this leftover ── fill remint ── four shared pins

522-n ── not minted
ⅠⅠⅠ ──── unused ── dim-0 T if asked
```
