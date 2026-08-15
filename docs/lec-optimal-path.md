# The LEC optimal-path ledger — failed hypotheses as guides

**Lane**: LargestEmptyCircle (construct) · **updated**: 15 Aug 2026 ·
**modules**: `theories/LECChordGap.v`, `theories/LECObstacleDistance.v`,
`theories/LargestEmptyCircle.v`, `theories/CellRadiusBound.v` ·
**oracle**: `LEC_CIRCLE`, `OBSTACLE_DISTANCE`

This lane runs prove-or-disprove: each engine-side hypothesis about how the
largest empty circle can be computed FASTER is either Qed-proven or refuted
by a Qed-closed disproof on an explicit witness cell.  **A refuted
hypothesis is not discarded — it is recorded here, because each failed path
constrains what the theoretically optimal algorithm must do.**  This file is
the prose ledger of those refutations and of the guide each one leaves
behind.

## The target: what "optimal" means here

JTS/NTS `LargestEmptyCircle` ships branch-and-bound: subdivide the domain
into square cells, bound each cell's achievable radius, refine the best
cell until the bound gap is under tolerance.  Its cost scales with the
subdivision depth, not just the obstacle count.  The theoretical optimum
for POINT obstacles is candidate enumeration: the maximiser of
nearest-obstacle distance over a bounded domain lies at a Voronoi vertex,
at a Voronoi-edge × boundary crossing, or on the boundary structure — a
finite candidate set computable in O(n log n) (Toussaint 1983,
doi:10.1007/BF00993201).  For DISC obstacles the additively-weighted
Voronoi (Apollonius) diagram plays the same role, because distance to a
filled disc is exactly the additively-weighted distance to its centre once
clamped at zero — the reduction proven as `min_disc_dist_weighted`.

The corpus's job is the exactness half: prove the closed forms an optimal
algorithm would enumerate, and refute the shortcuts that look cheaper but
are wrong.  The runtime half (median laser vs chainsaw under the perf
gate's 15% slack) stays engine-side by design.

## The ledger

### F1 — "the chord path is enough" (REFUTED · `LECChordGap.v`)

- **Hypothesis** (PERF-GATE, LEC row): "LargestEmptyCircle stays on the
  chord path — no cheaper construction beat densify-then-LEC."
- **Verdict**: disproved as an exactness claim on the single-circle-
  obstacle cell.  `lec_chord_hypothesis_refuted`: the exact LEC of the
  radius-2 circle over its disk is the closed form (centre, 2); the
  4-chord densification's exact answer is (centre, √2); every finite
  chording underestimates by cos(θ/2).
- **Witness**: circle r=2 about the origin vs its inscribed-square
  chording — laser 2, chainsaw √2.
- **Guide**: per-shape CLOSED FORMS exist where densification only
  converges.  The replacement is a typed per-component metric — which the
  engine then implemented (`ObstacleDistance`, jts-curve typed-obstacle
  lane) and F2/F3's module proved exact.

### F2 — "corners are enough" (REFUTED · `LECObstacleDistance.v`)

- **Hypothesis** (H-CORNER): "a radius achievable somewhere in a cell is
  achievable at one of the cell's corners" — the vertex-sampling shortcut
  that would let branch-and-bound bound a cell by evaluating its corners
  and skip `CellRadiusBound.v`'s √2·h Lipschitz slack.
- **Verdict**: `corner_sampling_hypothesis_refuted`.  On the 3-4-5
  witness cell (discs r=3 at (±4,0), domain [−4,4]×[−3,3]) all FOUR
  rectangle corners touch the discs — clearance exactly 0 — while the
  rectangle centre clears exactly 1 (`corner_clearance_zero`,
  `centre_clearance_one`).
- **Why it fails structurally**: min-of-distances is not convex; its
  maxima sit on bisectors in the cell INTERIOR, invisible from the
  vertices.
- **Guide**: cell bounds must carry the Lipschitz slack.  Together with
  9004-d this is a pincer: `cell_achievable_radius_bound` proves the
  centre-clearance + √2·h bound SOUND, its cell-slack witness proves the
  slack not droppable, and H-CORNER proves the vertex-only alternative
  UNSOUND.  The subdivision bound JTS ships is, in this exact sense, the
  right one — the speed frontier is not in weakening it but in replacing
  enumeration of cells with enumeration of candidates (F3).

### F3 — "the optimum is interior" (REFUTED · `LECObstacleDistance.v`)

- **Hypothesis** (H-INTERIOR): "the LEC centre may be searched among
  interior points" — e.g. only at interior equidistant points (Voronoi/
  Apollonius vertices, ≥3 obstacles tied), the tempting pure-vertex
  candidate set.
- **Verdict**: `interior_maximiser_hypothesis_refuted`, via
  `lec_two_discs_maximisers`: on the witness cell the maximisers are
  EXACTLY (0, ±3) — on the domain boundary (py = ±3), on the two-disc
  bisector, equidistant from just TWO obstacles.  No point of the cell is
  equidistant from three obstacles at the optimum radius; an
  Apollonius-vertex-only enumeration finds nothing.
- **Guide**: the optimal candidate set is Toussaint's, transported to
  discs by the Apollonius reduction (`min_disc_dist_weighted`):
  weighted-Voronoi VERTICES ∪ (weighted-Voronoi EDGES × boundary
  crossings) ∪ boundary structure.  The witness optimum (0,3) is a
  bisector × boundary crossing — the middle class, the one H-INTERIOR
  drops.

## What is Qed today (the verified bridge under the engine's table)

- **Filled-disc row exact**: `empty_disk_disc_iff` — emptiness of the
  disc obstacle at radius ρ ⟺ ρ ≤ max(0, dist(c,P) − r).  Lower bound by
  the reverse triangle inequality; ATTAINED by P itself (inside) or the
  radial projection onto the bounding circle (outside).
- **Full-circle-ring row exact**: `empty_disk_ring_iff` — same two
  halves for abs(dist(c,P) − r); from the very centre any circle point
  attains r.  (The disc/ring distinction the engine's table draws —
  filled CurvePolygon vs closed CircularString — is exactly the clamp.)
- **Flatten row sound**: `empty_disk_union_iff` /
  `empty_disk_two_discs_iff` — emptiness against a union is emptiness
  against each part; collection clearance is the min-fold.
- **Apollonius reduction**: `min_disc_dist_weighted` — clamping commutes
  with min, so LEC over discs ≡ additively-weighted LEC over centres.
- **A closed curved-collection cell**: `lec_two_discs` — the LEC of two
  3-4-5 discs over a rectangle is ((0,3), 2), fully rational, maximisers
  characterised exactly.  The oracle mode `OBSTACLE_DISTANCE` gates the
  pins bit-exact (clearance 2 at (0,±3), 1 at the centre, 0 at the four
  corners).

## Open rungs (in likelihood order)

1. **Point-to-arc row**: the engine measures CircularStrings per
   3-control window (radial-foot distance when the foot's angle is in the
   arc sweep, else endpoint min).  The oracle has `ARC_DISTANCE`; the
   Qed spec (sector case split without atan2 — chord-sign forms as in
   `ArcSplitAtNode.v`) is the next metric rung.
2. **CompoundCurve / n-ary flatten**: fold `empty_disk_union_iff` over a
   member list (finite indexed union), giving the engine's
   `getNumMembers`/`getMemberN` min a corpus twin.
3. **Segment/facet row**: the clamped-projection closed form for
   LineString facets — the last straight-edge metric without a spec.
4. **Candidate completeness** (the big one): every maximiser of the
   weighted min-distance over a convex domain is a weighted-Voronoi
   vertex, an edge × boundary crossing, or a boundary vertex — the
   theorem an O(n log n) LEC needs to be TRUSTED, in the corpus's
   witness-scoped style first (three discs, one Apollonius vertex).
5. **Runtime half**: stays engine-side (perf gate); the corpus only ever
   adjudicates exactness.

## Relation to the engine lane

The jts-curve typed-obstacle lane (JTS PR #8, `cursor/curve-perf-gate-45a0`)
keeps uncertified LEC on the branch-and-bound grid and swaps the clearance
callback for the typed metric — the F2 guide says that grid's bound is
right, the F1/F3 guides say where the next speed rung lives: certified
closed forms per cell class, then candidate enumeration on the Apollonius
side once rung 4 lands.  The locked `OBSTACLE_DISTANCE` vectors are the
differential handshake between the two sides.
