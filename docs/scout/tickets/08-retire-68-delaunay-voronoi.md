# Retire #68 — Delaunay triangulation and Voronoi diagrams

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** —

## Question

#68 (Non-urgent) asks for empty-circle exactness, triangulation invariants, the
Voronoi dual, a curve-densify path and oracle modes. The audit reads **PARTIAL**,
with an important nuance: **all three** of the body's round-2 queue items have
landed since the body was written, but a whole phase of the ask has not started.
Does it close, or does the unstarted phase mean it stays open as its own epic?

Landed (verify then cite): `theories/DelaunayFlipGeometric.v:75 inCircle_R_flip_witness_ccw`;
`theories/DelaunayDegeneratePins.v` (`single_triangle_delaunay` = JTS#1190,
`cocircular_square_tie_1039` = JTS#1039, `cocircular_tie_is_knife_edge`);
`theories/DelaunayLocallyDelaunay.v` (68-b,
`flip_witness_both_not_locally_delaunay`); 68-a
`theories/DelaunayEdgeEmptyCircle.v` (`verified-claims.md:434-435`).

Not started:

1. **Voronoi is absent.** `grep -li voronoi theories/` hits only comments and
   `HausdorffMetricSym.v`'s two-site `vor2_*` profile, which is a metric-lane
   slice, not the Delaunay dual. The body's own table already calls Voronoi
   "phase 2".
2. Bisector construction and four-point robustness (JTS#1039, JTS#20).
3. Ask 5: curve densify → triangulate (TRI-DT / TRI-VR densified-boundary path).
4. `DELAUNAY_WITNESS` oracle mode is not in `oracle/driver.ml`.

The decision this ticket owes: an epic whose phase 1 is done and whose phase 2 is
untouched is exactly the shape the destination calls "a clearly-stated new epic".
Close #68 on phase 1 with the evidence above and open *Voronoi dual and
triangulation robustness* as its successor, or keep #68 open and accept that the
block does not reach zero. The former is preferred by the destination; confirm the
phase boundary is real before acting.
