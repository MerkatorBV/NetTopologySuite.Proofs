# Library footnotes — papers filed, and where (if anywhere) they land

> **What this file is.** The operator's paper library grew faster than the
> corpus. This is the map from a filed paper to the module that honestly
> descends from it. A paper gets a cite block in a `.v` header **only** when
> that file's content is genuinely downstream of the paper's claim; everything
> else is parked here with a suggested future home, rather than stamped into an
> unrelated module.
>
> Not a claims index (that is `verified-claims.md`) and not an axiom record.
> Nothing here asserts that a paper has been implemented, ported, or proved.
>
> PDFs live in the operator's dashboard library, not in this repository;
> papers are identified by DOI only.

## Cited in the corpus

Three of the eleven filed papers have an existing module that is genuinely
their descendant. Each got a header block in house style (authors, title,
venue, `doi:…`, and an explicit paper-CLAIMS vs file-PROVES separation).

| Paper | DOI | Cite added to | What the file actually does |
|---|---|---|---|
| Hobby 1999, *Practical segment intersection with finite precision output* | 10.1016/S0925-7721(99)00021-8 | `theories-flocq/HobbyTheorem_b64.v` | Already mechanised Hobby §4 Theorem 4.1 over the corpus's own `snap_round`; the header carried the paper but no DOI. DOI + paper-vs-file paragraph added; no proof touched. |
| Greene & Yao 1986, *Finite-Resolution Computational Geometry* | 10.1109/SFCS.1986.19 | `theories-flocq/TopologicalCorrectness_b64.v` | The file's `no_spurious_intersections` — the milestone-4 half it explicitly does *not* prove — is Greene–Yao failure mode (1). Ancestry block names the catalogue, and marks the direction the file *does* prove ("no meeting is lost") against the one it does not ("no meeting is invented"). |
| Fortune 1987, *A Sweepline Algorithm for Voronoi Diagrams* | 10.1007/BF01840357 | `theories/DelaunayEdgeEmptyCircle.v` | The empty-circumcircle characterisation is the Delaunay side of Fortune's Voronoi dual; #68 is the lane that descends from his sweepline. The file proves the predicate side under a weak triangulation skeleton — no sweep, no beach line, no diagram construction. |

Deliberately **not** stamped elsewhere: Hobby is already named (without DOI) in
several downstream snap-rounding files, and Fortune's lane has four more
Delaunay modules. One cite per paper, at its best home.

## Map only — no honest home in the corpus today

| Paper | DOI | Suggested future module | Why not cited now |
|---|---|---|---|
| Zhai 2026, *Polycenter: fast and precise polygon center identification* | 10.1080/13658816.2025.2514056 | `MaximumInscribedCircle.v` (new; #813 lane) | There is **no MIC / visual-centre module**. `InDisk.v` is arc-supporting-circle disk membership (#64 arc primitives) and `Disk.v` is closed-disk containment — neither is a centre finder. A Polycenter cite in either would be false ancestry. |
| Garcia-Castellanos & Lombardo 2007, *Poles of inaccessibility* | 10.1080/14702540801897809 | same MIC module, as the **definition** footnote | Authoritative PIA definition (exactly three closest shoreline points), but **on the sphere**. The corpus is planar throughout; plane MIC ≠ spherical PIA, and Table 1's coordinates are not test oracles for anything here. |
| Chin, Snoeyink & Wang 1999, *Finding the Medial Axis of a Simple Polygon in Linear Time* | 10.1007/PL00009429 | `MedialAxis.v` (new) — or the "MIC centre lies on the medial axis" bridge lemma | No medial-axis content exists (`grep -i medial` over `theories/`, `theories-flocq/`, `docs/` returns nothing). `RingClearance.v` proves a sup-metric clearance ball around an off-ring point, which is a *corridor* fact for the face-walk, not a skeleton. |
| Lee 1982, *Medial Axis Transformation of a Planar Shape* | 10.1109/TPAMI.1982.4767267 | same `MedialAxis.v`, as the O(n log n) predecessor | Same reason. See the misnomer note below — this is **not** Lee–Drysdale 1981. |
| Beyhan, Güler & Tağa 2020, *An algorithm for maximum inscribed circle based on Voronoi diagrams* (MICGIS) | 10.1007/s10109-020-00325-3 | MIC lane, as the Voronoi + Apollonius alternative | Third MIC algorithm with no MIC module to sit under. Would be a new epic, not a footnote. Zhai's "days vs seconds" comparison is Zhai's measurement and is not reproduced anywhere in this repo. |
| Bentley 1975, *Multidimensional Binary Search Trees Used for Associative Searching* | 10.1145/361002.361007 | `KdTree.v` (new; NTS #814 / k-NN) | No spatial index is formalised. `MonotoneChain*.v` is JTS monotone-chain lineage (a different structure), and nothing in the corpus states a height, visit, or nearest-neighbour bound. |
| Edelsbrunner & Mücke 1994, *Three-Dimensional Alpha Shapes* | 10.1145/174462.156635 | `ConcaveHull.v` / `AlphaShape.v` (new) | No concave-hull or α-shape module. The paper is 3-D simplicial complexes; the honest planar bridge ("JTS concave hull at length α is a 2-D α-shape of the vertices, up to tie-break") needs a concave-hull definition that does not yet exist here. |
| Žunić & Rosin 2004, *A New Convexity Measure for Polygons* | 10.1109/TPAMI.2004.19 | shape-descriptor lane (none exists) | `Convex.v` defines the convex-set *predicate* and convex combinations. Žunić–Rosin is a continuous descriptor in (0,1] with its own axiom list — a different object. Citing it in `Convex.v` would misrepresent both. |

## Misnomer corrections

Two legacy bibliography ids are wrong. Neither appears in any `.v` or `.md`
file in this repository (checked by grep), so nothing in-tree needed rewriting;
recorded here so the next person to add these cites uses the right paper.

- **`lee-drysdale-1981-medial` → Lee 1982.** The filed PDF is D. T. Lee,
  *Medial Axis Transformation of a Planar Shape*, IEEE TPAMI PAMI-4(4):363–369,
  1982, doi:10.1109/TPAMI.1982.4767267. Lee–Drysdale 1981 is a different
  result (the O(n log² n) skeleton of *disjoint* objects). Use the 1982 DOI.
- **`rossignac-orey-1994-offset` → Rossignac & Requicha 1986.** The intended
  paper is *Offsetting operations in solid modelling*, doi:10.1016/0167-8396(86)90017-8.
  No cite was added. `BufferOffset.v` (offset segment is parallel to its source
  edge, at distance |d| along the unit normal) and `ArcOffset.v` (the offset of
  a circular arc is the concentric arc of radius r + d) are soundness facts
  about the JTS/NTS offset-curve *builder* — they descend from the builder, not
  from a solid-modelling construction.

  `BufferCorrectness.v` is the closest call: it states the buffer spec as
  Minkowski dilation by the closed disk, which is Rossignac–Requicha's r-offset
  read in the plane. It stays uncited because that is where the resemblance
  stops — the corpus's "Minkowski semantics" is the bare point set
  `{ p | dist(p, g) ≤ d }`, while the paper's content is *regularized* set
  operations on solids: growing vs shrinking, why the two do not compose to the
  identity, and rounding/filleting of the result. None of that appears here.
  What would flip the verdict: a module that proves something about
  grow-then-shrink (opening/closing), regularization, or the offset of a solid
  rather than of a curve. The bibliography already routes this id at issues #65
  and #815, so that module may well arrive — cite it then.

## Scope note

No theorem was added, changed, or removed for this pass. No `Admitted`,
`Axiom`, `Parameter`, or `Classical_Prop` was introduced. The three edits are
header comments only.

**Stale audit narrative — corrected in this pass.**
`theories-flocq/HobbyTheorem_b64.v`'s header claimed that its two §4 support
lemmas "are Admitted with registered deferred-proof entries", and that the file
carried "Two Admitteds". Neither is true of the file as it stands:
`hobby_lemma_4_2` is `Qed`, `hobby_lemma_4_3_no_proper` and `hobby_lemma_4_3`
are `Abort`ed (deliberately — the bare statement is false, per the
counterexample registry), `hobby_lemma_4_3_shared_endpoint` is `Qed`, and no
`Admitted` tactic survives anywhere in `theories/` or `theories-flocq/`.
`docs/admitted-deferred-proofs.txt` already records both former entries as
dispositions (4.2 CLOSED by Qed; 4.3-no-proper moved to
`docs/admitted-counterexamples.txt` as FALSE as stated), so the header was the
last place still asserting the old state. Both header sentences now match the
registry.
