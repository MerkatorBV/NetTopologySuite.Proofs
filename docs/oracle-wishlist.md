**Oracle Wishlist v7.0** (15 Aug 2026, Amsterdam)

**Milestone**: JTS two-disc overlay is exact; oracle still contact-only.

**TAGs shipped**: D-PT, C-LIN, D-AA, OFF, C-AREA, composites, D-CURVE, BUF-S, N-SS, R-CURVE (10+ vertical slices, all green with oracle matches).
**New accept**: **OV-DISC** (JTS product) — two-disc CAP·CUP·SUB·XOR exact; no oracle mode yet.

**Guiding Principles** (still enforced): Low-risk analytical first → pinnable RGR → reuse proofs math → SAFE_INT + BigDecimal → defer full overlay.

### Accepted TAGs (compact)
- **Distance** (D-PT/D-CURVE/D-AA): Full leaf + CS/CC lifts ✅
- **Centroid/Area** (C-LIN/C-AREA + composites): Enclosed + Polygon/Compound ✅
- **Offset/Buffer** (OFF + BUF-S): Leaf + single-arc CurvePolygon ✅
- **Intersections/Noding** (N-AA/N-AL + N-SS basic split): Sub-arc exact ✅
- **Relate/Predicates** (R-CURVE): Intersects/Contains/Relate wiring ✅
- **OV-DISC** (JTS product, 15 Aug 2026): two-disc CAP·CUP·SUB·XOR exact on JTS PR #8 `f58d56a3`. Not yet an oracle mode. https://github.com/grootstebozewolf/jts/pull/8

All with tests (4/4–20/20), code refs, oracle matches, and minimal changes. OV-DISC is a JTS-side accept only.

JTS R1.5 (`CircularDiscOverlay`, hooked in `OverlayNGCurve` after R1 / before R2): both operands circular discs (`CurveExact.circularDisc`) and `CircularArcDensifier.intersectCircles` returns two proper nodes. CAP = lens, CUP = two-arc blob, SUB = crescent, XOR = both crescents, as `CurvePolygon` of two `CircularString`s (`isApproximate = false`). Locked pair `CIRCLE_5` ∩ `CIRCLE_CROSSING`, centres (0,0) and (7,0), r=5, nodes `(3.5, ±√12.75)`. Crossing ratchet `aaaa` → `EEEE`; Crossing CAP 0.017 vs 0.681 ms (ratio 0.025); slack still 15%.

### Current Oracle Modes
✅ ARC_DISTANCE family, ARC_ARC_DISTANCE, ARC_CENTROID, ARC_AREA_CENTROID, ARC_OFFSET_XY, ARC_BUFFER_SIMPLE, N-AA/N-AL (`ARC_ARC_XY` / `run_arc_arc_xy`, `ARC_SEGMENT_XY`), relate_matrix partial, V-CP, PRC-SN + recent buffer/ring/area gens.

`OVERLAY_UNIFIED` is contact DE-9IM only (`212FF1FF2` / `FFFFFFFFF`), not overlay geometry. This repo already has the intersection kernels JTS R1.5 reused (`ARC_ARC_XY` / N-AA, same radical-axis formula; `ARC_SEGMENT_XY` / N-AL). No oracle mode emits the lens / two-arc blob / crescent.

### Remaining Roadmap (smart prioritisation)
| Priority | Item | Notes |
|----------|------|--------|
| High | **TWO_DISC_OVERLAY** oracle mode | Emit CAP/CUP/SUB/XOR geometry (or area + node list) for two full circular discs. Pin against JTS `CircularDiscOverlay` / `CIRCLE_5` ∩ `CIRCLE_CROSSING` nodes `(3.5, ±√12.75)`. Reuse `ARC_ARC_XY` + circumcentre_q. This is the next accept. |
| High | Adversarial + BigDecimal/ROCQ_REF_BIN harness | 1 day. Across all accepted modes. Close RGR gaps. |
| High | **ARC_BUFFER_FULL** (multi-arc, negative, self-intersect) | 3 days. Use BUF-S + N-SS. |
| High | General circular noding + arrangement | Unparked. Split arcs at N-AA/N-AL nodes, face labels, then general CAP·CUP·SUB·XOR. JTS next laser after two-disc (disc vs polygon, CompoundCurve shells, lineal arc vs line, on-arc-vertex TopologyException). |
| Medium | ARC_SIMPLIFY + ARC_SNAP | 2 days. Post-noding. |
| Medium | Full CURVE_RELATE/DE9IM (holes, Multi, mixed) | 3 days. Extend matrix. |
| Parked | Shewchuk port | After seams stable. |

**Recommended next**: **TWO_DISC_OVERLAY** (oracle has the intersection points; JTS already emits the overlay geometry).

### Reusable Templates
**RGR Pattern** (used for every slice): Read (grep fallback) → Red (analytical test) → Green (minimal reuse) → Refactor (tiny + comment) → Pin + Cake + oracle match → Accept.

**Oracle Add SOP**: Protocol keyword → OCaml/Coq + lemma → Extract → RocqRefRunner → Generator → NTS harness → Cake → bump this file.

**Verification command** (standard): `dotnet test ... --filter "Distance|Offset|Centroid|Area|Buffer|Intersects|Relate|Split"` + oracle probes.

### How to Keep This File Smart
- New accept → add 1 row to Accepted table + bump version/date + one-line note.
- New wishlist item → add to Remaining table only.
- No full RGR stories here (keep in PRs/commits for audit).

References unchanged.

This is the official maintainable plan.
