# #508 Phase 7 — P* rungs

Observatory note for Proofs #508 remaining rungs (Notion plan
[Implementation Plan: Proofs 508 ExactCurve zoo length](https://app.notion.com/p/3ca1c9833b0681809eb6f43b905cb946)).

`claimId: none` at the epic.  HOLDs (CurveSegment rewrite, Exact\* zoo
types, ADR-0004 remint) are untouched.  Year-1 engine stays circular-only.

| Priority | Lane | File | Headline | Status |
|---|---|---|---|---|
| P0 | bezier | `theories/Bezier3Polygon.v` | `bezier3_length_le_polygon` — L ≤ control-polygon length on [0,1] | Qed, 3-axiom |
| P1 | ellipse | `theories/EllipseLength_E.v` | `ellipse_circular_E_discharges` — rx=ry inhabits H_E_chord / H_E_approx at E(t)=r·t; general elliptic-E parked | Qed + Technique park, 3-axiom |
| P1 | clothoid | `theories/ClothoidLength_unit.v` | `unit_line_discharges_window` — unit-speed straight inhabits the [sd,ed] contract; Fresnel stays clothoid-halley-coq | Qed + Technique park, 3-axiom |
| P1 | nurbs | `theories/NurbsGeneralLength.v` | equal-weight rational cubic ↔ cubic; knot-span additivity; conditional primitive | Qed, 3-axiom |
| P2 | arc | `theories/ArcMidSweep.v` | `valid_arc_sweep_nonzero`; `arc_mid_on_circle_param` | Qed, Category C (atan2; removal tracks AngleBetween) |

Oracle `B` stays 8-coord cubic.  `red_length_unified_zoo_tests.py` is
untouched.  No new 64-a r·θ definition.
