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
| — | framework | `theories/BernsteinBasis.v` | `bern_partition`; `bern_elevate_2` (n=2 instance of `elevate_ctrl`); `bezier3_elevation_pointwise` re-proved through it | Qed, 3-axiom (#562 / 508-f) |

Oracle `B` stays 8-coord cubic.  `red_length_unified_zoo_tests.py` is
untouched.  No new 64-a r·θ definition.

## 508-c spike (#561)

Route 1 (in-corpus).  `theories/SpeedIntegral.v` packages

`uniformly_continuous_on σ` + `increment_squeezed F σ` + `chord_rate_tight g σ`

over tagged partitions (`chain` + one tag per gap, `riemann_sum`) and
proves `speed_integral_premises → is_curve_length g a b (F b − F a)`.

Heine–Cantor is **not** imported — uniform continuity stays a
hypothesis (3-axiom allowlist).  Coquelicot / `RInt` (Route 2) is
gated off this letter; host-lane metric files stay 3-axiom.  508-d
(elliptic E) and 508-e (Fresnel) instantiate the pack.

## 508-f (#562)

`theories/BernsteinBasis.v` consolidates the Bernstein / rational
plumbing that lived in `Bezier3Length.v`, `NurbsQuadraticLength.v`,
and `NurbsGeneralLength.v`.  Public names stay (`bern2_*`, `bern3_*`,
`bezier3_c0/c1/c2`, `norm_triple_le`, `nurbs2_den_lb`).  Elevation
exactness is the n=2 instance of `elevate_ctrl` via `bern_elevate_2`.
Non-negativity is `Rmult_le_pos` / `lra` — Flocq 4.2.1 `nra` cannot
find a cubic witness (CI death on 48a5c3f). Does not retire epic 508.
Wrap-up is #566.
