# #508 Phase 7 — P* rungs

Observatory note for Proofs #508 remaining rungs (Notion plan
[Implementation Plan: Proofs 508 ExactCurve zoo length](https://app.notion.com/p/3ca1c9833b0681809eb6f43b905cb946)).

`claimId: none` at the epic.  HOLDs (CurveSegment rewrite, Exact\* zoo
types, ADR-0004 remint) are untouched.  Year-1 engine stays circular-only.

| Priority | Lane | File | Headline | Status |
|---|---|---|---|---|
| P0 | bezier | `theories/Bezier3Polygon.v` | `bezier3_length_le_polygon` — L ≤ control-polygon length on [0,1] | Qed, 3-axiom |
| P1 | ellipse | `theories/EllipseLength_E.v` | `ellipse_circular_E_discharges` — rx=ry inhabits H_E_chord / H_E_approx at E(t)=r·t; general elliptic-E parked | Qed + Technique park, 3-axiom |
| P1 | ellipse | `theories/EllipseSpeedIntegral.v` | `ellipse_speed_integral_is_curve_length` — UC + chord-rate of √σ²; increment_squeezed E σ is the remaining primitive | Qed + Technique park, 3-axiom (#563 / 508-d) |
| P1 | clothoid | `theories/ClothoidLength_unit.v` | `unit_line_discharges_window` — unit-speed straight inhabits the [sd,ed] contract; Euler-spiral integrals stay Route-1 primitives | Qed + Technique park, 3-axiom |
| P1 | clothoid | `theories/ClothoidFresnel.v` | `fresnel_is_curve_length` — unit-speed pack at `F = fun t => 1 * t`; Cx, Cy increment_squeezed against (cos,sin)(t²/2); conditional, no inhabitant | Qed + Technique park, 3-axiom (#564 / 508-e) |
| P1 | nurbs | `theories/NurbsGeneralLength.v` | equal-weight rational cubic ↔ cubic; knot-span additivity; conditional primitive | Qed, 3-axiom |
| P2 | arc | `theories/ArcMidSweep.v` | `valid_arc_sweep_nonzero`; `arc_mid_on_circle_param` | Qed, Category C (atan2; removal tracks AngleBetween) |
| — | framework | `theories/BernsteinBasis.v` | `bern_partition`; `bern_elevate_2` (n=2 instance of `elevate_ctrl`); `bezier3_elevation_pointwise` re-proved through it | Qed, 3-axiom (#562 / 508-f) |
| — | stop | `theories/ExactCurveEpic508.v` | `ticket_508_qed_or_qex` — zoo-on-CurveSegment (QED) or missing constructor (QEX); discharged QEX on the ellipse | Qed, 3-axiom (508-qed-qex) |

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

## 508-d (#563)

`theories/EllipseSpeedIntegral.v` instantiates the pack on
`ellipse_speed rx ry = √(rx² sin² t + ry² cos² t)`.  Uniform
continuity is Hölder 1/2 (`|σ(t)−σ(s)| ≤ √(K·|t−s|)`).  Chord-rate
uses the exact identity `dist = 2|sin(gap/2)|·σ(mid)`.  Route 1 does
**not** construct the incomplete elliptic integral — `increment_squeezed`
stays the Technique-park hypothesis.  Witness: any such E on the
`rx=3, ry=4` quarter lies in `[3π/2, 4π/2]`.  Does not retire epic 508.
Wrap-up is #566.  Does not remint SpeedIntegral.

## 508-e (#564)

`theories/ClothoidFresnel.v` is a #561 pack instance on the
clothoid-shaped integrands `(cos,sin)(t²/2)`, not a Fresnel
construction: there is still no `Cx` / `Cy` inhabitant, and Route 1
does not produce `RInt`. Heading `t²/2` is Lipschitz on a compact
window (constant `Rmax(|a|,|b|)`), so a fine gap makes the
coordinate increments a first-order match to the unit velocity
(`cos²+sin²=1`) and the chord realizes the gap. Uniform continuity
of `σ ≡ 1` and `increment_squeezed (fun t => 1 * t) (fun _ => 1)`
are free (`constant_speed_premises`; pack `F` is `fun t => 1 * t`,
not bare `id`). `increment_squeezed` on each coordinate stays the
Technique-park hypothesis. ADR-0001 route D (Coquelicot lane)
stays consumer-gated. Ellipse #563 already instantiated the same
pack on a curved speed; this is the first clothoid-shaped
integrand, not the first curved pack use. The `[0,1]` length-1
claim is the same theorem with `b − a` peeled by `Rminus_0_r`.
`fresnel_discharges_clothoid_window` is a K-token wiring check
(same statement via `H_unit_chord` / `H_unit_approx`), not extra
geometric content. Never global. Does not retire epic 508.
Wrap-up is #566. Does not remint SpeedIntegral.

## 508-f (#562)

`theories/BernsteinBasis.v` consolidates the Bernstein / rational
plumbing that lived in `Bezier3Length.v`, `NurbsQuadraticLength.v`,
and `NurbsGeneralLength.v`.  Public names stay (`bern2_*`, `bern3_*`,
`bezier3_c0/c1/c2`, `norm_triple_le`, `nurbs2_den_lb`).  Elevation
exactness is the n=2 instance of `elevate_ctrl` via `bern_elevate_2`.
Non-negativity is `Rmult_le_pos` / `lra` — Flocq 4.2.1 `nra` cannot
find a cubic witness (CI death on 48a5c3f). Does not retire epic 508.
Wrap-up is #566.

## 508 QED ∨ QEX stop

`theories/ExactCurveEpic508.v` is the ticket-named stop (same shape
as #522 / #523). QED is zoo-on-`CurveSegment`. QEX is a documented
missing constructor. Discharged QEX on the ellipse — the issue's
carrier blocker (`CSChord | CSArc`). Chord and circular-arc inhabit;
every inhabitant is one of those two. Not a `CurveSegment` remint.
Not an Exact* zoo type. QEX is not owner accept. Does not steal
508-e / 508-g / 508-h. Wrap-up is #566.
