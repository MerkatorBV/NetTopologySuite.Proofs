(* ============================================================================
   NetTopologySuite.Proofs.ArcTraversalBridge
   ----------------------------------------------------------------------------
   Issue #508 arc-lane final rung: the MID-DISAMBIGUATED traversal — the
   directed central angle `arc_sweep` (RelateArcAnalytic), which passes
   through `arc_mid` and may be REFLEX (π < |sweep| < 2π) — is realized on
   the circumscribed circle with metric length
   `arc_length (arc_radius a) (Rabs (arc_sweep a))` in the
   `is_curve_length` sense.

   ArcParamBridge.v realized the PRINCIPAL sweep (|sweep| ≤ π).  The engines'
   major arcs traverse the other way around: `arc_sweep` adjusts the
   principal angle by ±2π when `arc_mid` lies in the reflex sector.  Since
   `cos`/`sin` are 2π-periodic, the SAME anchor endpoints realize the
   adjusted sweep — `arc_sweep_cases` enumerates the definition's four
   outcomes (θ, θ − 2π, θ + 2π, 0), periodicity shifts the anchor, and
   `realize_sweep` assembles the oriented interval.

   Scope honesty: this realizes whatever traversal `arc_sweep`'s definition
   chose; the geometric statement that the chosen traversal passes through
   `arc_mid` (a point-set claim about the parameter interval) is a separate
   future rung.  The `arc_sweep a = 0` outcome is excluded by hypothesis —
   under `valid_arc` it would force `arc_end = arc_start` (informally); the
   formal nonzero pin is likewise future work.

   Assumption footprint: 4-axiom (inherits the atan2 lane through
   ArcParamBridge).  Exempted in docs/audit-exceptions.txt.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry Atan2 AngleBetween
                               RelateArcAnalytic ArcLength CurveLength
                               ArcRectifiable ArcParamBridge.
Local Open Scope R_scope.

(* 2π-periodicity of the circle parameterization. *)
Lemma circle_pt_add_2PI : forall (Oc : Point) r t,
  circle_pt Oc r (t + 2 * PI) = circle_pt Oc r t.
Proof.
Qed.

Lemma circle_pt_sub_2PI : forall (Oc : Point) r t,
  circle_pt Oc r (t - 2 * PI) = circle_pt Oc r t.
Proof.
Qed.

(* The four outcomes of arc_sweep's decision tree. *)
Lemma arc_sweep_cases : forall a : CircularArc,
  arc_sweep a = arc_sweep_angle a \/
  arc_sweep a = arc_sweep_angle a - 2 * PI \/
  arc_sweep a = arc_sweep_angle a + 2 * PI \/
  arc_sweep a = 0.
Proof.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: the mid-disambiguated traversal is realized on the circle.       *)
(* -------------------------------------------------------------------------- *)

Theorem arc_traversal_param_bridge : forall a : CircularArc,
  valid_arc a ->
  arc_sweep a <> 0 ->
  exists s t : R,
    s <= t /\
    t - s = Rabs (arc_sweep a) /\
    ((circle_pt (arc_center a) (arc_radius a) s = arc_start a /\
      circle_pt (arc_center a) (arc_radius a) t = arc_end a) \/
     (circle_pt (arc_center a) (arc_radius a) s = arc_end a /\
      circle_pt (arc_center a) (arc_radius a) t = arc_start a)) /\
    is_curve_length (circle_param (arc_center a) (arc_radius a)) s t
                    (arc_length (arc_radius a) (Rabs (arc_sweep a))).
Proof.
Qed.

Print Assumptions arc_traversal_param_bridge.
