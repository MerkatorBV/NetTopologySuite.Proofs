(* ============================================================================
   NetTopologySuite.Proofs.ArcParamBridge
   ----------------------------------------------------------------------------
   Issue #508, the "Also owed" bridge: the 3-point CircularArc model meets
   the parameterized-circle model — and through it, the CurveLength spec.

   ArcRectifiable.v proved r·θ is the metric length of the PARAMETERIZED
   circle t ↦ O + r·(cos t, sin t).  The engines and the corpus's CircularArc
   carry arcs as 3 points (start/mid/end) instead, with the central sweep
   `arc_sweep_angle` recovered through atan2 / `angle_between`.  This file
   connects the two: for a `valid_arc`, the principal sweep is REALIZED by a
   parameter interval of the circumscribed circle — the interval's circle
   points are exactly `arc_start`/`arc_end` (in sweep orientation), its width
   is `|arc_sweep_angle|`, and its metric length in the `is_curve_length`
   sense is exactly `arc_length (arc_radius a) (Rabs (arc_sweep_angle a))` —
   the number `ARC_LENGTH` emits and `arc_chord_le_arc_length` bounds.

   Proof route (branch-cut-free): anchor the start angle with
   `atan2_on_circle`; rotate onto the end point by `cos_plus`/`sin_plus`
   against the `cos_angle_between`/`sin_angle_between` characterisations —
   the mixed terms cancel through ux(ux·vx + uy·vy) − uy(ux·vy − uy·vx)
   = (ux² + uy²)·vx, so no atan2 difference identity is ever needed.

   Assumption footprint: 4-axiom — `atan2` facts pull
   `Classical_Prop.classic` (same lineage as Atan2.v / AngleBetween.v /
   RelateArcAnalytic.v / ArcChordLength.v).  Exempted in
   docs/audit-exceptions.txt accordingly.

   Deliberately NOT this file: the mid-point-disambiguated MAJOR traversal
   (`arc_sweep`, |sweep| possibly > π) — that reflex case is the next rung.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcChordApprox
                               Atan2 AngleBetween RelateArcAnalytic
                               ArcLength CurveLength ArcRectifiable.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Headline: the principal sweep of a 3-point arc is realized on its          *)
(* circumscribed circle with metric length arc_length r |sweep|.              *)
(* -------------------------------------------------------------------------- *)

Theorem arc_sweep_param_bridge : forall a : CircularArc,
  valid_arc a ->
  exists s t : R,
    s <= t /\
    t - s = Rabs (arc_sweep_angle a) /\
    ((circle_pt (arc_center a) (arc_radius a) s = arc_start a /\
      circle_pt (arc_center a) (arc_radius a) t = arc_end a) \/
     (circle_pt (arc_center a) (arc_radius a) s = arc_end a /\
      circle_pt (arc_center a) (arc_radius a) t = arc_start a)) /\
    is_curve_length (circle_param (arc_center a) (arc_radius a)) s t
                    (arc_length (arc_radius a) (Rabs (arc_sweep_angle a))).
Proof.
Qed.

Print Assumptions arc_sweep_param_bridge.
