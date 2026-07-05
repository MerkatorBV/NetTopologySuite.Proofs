(* ============================================================================
   NetTopologySuite.Proofs.ArcMinorWitness
   ----------------------------------------------------------------------------
   Companion counterexample for `ArcOrient.arc_minor`, in the style of
   `SpectreChordArcWitness.v`: a concrete valid arc where `arc_mid` sits on
   the MAJOR side of the chord (subtended angle > pi), exhibiting concretely
   that the sagitta bound (`ArcChordApprox.sagitta`) does NOT bound the arc's
   distance from its own chord SEGMENT when `arc_minor` fails.

   THE WITNESS.  Take the three control points (1,0), (-1,0), (0,1) -- all on
   the unit circle centred at the origin (arc_center = (0,0), arc_radius = 1).
   The chord is the segment (1,0)-(0,1).  `arc_mid = (-1,0)` sits on the
   OPPOSITE side of the chord from the circumcenter's "expected" minor-arc
   placement -- concretely, `arc_side_chord` at the center and at `arc_mid`
   have the SAME sign (both positive), so `arc_minor` (which requires opposite
   signs, i.e. product <= 0) is FALSE here.  This is the "major" labeling:
   the three control points trace the long way (270 degrees) around the
   circle from start to end.

   `arc_mid` is trivially on its own arc (on-circle and in-span by
   construction, `ArcIntersect.arc_span_contains_mid`), so it is a genuine
   point of the arc.  Its distance to the chord SEGMENT (1,0)-(0,1) is
   UNCONDITIONALLY (for every parameter t, not just t in [0,1]) at least
   sqrt 2 -- via the identity `dist_sq(mid, segment_point t) - 2 = 2*(t-1)^2
   >= 0`.  The sagitta here is `1 - sqrt(1/2) < 1`, so `sagitta^2 < 2`: the
   sagitta bound fails to cover this arc point by a wide margin.

   Pure `R`; no Admitted / Axiom / Parameter.  Standard three-axiom
   classical-reals base (lra / nra / ring / field only).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveGeometry ArcOrient ArcChordApprox HotPixel.
Local Open Scope R_scope.

Definition major_arc_witness : CircularArc :=
  mkCircularArc (mkPoint 1 0) (mkPoint (-1) 0) (mkPoint 0 1).

Lemma major_arc_witness_valid : valid_arc major_arc_witness.
Proof. unfold valid_arc, major_arc_witness; cbn [arc_start arc_mid arc_end px py]; lra. Qed.

Lemma major_arc_witness_center :
  arc_center major_arc_witness = mkPoint 0 0.
Proof.
  unfold arc_center, major_arc_witness; cbn [arc_start arc_mid arc_end px py].
  f_equal; field.
Qed.

(* The circumcenter and `arc_mid` are on the SAME side of the chord: their
   `arc_side_chord` values are both positive, so `arc_minor` (product <= 0)
   fails. *)
Theorem major_arc_witness_not_minor : ~ arc_minor major_arc_witness.
Proof.
  unfold arc_minor, arc_side_chord, cross_R_pt.
  rewrite major_arc_witness_center.
  unfold major_arc_witness.
  cbn [arc_start arc_mid arc_end px py].
  lra.
Qed.

(* `arc_mid` (a genuine point of the arc, on-circle and in-span by
   construction) is at distance >= sqrt 2 from EVERY point of the chord
   segment (1,0)-(0,1) -- not just the closest one. *)
Theorem major_arc_witness_mid_far_from_chord :
  forall t : R,
    2 <= dist_sq (mkPoint (-1) 0)
                 (segment_point (mkPoint 1 0) (mkPoint 0 1) t).
Proof.
  intro t. unfold dist_sq, segment_point; cbn [px py].
  pose proof (sqr_nonneg (t - 1)) as Hsq.
  nra.
Qed.

Theorem major_arc_witness_radius : arc_radius major_arc_witness = 1.
Proof.
  unfold arc_radius, dist.
  rewrite major_arc_witness_center.
  unfold major_arc_witness. cbn [arc_start arc_mid arc_end px py].
  replace (dist_sq (mkPoint 0 0) (mkPoint 1 0)) with 1
    by (unfold dist_sq; cbn [px py]; lra).
  exact sqrt_1.
Qed.

(* The sagitta is strictly less than sqrt 2 in squared form: sagitta^2 < 2.
   So the naive "arc point within sagitta of the chord segment" bound is
   false here by a wide margin (the actual distance is >= sqrt 2, the
   sagitta budget is <= arc_radius = 1 < sqrt 2).  Reuses the corpus's own
   `sagitta_nonneg`/`sagitta_le_arc_radius`, no need to recompute the exact
   sagitta value. *)
Theorem major_arc_witness_sagitta_lt_sqrt2_sq :
  sagitta major_arc_witness * sagitta major_arc_witness < 2.
Proof.
  pose proof (sagitta_nonneg major_arc_witness) as Hnn.
  pose proof (sagitta_le_arc_radius major_arc_witness) as Hle.
  rewrite major_arc_witness_radius in Hle.
  nra.
Qed.

(* Assembled counterexample: the naive claim "every arc point is within
   sagitta of some point of the chord segment" is FALSE for `arc_mid` on
   this major-labeled arc. *)
Theorem major_arc_witness_naive_bound_fails :
  ~ exists t : R,
      0 <= t <= 1 /\
      dist_sq (arc_mid major_arc_witness)
              (segment_point (arc_start major_arc_witness) (arc_end major_arc_witness) t)
      <= sagitta major_arc_witness * sagitta major_arc_witness.
Proof.
  intros [t [_ Hle]].
  unfold major_arc_witness in Hle at 1 2 3.
  cbn [arc_start arc_mid arc_end] in Hle.
  pose proof (major_arc_witness_mid_far_from_chord t) as Hfar.
  pose proof major_arc_witness_sagitta_lt_sqrt2_sq as Hsag.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions major_arc_witness_valid.
Print Assumptions major_arc_witness_center.
Print Assumptions major_arc_witness_not_minor.
Print Assumptions major_arc_witness_radius.
Print Assumptions major_arc_witness_mid_far_from_chord.
Print Assumptions major_arc_witness_sagitta_lt_sqrt2_sq.
Print Assumptions major_arc_witness_naive_bound_fails.
