(* ==========================================================================
   C-3e-ef-corridor-assumption.v

   C-3e open design note (post-PR#339) and the tiny safety probe for the
   ef-vs-corridor threshold relation.  No new axioms; the load-bearing
   closure is recorded here for the concurrent handoff-connector track.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

(* C-3e open design note (post-PR#339)
   Both tracks currently connect only d's own two corner samples via corridor.
   Target for face_transport_premise: (edge_x_at d my - ef, my) and +ef.
   Question: corridor.safe_offset guarantees delta < threshold, but ef comes from
   straddle_side_core with no explicit relation yet.
   Proposed closure: prove ∃ ε₀ > 0, ∀ ef < ε₀, corridor argument still holds
   (standard "sufficiently small" + triangle-inequality chaining). *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents
                               JCTCorridor WalkCorridor MirrorCorridor.

Import ListNotations.
Local Open Scope R_scope.

(* Uniform corridor clearance from `walk_dart_corridor_clear` / east mirror. *)
Definition corridor_safe_threshold
  (delta0 : R) : R := delta0.

Definition corridor_safe_half (delta0 : R) : R := delta0 / 2.

(* The straddle offset ef sits below the corridor half-threshold, hence below
   delta0 itself: the same uniform clearance window applies with delta := ef. *)
Lemma corridor_absorbs_ef :
  forall (delta0 ef : R),
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_half delta0 ->
    0 < ef /\ ef < delta0.
Proof.
  intros delta0 ef Hd0 Hef Hhalf.
  split; [ exact Hef | ]. lra.
Qed.

(* Headline-shaped probe: any ef below half of a walk-dart delta0 inherits the
   corridor's ring-freedom at every height in the window. *)
Lemma corridor_ef_inherits_clearance :
  forall (x : Dart) (r : Ring) (delta0 ef y ylo yhi : R),
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_half delta0 ->
    ylo <= yhi ->
    (forall delta, 0 < delta < delta0 ->
       forall y', ylo <= y' <= yhi ->
         ~ ring_image r (corridor x delta y')) ->
    ylo <= y <= yhi ->
    ~ ring_image r (corridor x ef y).
Proof.
  intros x r delta0 ef y ylo yhi Hd0 Hef Hhalf Hle Hclear Hy.
  assert (Hef_lt : ef < delta0) by lra.
  exact (Hclear ef Hef_lt y Hy).
Qed.

Lemma corridor_ef_inherits_clearance_east :
  forall (x : Dart) (r : Ring) (delta0 ef y ylo yhi : R),
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_half delta0 ->
    ylo <= yhi ->
    (forall delta, 0 < delta < delta0 ->
       forall y', ylo <= y' <= yhi ->
         ~ ring_image r (corridor_east x delta y')) ->
    ylo <= y <= yhi ->
    ~ ring_image r (corridor_east x ef y).
Proof.
  intros x r delta0 ef y ylo yhi Hd0 Hef Hhalf Hle Hclear Hy.
  assert (Hef_lt : ef < delta0) by lra.
  exact (Hclear ef Hef_lt y Hy).
Qed.

(* Straddle west sample = west corridor point at the same offset. *)
Lemma straddle_west_eq_corridor :
  forall (d : Dart) (my ef : R),
    corridor d ef my = mkPoint (edge_x_at d my - ef) my.
Proof.
  intros d my ef. unfold corridor. reflexivity.
Qed.

Lemma straddle_east_eq_corridor_east :
  forall (d : Dart) (my ef : R),
    corridor_east d ef my = mkPoint (edge_x_at d my + ef) my.
Proof.
  intros d my ef. unfold corridor_east. reflexivity.
Qed.

Print Assumptions corridor_absorbs_ef.
Print Assumptions corridor_ef_inherits_clearance.
Print Assumptions straddle_west_eq_corridor.