(* ==========================================================================
   WalkAssembly.v

   [H-bridge attack, C-3f step 1(iv)] THE ASSEMBLY: orbit chain + two
   end ties = the premise's straddle pair is CONNECTED in the ring
   complement; `parity_constant_on_components` then delivers exactly
   `face_transport_premise`'s parity conclusion.

   For a DESCENDING d (ascending mirrored), with ONE shared corner
   delta `corner_delta_for_ef_west d ef` (= `corner_delta_for_ef_east
   (twin d) ef` by the WalkEndTies consistency identity):

     (X - ef, my)                                       (X + ef, my)
        ^                                                   ^
        | west tie (along_dart_base_to_straddle_west)       | east tie
        |                                                   | (twin_base_
     d's base sample --- walk_chain_to_twin ---> twin d's   |  to_straddle
                        (k rides + k corners)   base sample-+   _east)

   All heavy inputs stay caller-side hypothesis FAMILIES (the per-step
   rides/corners, the tie clearances, the start complement) -- their
   concrete discharge for the cycle ring, from the C-3c/C-3d threshold
   theorems and the twin-aware guards, is the NEXT rung.  What this
   file settles is that nothing else is needed: the shapes compose, and
   the conclusion is literally the premise's biconditional.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import OverlayGraph Vec Azimuth Direction Dart
                               DartAngularOrder DartNext DartNextSpec DartFace
                               OrbitCycle JCTSeparation JCTHugStep
                               RingClearance SectorPath CornerSamples
                               CornerConnector JCTCorridor WalkCorridor
                               MirrorCorridor DartSideKit CornerCorridorBridge
                               HandoffConnector C3eEfCorridorAssumption
                               BaseToTipHeadline WalkStepChain
                               WalkChainInduction WalkEndTies.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  DESCENDING d: the straddle pair is connected in the complement.         *)
(* -------------------------------------------------------------------------- *)

Theorem walk_straddle_connected_desc :
  forall (r : Ring) (D : list Dart) (d : Dart) (k : nat)
         (rho_out rho_in : nat -> R) (ef my h_w h_e : R),
    vy (ddir d) < 0 ->
    iter (fstep D) k d = twin d ->
    (* the chain inputs (WalkChainInduction), at the shared delta *)
    ring_complement r
      (point_at (dbase d)
         (corner_sample_out (ddir d) (rho_out 0%nat)
            (corner_delta_for_ef_west d ef))) ->
    (forall i, (i < k)%nat -> In (twin (iter (fstep D) i d)) D) ->
    (forall i, (i < k)%nat ->
       connected_in_complement_cont r
         (point_at (dbase (iter (fstep D) i d))
            (corner_sample_out (ddir (iter (fstep D) i d))
               (rho_out i) (corner_delta_for_ef_west d ef)))
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_in
               (point_diff (dbase (iter (fstep D) i d))
                           (dtip (iter (fstep D) i d)))
               (rho_in i) (corner_delta_for_ef_west d ef)))) ->
    (forall i, (i < k)%nat ->
       connected_in_complement_cont r
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_in (ddir (twin (iter (fstep D) i d)))
               (rho_in i) (corner_delta_for_ef_west d ef)))
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_out (ddir (fstep D (iter (fstep D) i d)))
               (rho_out (S i)) (corner_delta_for_ef_west d ef)))) ->
    (* the west tie (d's own ride down to the -ef point) *)
    h_w = bridge_height_base d (rho_out 0%nat)
            (corner_delta_for_ef_west d ef) ->
    h_w <= my ->
    (forall y, h_w <= y <= my -> ~ ring_image r (corridor d ef y)) ->
    (* the east tie (twin d's ride down to the +ef point) *)
    h_e = bridge_height_base (twin d) (rho_out k)
            (corner_delta_for_ef_west d ef) ->
    h_e <= my ->
    (forall y, h_e <= y <= my -> ~ ring_image r (corridor_east d ef y)) ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at d my - ef) my)
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r D d k rho_out rho_in ef my h_w h_e
         Hdesc Hret Hstart Htw Hride Hcorner
         Hhw Hlew Hclw Hhe Hlee Hcle.
  pose proof (walk_chain_to_twin r D d k rho_out rho_in
                (corner_delta_for_ef_west d ef)
                Hret Hstart Htw Hride Hcorner) as Hchain.
  pose proof (along_dart_base_to_straddle_west r d (rho_out 0%nat) ef my h_w
                Hdesc Hhw Hlew Hclw) as Hwest.
  pose proof (twin_base_to_straddle_east r d (rho_out k) ef my h_e
                Hdesc Hhe Hlee Hcle) as Heast.
  apply connected_in_complement_cont_sym in Hwest.
  eapply connected_in_complement_cont_trans; [ exact Hwest | ].
  eapply connected_in_complement_cont_trans; [ exact Hchain | ].
  exact Heast.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  ASCENDING d: the mirror (d's face side is east; twin's is west).        *)
(* -------------------------------------------------------------------------- *)

Theorem walk_straddle_connected_asc :
  forall (r : Ring) (D : list Dart) (d : Dart) (k : nat)
         (rho_out rho_in : nat -> R) (ef my h_w h_e : R),
    0 < vy (ddir d) ->
    iter (fstep D) k d = twin d ->
    ring_complement r
      (point_at (dbase d)
         (corner_sample_out (ddir d) (rho_out 0%nat)
            (corner_delta_for_ef_east d ef))) ->
    (forall i, (i < k)%nat -> In (twin (iter (fstep D) i d)) D) ->
    (forall i, (i < k)%nat ->
       connected_in_complement_cont r
         (point_at (dbase (iter (fstep D) i d))
            (corner_sample_out (ddir (iter (fstep D) i d))
               (rho_out i) (corner_delta_for_ef_east d ef)))
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_in
               (point_diff (dbase (iter (fstep D) i d))
                           (dtip (iter (fstep D) i d)))
               (rho_in i) (corner_delta_for_ef_east d ef)))) ->
    (forall i, (i < k)%nat ->
       connected_in_complement_cont r
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_in (ddir (twin (iter (fstep D) i d)))
               (rho_in i) (corner_delta_for_ef_east d ef)))
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_out (ddir (fstep D (iter (fstep D) i d)))
               (rho_out (S i)) (corner_delta_for_ef_east d ef)))) ->
    (* the east tie: d's own ride to the +ef point *)
    h_e = bridge_height_base d (rho_out 0%nat)
            (corner_delta_for_ef_east d ef) ->
    h_e <= my ->
    (forall y, h_e <= y <= my -> ~ ring_image r (corridor_east d ef y)) ->
    (* the west tie: twin d's ride to the -ef point *)
    h_w = bridge_height_base (twin d) (rho_out k)
            (corner_delta_for_ef_east d ef) ->
    h_w <= my ->
    (forall y, h_w <= y <= my -> ~ ring_image r (corridor d ef y)) ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at d my - ef) my)
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r D d k rho_out rho_in ef my h_w h_e
         Hasc Hret Hstart Htw Hride Hcorner
         Hhe Hlee Hcle Hhw Hlew Hclw.
  pose proof (walk_chain_to_twin r D d k rho_out rho_in
                (corner_delta_for_ef_east d ef)
                Hret Hstart Htw Hride Hcorner) as Hchain.
  pose proof (along_dart_base_to_straddle_east r d (rho_out 0%nat) ef my h_e
                Hasc Hhe Hlee Hcle) as Heast.
  pose proof (twin_base_to_straddle_west r d (rho_out k) ef my h_w
                Hasc Hhw Hlew Hclw) as Hwest.
  apply connected_in_complement_cont_sym in Hwest.
  eapply connected_in_complement_cont_trans; [ exact Hwest | ].
  apply connected_in_complement_cont_sym in Hchain.
  eapply connected_in_complement_cont_trans; [ exact Hchain | ].
  exact Heast.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The parity close: exactly the premise's biconditional.                  *)
(* -------------------------------------------------------------------------- *)

Corollary walk_straddle_parity :
  forall (r : Ring) (d : Dart) (ef my : R),
    ring_closed r ->
    ray_avoids_vertices (mkPoint (edge_x_at d my - ef) my) r ->
    ray_avoids_vertices (mkPoint (edge_x_at d my + ef) my) r ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at d my - ef) my)
      (mkPoint (edge_x_at d my + ef) my) ->
    (point_in_ring (mkPoint (edge_x_at d my - ef) my) r
       <-> point_in_ring (mkPoint (edge_x_at d my + ef) my) r).
Proof.
  intros r d ef my Hclosed Hav1 Hav2 Hconn.
  exact (parity_constant_on_components r _ _ Hclosed Hav1 Hav2 Hconn).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Assembly wiring; allowlist axioms only.                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions walk_straddle_connected_desc.
Print Assumptions walk_straddle_connected_asc.
Print Assumptions walk_straddle_parity.
