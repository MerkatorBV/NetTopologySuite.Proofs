(* ==========================================================================
   WalkChainInduction.v

   [H-bridge attack, C-3f step 1(ii)] The ORBIT-CHAIN INDUCTION: folding
   the per-step glue (`WalkStepChain.walk_step_connected`) over the face
   walk `x_i = iter (fstep D) i d` connects the base sample of `d` to
   the base sample of `iter (fstep D) k d` -- for `k` from
   `same_face_twin_first_step_index`, that is the base sample of
   `twin d`, i.e. the east side of `d`.

   Statement discipline:
     - the per-step parameters are TWO FUNCTIONS `rho_out rho_in : nat
       -> R` (the base-sample and tip-sample rho of step i), so the
       step lemma's (rho0, rho1, rho2) triple is (rho_out i, rho_in i,
       rho_out (S i)) and the induction carries NO index arithmetic;
     - `delta` stays one global value (the shared-delta discipline of
       step 1(i)); the ride and corner legs stay caller-side hypothesis
       FAMILIES (forall i < k, ...), each instance supplied
       per-orientation by the banked C-3e/C-3d theorems under that
       step's thresholds -- discharging them for the concrete walk is
       step 1(iii)'s business;
     - the base case is reflexivity of the connectedness relation at
       the start sample, so ONE `ring_complement` fact for the start
       point is the only k-independent input.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Direction Dart DartAngularOrder DartNext
                               DartNextSpec DartFace OrbitCycle
                               PointInRingTangents JordanCurveSeam JCT
                               JCTHugStep RingClearance SectorPath
                               CornerSamples CornerConnector FanGapSector
                               FanCorner JCTCorridor MirrorCorridor
                               CornerCorridorBridge WalkStepChain.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The chain induction.                                                    *)
(* -------------------------------------------------------------------------- *)

Theorem walk_chain_connected :
  forall (r : Ring) (D : list Dart) (d : Dart) (k : nat)
         (rho_out rho_in : nat -> R) (delta : R),
    ring_complement r
      (point_at (dbase d)
         (corner_sample_out (ddir d) (rho_out 0%nat) delta)) ->
    (forall i, (i < k)%nat -> In (twin (iter (fstep D) i d)) D) ->
    (* the ride of x_i (C-3e, per-orientation, shared delta) *)
    (forall i, (i < k)%nat ->
       connected_in_complement_cont r
         (point_at (dbase (iter (fstep D) i d))
            (corner_sample_out (ddir (iter (fstep D) i d))
               (rho_out i) delta))
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_in
               (point_diff (dbase (iter (fstep D) i d))
                           (dtip (iter (fstep D) i d)))
               (rho_in i) delta))) ->
    (* the fan corner at dtip x_i (C-3d, explicit parameters) *)
    (forall i, (i < k)%nat ->
       connected_in_complement_cont r
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_in (ddir (twin (iter (fstep D) i d)))
               (rho_in i) delta))
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_out (ddir (fstep D (iter (fstep D) i d)))
               (rho_out (S i)) delta))) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) (rho_out 0%nat) delta))
      (point_at (dbase (iter (fstep D) k d))
         (corner_sample_out (ddir (iter (fstep D) k d))
            (rho_out k) delta)).
Proof.
  intros r D d k rho_out rho_in delta Hstart Htw Hride Hcorner.
  revert Htw Hride Hcorner.
  induction k as [| k IH]; intros Htw Hride Hcorner.
  - (* k = 0: the chain is the start sample itself *)
    cbn [iter].
    apply connected_in_complement_cont_refl.
    exact Hstart.
  - (* k -> S k: chain to x_k, then one more glue step *)
    cbn [iter].
    eapply connected_in_complement_cont_trans.
    + apply IH.
      * intros i Hi. apply Htw. lia.
      * intros i Hi. apply Hride. lia.
      * intros i Hi. apply Hcorner. lia.
    + apply (walk_step_connected r D (iter (fstep D) k d)
               (rho_out k) (rho_in k) (rho_out (S k)) delta).
      * apply Htw. lia.
      * apply Hride. lia.
      * apply Hcorner. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  At the same-face index, the chain ends at twin d's base sample.         *)
(* -------------------------------------------------------------------------- *)

(* Specialization: when `iter (fstep D) k d = twin d` (the index from
   `same_face_twin_first_step_index`), the chain connects d's base-side
   sample to TWIN d's base-side sample -- the two face-side parkings the
   end ties of step 1(iii) will hook to the -/+ef straddle points. *)
Corollary walk_chain_to_twin :
  forall (r : Ring) (D : list Dart) (d : Dart) (k : nat)
         (rho_out rho_in : nat -> R) (delta : R),
    iter (fstep D) k d = twin d ->
    ring_complement r
      (point_at (dbase d)
         (corner_sample_out (ddir d) (rho_out 0%nat) delta)) ->
    (forall i, (i < k)%nat -> In (twin (iter (fstep D) i d)) D) ->
    (forall i, (i < k)%nat ->
       connected_in_complement_cont r
         (point_at (dbase (iter (fstep D) i d))
            (corner_sample_out (ddir (iter (fstep D) i d))
               (rho_out i) delta))
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_in
               (point_diff (dbase (iter (fstep D) i d))
                           (dtip (iter (fstep D) i d)))
               (rho_in i) delta))) ->
    (forall i, (i < k)%nat ->
       connected_in_complement_cont r
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_in (ddir (twin (iter (fstep D) i d)))
               (rho_in i) delta))
         (point_at (dtip (iter (fstep D) i d))
            (corner_sample_out (ddir (fstep D (iter (fstep D) i d)))
               (rho_out (S i)) delta))) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) (rho_out 0%nat) delta))
      (point_at (dtip d)
         (corner_sample_out (ddir (twin d)) (rho_out k) delta)).
Proof.
  intros r D d k rho_out rho_in delta Hret Hstart Htw Hride Hcorner.
  pose proof (walk_chain_connected r D d k rho_out rho_in delta
                Hstart Htw Hride Hcorner) as Hchain.
  rewrite Hret in Hchain.
  rewrite dbase_twin in Hchain.
  exact Hchain.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Induction + transitivity; allowlist axioms only.              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions walk_chain_connected.
Print Assumptions walk_chain_to_twin.
