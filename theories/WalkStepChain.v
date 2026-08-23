(* ==========================================================================
   WalkStepChain.v

   [H-bridge attack, C-3f step 1(i)] The PER-STEP GLUE of the orbit
   chain: one along-dart ride (C-3e) composed with one fan corner
   (C-3d) advances the connected chain from the base sample of a walk
   dart `x` to the base sample of its face-walk successor `fstep D x`.

   The content is deliberately thin -- pure alignment + transitivity --
   because the two heavy legs are already banked and the ONLY new facts
   a step needs are bookkeeping:

     - `walk_corner_walls`: `fstep D x` IS `next` of the tip fan at
       `twin x` (definitional), so the corner at `dtip x` instantiates
       `FanCorner`'s theorems with `F := outgoing (dtip x) D`,
       `a := twin x` -- the corner walls are `ddir (twin x)` and
       `ddir (fstep D x)`, exactly the machine-checked convention;
     - `twin_in_fan` / `dbase_fstep`: the arriving reversal is a fan
       member, and the successor is based at the shared vertex
       (`next_base`), so the next ride starts where the corner ends;
     - `tip_sample_wall_form`: the ride's tip sample
       (`corner_sample_in (point_diff (dbase x) (dtip x))`, the
       CornerCorridorBridge form) and the corner's wall-1 sample
       (`corner_sample_in (ddir (twin x))`, the FanCorner form) are the
       SAME point -- definitionally, `reflexivity`;
     - `walk_step_connected` (headline): ride + corner + one
       `connected_in_complement_cont_trans`.  The SHARED POINT of the
       two legs is the tip sample AT `dtip x`: the ride ends there in
       CornerCorridorBridge form, the corner starts there in FanCorner
       form, and `tip_sample_wall_form` says they are the same point;
       `dbase_fstep` then rewrites the corner's exit
       (`corner_sample_out (ddir (fstep D x))` at `dtip x`) into the
       next ride's base sample verbatim.  The SHARED-delta discipline
       is visible in the statement: the per-step `delta` is one global
       value along the chain (each ride needs it equal at both of its
       ends); the `rho_i` are free per-vertex.  The orbit induction
       (step 1(ii)) folds this lemma over `k` from
       `same_face_twin_first_step_index`.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import OverlayGraph Vec Azimuth Direction Dart
                               DartAngularOrder DartNext DartNextSpec DartFace
                               JCTHugStep RingClearance SectorPath
                               CornerSamples CornerConnector FanGapSector
                               FanCorner JCTCorridor MirrorCorridor
                               CornerCorridorBridge.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Walk-step bookkeeping: the corner at `dtip x` in fan terms.              *)
(* -------------------------------------------------------------------------- *)

(* The face-walk successor is the rotational `next` of the tip fan at the
   arriving reversal -- definitionally. *)
Lemma walk_corner_walls :
  forall (D : list Dart) (x : Dart),
    fstep D x = next (outgoing (dtip x) D) (twin x).
Proof. reflexivity. Qed.

(* The arriving reversal is a member of the tip fan. *)
Lemma twin_in_fan :
  forall (D : list Dart) (x : Dart),
    In (twin x) D -> In (twin x) (outgoing (dtip x) D).
Proof.
  intros D x Htw.
  apply in_outgoing. split; [ exact Htw | apply dbase_twin ].
Qed.

(* The successor is based at the shared vertex: the next ride starts
   where the corner ends. *)
Lemma dbase_fstep :
  forall (D : list Dart) (x : Dart),
    In (twin x) D -> dbase (fstep D x) = dtip x.
Proof.
  intros D x Htw.
  unfold fstep.
  apply next_base.
  apply twin_in_fan. exact Htw.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The two sample forms at the tip are the same point.                     *)
(* -------------------------------------------------------------------------- *)

(* The ride's tip sample (CornerCorridorBridge form) IS the corner's
   wall-1 sample (FanCorner form): `ddir (twin x)` unfolds to
   `point_diff (dbase x) (dtip x)`. *)
Lemma tip_sample_wall_form :
  forall (x : Dart) (rho delta : R),
    point_at (dtip x)
      (corner_sample_in (point_diff (dbase x) (dtip x)) rho delta)
    = point_at (dtip x) (corner_sample_in (ddir (twin x)) rho delta).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Headline: ride + corner = one walk step of the orbit chain.             *)
(* -------------------------------------------------------------------------- *)

Theorem walk_step_connected :
  forall (r : Ring) (D : list Dart) (x : Dart) (rho0 rho1 rho2 delta : R),
    In (twin x) D ->
    (* the along-dart ride of x (C-3e: along_dart_* with shared delta) *)
    connected_in_complement_cont r
      (point_at (dbase x) (corner_sample_out (ddir x) rho0 delta))
      (point_at (dtip x)
         (corner_sample_in (point_diff (dbase x) (dtip x)) rho1 delta)) ->
    (* the fan corner at dtip x (C-3d: fan_corner_connected_reflex /
       _convex with F := outgoing (dtip x) D, a := twin x) *)
    connected_in_complement_cont r
      (point_at (dtip x) (corner_sample_in (ddir (twin x)) rho1 delta))
      (point_at (dtip x) (corner_sample_out (ddir (fstep D x)) rho2 delta)) ->
    connected_in_complement_cont r
      (point_at (dbase x) (corner_sample_out (ddir x) rho0 delta))
      (point_at (dbase (fstep D x))
         (corner_sample_out (ddir (fstep D x)) rho2 delta)).
Proof.
  intros r D x rho0 rho1 rho2 delta Htw Hride Hcorner.
  (* align the endpoint: the successor is based at dtip x, so the
     conclusion's final sample is literally Hcorner's exit point *)
  rewrite (dbase_fstep D x Htw).
  (* chain through the shared tip sample; the ride's endpoint and the
     corner's entry are the same point definitionally
     (tip_sample_wall_form), so no rewrite is needed between the legs *)
  eapply connected_in_complement_cont_trans; [ exact Hride | ].
  exact Hcorner.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure bookkeeping + transitivity; allowlist axioms only.       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dbase_fstep.
Print Assumptions walk_step_connected.
