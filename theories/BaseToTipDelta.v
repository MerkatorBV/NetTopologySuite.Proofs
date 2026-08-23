(* ==========================================================================
   BaseToTipDelta.v

   [C-3e step C, layer 1] Bridge deltas and heights: the corridor offset
   produced by corner parameters, the ef-matched corner deltas, and the
   ddir nonzero guard.  Gains its own Print Assumptions footer (the
   monolith printed none for this layer) per the no-footer audit rule
   from the 2026-08-16 categorisation pass: every module prints its own
   leaves.

   Split out of the former 1574-line BaseToTipHeadline.v monolith
   (H-bridge attack, C-3e step C); BaseToTipHeadline.v remains as the
   Require Export umbrella, so importers are unaffected.  Slice text,
   declarations, and Print Assumptions footers carried over verbatim.
   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import OverlayGraph Vec Azimuth Direction Dart
                               DartAngularOrder JCTHugStep JCTMinOpenStep
                               JCTTautClearance JCTNesting GeneralTautBridge
                               RingClearance SectorPath CornerSamples
                               CornerConnector JCTCorridor StraddleSides
                               MirrorCorridor DartSideKit HandoffWedge
                               WalkCorridor FaceTwinAware HBridgeCoreSlice
                               RingExtract RectangleJCT.
From NTS.Proofs Require Export CornerCorridorBridge C3eEfCorridorAssumption
                               HandoffConnector.

Import ListNotations.
Local Open Scope R_scope.
(* §C-3e-C  Along-dart headline -> straddle (edge_x_at d my ± ef, my).        *)

(* -------------------------------------------------------------------------- *)

(* Bridge delta: the corridor offset produced by corner parameters. *)
Definition bridge_delta_west (d : Dart) (delta_c : R) : R :=
  delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
    / (- vy (ddir d)).

Definition bridge_delta_east (d : Dart) (delta_c : R) : R :=
  delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
    / vy (ddir d).

Definition bridge_height_base (d : Dart) (rho delta_c : R) : R :=
  py (dbase d) + (rho * vy (ddir d) - delta_c * vx (ddir d)).

Definition bridge_height_tip (d : Dart) (rho delta_c : R) : R :=
  py (dtip d) + (- rho * vy (ddir d) - delta_c * vx (ddir d)).

(* Corner delta that makes the bridge delta equal a target corridor offset `ef`. *)
Definition corner_delta_for_ef_west (d : Dart) (ef : R) : R :=
  ef * (- vy (ddir d))
    / (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d)).

Definition corner_delta_for_ef_east (d : Dart) (ef : R) : R :=
  ef * vy (ddir d)
    / (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d)).

Lemma ddir_sq_nez_of_vy_nez :
  forall (d : Dart), vy (ddir d) <> 0 ->
    vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d) <> 0.
Proof.
  intros d Hvy H0.
  apply Rplus_sqr_eq_0 in H0. destruct H0 as [_ Hvy0]. exact (Hvy Hvy0).
Qed.

Lemma bridge_delta_west_for_ef :
  forall (d : Dart) (ef : R), vy (ddir d) < 0 ->
    bridge_delta_west d (corner_delta_for_ef_west d ef) = ef.
Proof.
  intros d ef Hdesc.
  unfold bridge_delta_west, corner_delta_for_ef_west.
  assert (Hvy : vy (ddir d) <> 0)
    by (intro Hz; rewrite Hz in Hdesc; cbn in Hdesc; lra).
  assert (Hden := ddir_sq_nez_of_vy_nez d Hvy).
  field.
  - split; [ exact Hden | exact Hvy ].
Qed.

Lemma bridge_delta_east_for_ef :
  forall (d : Dart) (ef : R), vy (ddir d) > 0 ->
    bridge_delta_east d (corner_delta_for_ef_east d ef) = ef.
Proof.
  intros d ef Hasc.
  unfold bridge_delta_east, corner_delta_for_ef_east.
  assert (Hvy : vy (ddir d) <> 0)
    by (intro Hz; rewrite Hz in Hasc; cbn in Hasc; lra).
  assert (Hden := ddir_sq_nez_of_vy_nez d Hvy).
  field.
  - split; [ exact Hden | exact Hvy ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions ddir_sq_nez_of_vy_nez.
Print Assumptions bridge_delta_west_for_ef.
Print Assumptions bridge_delta_east_for_ef.
