(* ==========================================================================
   BaseToTipAlongDart.v

   [C-3e step C, layer 2] The ALONG-DART HEADLINES: base/tip corner
   sample -> corridor ride -> straddle target at height my, composed by
   transitivity -- descending/west (SS1) and ascending/east mirror (SS2).

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
From NTS.Proofs Require Import BaseToTipDelta.

(* -------------------------------------------------------------------------- *)
(* §1  DESCENDING / west: base sample -> straddle west at `my`.                *)
(* -------------------------------------------------------------------------- *)

Theorem along_dart_base_to_straddle_west :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    h_base <= my ->
    (forall y, h_base <= y <= my ->
       ~ ring_image r (corridor d ef y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_west d ef)))
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros r d rho ef my h_base Hdesc Hhbase Hle Hclear.
  set (delta_c := corner_delta_for_ef_west d ef).
  assert (Hbase_eq :
    point_at (dbase d) (corner_sample_out (ddir d) rho delta_c)
      = corridor d ef h_base).
  { rewrite (handoff_base_bridge_west d rho delta_c Hdesc).
    change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
              / (- vy (ddir d))) with (bridge_delta_west d delta_c).
    change (py (dbase d) + (rho * vy (ddir d) - delta_c * vx (ddir d)))
      with (bridge_height_base d rho delta_c).
    assert (Hbd : bridge_delta_west d delta_c = ef)
      by (unfold delta_c; exact (bridge_delta_west_for_ef d ef Hdesc)).
    assert (Hbh : bridge_height_base d rho delta_c = h_base)
      by (unfold delta_c; symmetry; exact Hhbase).
    rewrite Hbd, Hbh. reflexivity. }
  assert (Hride : connected_in_complement_cont r (corridor d ef h_base)
                    (corridor d ef my)).
  { assert (Hnh : py (dbase d) <> py (dtip d)).
    { intro Heq. pose proof (dart_descend_tip_below_base d Hdesc) as Hwest.
      rewrite Heq in Hwest. lra. }
    apply connected_in_complement_cont_sym.
    exact (corridor_connected r d h_base my ef Hnh Hle Hclear). }
  rewrite Hbase_eq, <- straddle_west_eq_corridor.
  exact Hride.
Qed.

(* DESCENDING / west: tip sample -> straddle west at `my`. *)
Theorem along_dart_tip_to_straddle_west :
  forall (r : Ring) (d : Dart) (rho ef my h_tip : R),
    vy (ddir d) < 0 ->
    my <= h_tip ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    (forall y, my <= y <= h_tip ->
       ~ ring_image r (corridor d ef y)) ->
    connected_in_complement_cont r
      (point_at (dtip d)
         (corner_sample_in (point_diff (dbase d) (dtip d)) rho
            (corner_delta_for_ef_west d ef)))
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros r d rho ef my h_tip Hdesc Hle Hhtip Hclear.
  set (delta_c := corner_delta_for_ef_west d ef).
  assert (Htip_eq :
    point_at (dtip d)
      (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta_c)
      = corridor d ef h_tip).
  { rewrite (handoff_tip_bridge_west d rho delta_c Hdesc).
    change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
              / (- vy (ddir d))) with (bridge_delta_west d delta_c).
    change (py (dtip d) + (- rho * vy (ddir d) - delta_c * vx (ddir d)))
      with (bridge_height_tip d rho delta_c).
    assert (Hbd : bridge_delta_west d delta_c = ef)
      by (unfold delta_c; exact (bridge_delta_west_for_ef d ef Hdesc)).
    assert (Hth : bridge_height_tip d rho delta_c = h_tip)
      by (unfold delta_c; symmetry; exact Hhtip).
    rewrite Hbd, Hth. reflexivity. }
  assert (Hride : connected_in_complement_cont r (corridor d ef my)
                    (corridor d ef h_tip)).
  { assert (Hnh : py (dbase d) <> py (dtip d)).
    { intro Heq. pose proof (dart_descend_tip_below_base d Hdesc) as Hwest.
      rewrite Heq in Hwest. lra. }
    apply connected_in_complement_cont_sym.
    exact (corridor_connected r d my h_tip ef Hnh Hle Hclear). }
  apply connected_in_complement_cont_sym in Hride.
  rewrite <- Htip_eq in Hride.
  rewrite straddle_west_eq_corridor in Hride.
  exact Hride.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  ASCENDING / east mirror.                                                *)
(* -------------------------------------------------------------------------- *)

Theorem along_dart_base_to_straddle_east :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    h_base <= my ->
    (forall y, h_base <= y <= my ->
       ~ ring_image r (corridor_east d ef y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_east d ef)))
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r d rho ef my h_base Hasc Hhbase Hle Hclear.
  set (delta_c := corner_delta_for_ef_east d ef).
  assert (Hbase_eq :
    point_at (dbase d) (corner_sample_out (ddir d) rho delta_c)
      = corridor_east d ef h_base).
  { rewrite (handoff_base_bridge_east d rho delta_c Hasc).
    change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
              / vy (ddir d)) with (bridge_delta_east d delta_c).
    change (py (dbase d) + (rho * vy (ddir d) - delta_c * vx (ddir d)))
      with (bridge_height_base d rho delta_c).
    assert (Hbd : bridge_delta_east d delta_c = ef)
      by (unfold delta_c; exact (bridge_delta_east_for_ef d ef Hasc)).
    assert (Hbh : bridge_height_base d rho delta_c = h_base)
      by (unfold delta_c; symmetry; exact Hhbase).
    rewrite Hbd, Hbh. reflexivity. }
  assert (Hride : connected_in_complement_cont r (corridor_east d ef h_base)
                    (corridor_east d ef my)).
  { assert (Hnh : py (dbase d) <> py (dtip d)).
    { intro Heq. pose proof (dart_ascend_base_below_tip d Hasc) as Hasc'.
      rewrite Heq in Hasc'. lra. }
    apply connected_in_complement_cont_sym.
    exact (corridor_connected_east r d h_base my ef Hnh Hle Hclear). }
  rewrite Hbase_eq, <- straddle_east_eq_corridor_east.
  exact Hride.
Qed.

Theorem along_dart_tip_to_straddle_east :
  forall (r : Ring) (d : Dart) (rho ef my h_tip : R),
    vy (ddir d) > 0 ->
    my <= h_tip ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_east d ef) ->
    (forall y, my <= y <= h_tip ->
       ~ ring_image r (corridor_east d ef y)) ->
    connected_in_complement_cont r
      (point_at (dtip d)
         (corner_sample_in (point_diff (dbase d) (dtip d)) rho
            (corner_delta_for_ef_east d ef)))
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r d rho ef my h_tip Hasc Hle Hhtip Hclear.
  set (delta_c := corner_delta_for_ef_east d ef).
  assert (Htip_eq :
    point_at (dtip d)
      (corner_sample_in (point_diff (dbase d) (dtip d)) rho delta_c)
      = corridor_east d ef h_tip).
  { rewrite (handoff_tip_bridge_east d rho delta_c Hasc).
    change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
              / vy (ddir d)) with (bridge_delta_east d delta_c).
    change (py (dtip d) + (- rho * vy (ddir d) - delta_c * vx (ddir d)))
      with (bridge_height_tip d rho delta_c).
    assert (Hbd : bridge_delta_east d delta_c = ef)
      by (unfold delta_c; exact (bridge_delta_east_for_ef d ef Hasc)).
    assert (Hth : bridge_height_tip d rho delta_c = h_tip)
      by (unfold delta_c; symmetry; exact Hhtip).
    rewrite Hbd, Hth. reflexivity. }
  assert (Hride : connected_in_complement_cont r (corridor_east d ef my)
                    (corridor_east d ef h_tip)).
  { assert (Hnh : py (dbase d) <> py (dtip d)).
    { intro Heq. pose proof (dart_ascend_base_below_tip d Hasc) as Hasc'.
      rewrite Heq in Hasc'. lra. }
    apply connected_in_complement_cont_sym.
    exact (corridor_connected_east r d my h_tip ef Hnh Hle Hclear). }
  apply connected_in_complement_cont_sym in Hride.
  rewrite <- Htip_eq in Hride.
  rewrite straddle_east_eq_corridor_east in Hride.
  exact Hride.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions along_dart_base_to_straddle_west.
Print Assumptions along_dart_base_to_straddle_east.
