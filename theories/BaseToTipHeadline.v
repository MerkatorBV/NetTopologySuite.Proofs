(* ==========================================================================
   BaseToTipHeadline.v

   [H-bridge attack, C-3e step 4] The ALONG-DART HEADLINE: base corner
   sample -> corridor ride -> straddle target at height `my`, composed by
   transitivity.  The straddle pair `(edge_x_at d my ± ef, my)` is reached
   as a west/east corridor point once `ef` sits below the corridor
   half-threshold (`corridor_absorbs_ef` / `corridor_ef_inherits_clearance`).

   The algebraic bypass (`HandoffConnector.handoff_base_bridge_*`) reuses
   the corner connector's own sample as the corridor endpoint at the bridge
   height; the handoff chord (`handoff_base_to_corridor_west_convex`) is
   the general alternative when heights differ.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay Vec Azimuth Dart DartAngularOrder
                               PointInRingTangents JordanCurveSeam
                               JCT JCTCorridor JCTMinOpenStep JCTTautClearance
                               MirrorCorridor WalkCorridor FaceTwinAware
                               HBridgeCoreSlice CornerSamples CornerConnector
                               CornerCorridorBridge HandoffConnector
                               C3eEfCorridorAssumption.

Import ListNotations.
Local Open Scope R_scope.

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
(* §3  Packaged with walk-dart clearance + ef half-threshold.                  *)
(* -------------------------------------------------------------------------- *)

Theorem along_dart_base_to_straddle_west_clear :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base ylo yhi : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= yhi ->
    0 < ef ->
    (exists delta0, 0 < delta0 /\
       ef < corridor_safe_half delta0 /\
       forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor d delta y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_west d ef)))
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros D r d rho ef my h_base ylo yhi Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hdesc Hhbase [[Hhlo Hhhi] Hmhi] Hef
         [delta0 [Hd0 [Hhalf Hclear]]].
  apply (along_dart_base_to_straddle_west r d rho ef my h_base Hdesc Hhbase).
  - exact Hhhi.
  - intros y Hy.
    apply (corridor_ef_inherits_clearance d r delta0 ef y ylo yhi Hd0 Hef Hhalf Hle).
    + exact Hclear.
    + lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Representative exercise: bridge delta discharged for any dart.        *)
(* -------------------------------------------------------------------------- *)

(* Any descending dart with corridor clearance reaches the west straddle
   point once rho picks the bridge height; `bridge_delta_west_for_ef` closes
   the offset identity that `straddle_side_core` supplies as positive `ef`. *)
Example along_dart_west_reaches_straddle :
  forall (r : Ring) (d : Dart) (rho ef my h_base : R),
    vy (ddir d) < 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
    h_base <= my ->
    (forall y, h_base <= y <= my -> ~ ring_image r (corridor d ef y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_west d ef)))
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros r d rho ef my h_base Hdesc Hhbase Hle Hclear.
  exact (along_dart_base_to_straddle_west r d rho ef my h_base
           Hdesc Hhbase Hle Hclear).
Qed.

Lemma along_dart_west_bridge_delta :
  forall (d : Dart) (ef : R), vy (ddir d) < 0 ->
    bridge_delta_west d (corner_delta_for_ef_west d ef) = ef.
Proof. exact bridge_delta_west_for_ef. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions along_dart_base_to_straddle_west.
Print Assumptions along_dart_base_to_straddle_west_clear.
Print Assumptions along_dart_base_to_straddle_east.