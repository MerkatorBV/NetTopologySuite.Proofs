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
                               JCTNesting GeneralTautBridge
                               MirrorCorridor WalkCorridor FaceTwinAware
                               HBridgeCoreSlice CornerSamples CornerConnector
                               CornerCorridorBridge HandoffConnector
                               C3eEfCorridorAssumption RectangleJCT.

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
(* §4  Representative exercise on a concrete descending dart.                *)
(* -------------------------------------------------------------------------- *)

(* Base (0,2) -> tip (1,0): vy (ddir d) = -2 < 0. *)
Definition descending_sample_dart : Dart :=
  (mkPoint 0 2, mkPoint 1 0).

Lemma descending_sample_dart_vy :
  vy (ddir descending_sample_dart) < 0.
Proof.
  unfold descending_sample_dart, ddir, point_diff, dtip, dbase, vy, fst, snd.
  cbn. lra.
Qed.

Lemma bridge_delta_west_sample_closed :
  bridge_delta_west descending_sample_dart
    (corner_delta_for_ef_west descending_sample_dart (1 / 10))
  = 1 / 10.
Proof.
  apply bridge_delta_west_for_ef. exact descending_sample_dart_vy.
Qed.

Lemma edge_x_at_sample_closed :
  edge_x_at descending_sample_dart 1 = 1 / 2.
Proof.
  unfold descending_sample_dart, edge_x_at. cbn.
  field.
Qed.

Lemma straddle_west_target_sample_closed :
  corridor descending_sample_dart (1 / 10) 1 = mkPoint (2 / 5) 1.
Proof.
  rewrite straddle_west_eq_corridor, edge_x_at_sample_closed.
  f_equal. field_simplify. lra.
Qed.

Lemma handoff_base_sample_endpoint_closed :
  point_at (dbase descending_sample_dart)
    (corner_sample_out (ddir descending_sample_dart) (1 / 4)
       (corner_delta_for_ef_west descending_sample_dart (1 / 10)))
  = corridor descending_sample_dart (1 / 10)
      (bridge_height_base descending_sample_dart (1 / 4)
         (corner_delta_for_ef_west descending_sample_dart (1 / 10))).
Proof.
  set (d := descending_sample_dart).
  set (ef := 1 / 10).
  set (rho := 1 / 4).
  set (delta_c := corner_delta_for_ef_west d ef).
  set (h_base := bridge_height_base d rho delta_c).
  rewrite (handoff_base_bridge_west d rho delta_c descending_sample_dart_vy).
  change (delta_c * (vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
            / (- vy (ddir d))) with (bridge_delta_west d delta_c).
  change (py (dbase d) + (rho * vy (ddir d) - delta_c * vx (ddir d)))
    with (bridge_height_base d rho delta_c).
  assert (Hbd : bridge_delta_west d delta_c = ef)
    by (unfold d, ef, delta_c; exact bridge_delta_west_sample_closed).
  assert (Hbh : bridge_height_base d rho delta_c = h_base) by reflexivity.
  rewrite Hbd, Hbh. reflexivity.
Qed.

Definition sample_ef : R := 1 / 10.
Definition sample_rho : R := 1 / 2.
Definition sample_my : R := 1.
Definition sample_h_base : R := 24 / 25.
(* Ring placed far east so the sample corridor (x ~ 0.4, y in [24/25,1])
   cannot meet any edge — clearance is explicit, not a load-bearing hypothesis. *)
Definition sample_ring : Ring := rect_ring 10 10 12 12.
Definition sample_ylo : R := 1 / 100.
Definition sample_yhi : R := 99 / 50.
Definition sample_D : list Dart :=
  descending_sample_dart :: ring_edges sample_ring.

Lemma rect_ring_no_foreign_vertex : forall x0 y0 x1 y1,
  x0 < x1 -> y0 < y1 ->
  ring_no_vertex_on_foreign_edge_interior (rect_ring x0 y0 x1 y1).
Proof.
  intros x0 y0 x1 y1 Hx01 Hy01 e f He Hf Hef.
  rewrite ring_edges_rect in He, Hf. cbn [In] in He, Hf.
  destruct He as [He | [He | [He | [He | []]]]];
  destruct Hf as [Hf | [Hf | [Hf | [Hf | []]]]];
    subst e f; cbn [fst snd px py];
    split; intros [t [[Ht0 Ht1] [Hx Hy]]];
    try (apply Hef; reflexivity);
    nra.
Qed.

Lemma sample_ring_taut : ring_taut sample_ring.
Proof.
  unfold sample_ring.
  apply ring_taut_of_simple_and_no_foreign_vertex.
  - apply rect_ring_simple; lra.
  - apply rect_ring_no_foreign_vertex; lra.
Qed.

Lemma sample_dart_px_le (t : R) :
  0 <= t <= 1 ->
  (1 - t) * px (dbase descending_sample_dart) + t * px (dtip descending_sample_dart) <= 1.
Proof.
  intros [Ht0 Ht1].
  unfold descending_sample_dart, dbase, dtip, px, fst, snd. nra.
Qed.

Lemma sample_dart_py_le (t : R) :
  0 <= t <= 1 ->
  (1 - t) * py (dbase descending_sample_dart) + t * py (dtip descending_sample_dart) <= 2.
Proof.
  intros [Ht0 Ht1].
  unfold descending_sample_dart, dbase, dtip, py, fst, snd. nra.
Qed.

Lemma sample_ring_edge_py_ge :
  forall (f : Edge) (s : R),
    In f (ring_edges sample_ring) ->
    0 <= s <= 1 ->
    10 <= (1 - s) * py (fst f) + s * py (snd f).
Proof.
  intros f s Hin Hs.
  unfold sample_ring in Hin.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [Hf | [Hf | [Hf | [Hf | []]]]]; subst f; cbn [fst snd py];
    destruct Hs as [Hs0 Hs1]; nra.
Qed.

Lemma sample_ring_edge_px_ge :
  forall (f : Edge) (t : R),
    In f (ring_edges sample_ring) ->
    0 <= t <= 1 ->
    10 <= (1 - t) * px (fst f) + t * px (snd f).
Proof.
  intros f t Hin Ht.
  unfold sample_ring in Hin.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [Hf | [Hf | [Hf | [Hf | []]]]]; subst f; cbn [fst snd px];
    destruct Ht as [Ht1 Ht2]; nra.
Qed.

Lemma sip_exchange_segments :
  forall (P0 P1 Q0 Q1 : Point),
    segments_intersect_properly P0 P1 Q0 Q1 ->
    segments_intersect_properly Q0 Q1 P0 P1.
Proof.
  intros P0 P1 Q0 Q1 (t & s & Ht & Hs & Hx & Hy).
  exists s, t. repeat split; try lra; assumption.
Qed.

Lemma sample_dart_no_proper_cross_ring_edge :
  forall (f : Edge),
    In f (ring_edges sample_ring) ->
    ~ segments_intersect_properly (dbase descending_sample_dart)
      (dtip descending_sample_dart) (fst f) (snd f).
Proof.
  intros f Hin (t & s & Ht & Hs & Hx & Hy).
  unfold sample_ring in Hin.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [Hf | [Hf | [Hf | [Hf | []]]]]; subst f;
    unfold descending_sample_dart, dbase, dtip, px, py, fst, snd in Hx, Hy;
    destruct Ht as [Ht0 Ht1]; destruct Hs as [Hs0 Hs1]; nra.
Qed.

Lemma sample_pairwise_twin_aware :
  pairwise_no_proper_cross_twin_aware sample_D.
Proof.
  unfold pairwise_no_proper_cross_twin_aware, sample_D.
  intros d1 d2 H1 H2 Hne Hnt Hcross.
  simpl in H1. destruct H1 as [Hd1 | H1]; [subst d1 | ].
  - simpl in H2. destruct H2 as [Hd2 | H2]; [subst d2; exfalso; apply Hne; reflexivity | ].
    apply (sample_dart_no_proper_cross_ring_edge d2 H2). exact Hcross.
  - simpl in H2. destruct H2 as [Hd2 | H2]; [subst d2 | ].
    + apply (sample_dart_no_proper_cross_ring_edge d1 H1).
      apply sip_exchange_segments. exact Hcross.
    + pose proof (rect_ring_simple 10 10 12 12 (ltac:(lra)) (ltac:(lra))) as Hsimp.
      unfold ring_simple in Hsimp.
      apply (Hsimp d1 d2 H1 H2 Hne). exact Hcross.
Qed.

Lemma sample_ring_vertices_not_on_dart :
  forall (f : Edge),
    In f (ring_edges sample_ring) ->
    (~ exists t : R, 0 < t < 1 /\
         px (fst f) = (1 - t) * px (dbase descending_sample_dart) + t * px (dtip descending_sample_dart) /\
         py (fst f) = (1 - t) * py (dbase descending_sample_dart) + t * py (dtip descending_sample_dart)) /\
    (~ exists t : R, 0 < t < 1 /\
         px (snd f) = (1 - t) * px (dbase descending_sample_dart) + t * px (dtip descending_sample_dart) /\
         py (snd f) = (1 - t) * py (dbase descending_sample_dart) + t * py (dtip descending_sample_dart)).
Proof.
  intros f Hin.
  unfold sample_ring in Hin.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [Hf | [Hf | [Hf | [Hf | []]]]]; subst f;
    split; intros [t [[Ht0 Ht1] [Hx Hy]]];
    unfold descending_sample_dart, dbase, dtip, px, py, fst, snd in Hx, Hy; nra.
Qed.

Lemma sample_dart_vertices_not_on_ring :
  forall (e : Edge),
    In e (ring_edges sample_ring) ->
    (~ exists t : R, 0 < t < 1 /\
         px (dbase descending_sample_dart) = (1 - t) * px (fst e) + t * px (snd e) /\
         py (dbase descending_sample_dart) = (1 - t) * py (fst e) + t * py (snd e)) /\
    (~ exists t : R, 0 < t < 1 /\
         px (dtip descending_sample_dart) = (1 - t) * px (fst e) + t * px (snd e) /\
         py (dtip descending_sample_dart) = (1 - t) * py (fst e) + t * py (snd e)).
Proof.
  intros e Hin.
  unfold sample_ring in Hin.
  rewrite ring_edges_rect in Hin. cbn [In] in Hin.
  destruct Hin as [He | [He | [He | [He | []]]]]; subst e;
    split; intros [t [[Ht0 Ht1] [Hx Hy]]];
    unfold descending_sample_dart, dbase, dtip, px, py, fst, snd in Hx, Hy; nra.
Qed.

Lemma sample_no_foreign_twin_aware :
  no_foreign_vertex_twin_aware sample_D.
Proof.
  unfold no_foreign_vertex_twin_aware, sample_D.
  intros e f He Hf Hne Hnt.
  simpl in He, Hf.
  destruct He as [Heq | He]; destruct Hf as [Heqf | Hf].
  - subst e f. exfalso. apply Hne. reflexivity.
  - subst e. apply sample_ring_vertices_not_on_dart. exact Hf.
  - subst f. apply sample_dart_vertices_not_on_ring. exact He.
  - destruct (rect_ring_no_foreign_vertex 10 10 12 12 (ltac:(lra)) (ltac:(lra))
                e f He Hf Hne) as [H1 H2].
    exact (conj H1 H2).
Qed.

Lemma sample_ring_edges_in_D :
  forall f, In f (ring_edges sample_ring) -> In f sample_D.
Proof.
  intros f Hin. simpl. right. exact Hin.
Qed.

Lemma sample_span :
  (py (snd descending_sample_dart) < sample_ylo /\ sample_yhi < py (fst descending_sample_dart)).
Proof.
  unfold sample_ylo, sample_yhi, descending_sample_dart, fst, snd, py. lra.
Qed.

Lemma edge_x_at_descending_sample (y : R) :
  edge_x_at descending_sample_dart y = (2 - y) / 2.
Proof.
  unfold descending_sample_dart, edge_x_at. cbn. field.
Qed.

Lemma corridor_px_sample_lt_delta :
  forall (delta y_sample : R),
    0 < delta < 1 ->
    sample_ylo <= y_sample <= sample_yhi ->
    px (corridor descending_sample_dart delta y_sample) < 1.
Proof.
  intros delta y_sample [Hdp Hdt] [Hylo Hyhi].
  unfold corridor. cbn [px].
  rewrite edge_x_at_descending_sample.
  unfold sample_ylo, sample_yhi in Hylo, Hyhi.
  assert (Hmax : (2 - y_sample) / 2 <= 199 / 200) by nra.
  nra.
Qed.

Lemma sample_clearance_delta :
  forall (delta y_sample : R),
    0 < delta < 1 ->
    sample_ylo <= y_sample <= sample_yhi ->
    ~ ring_image sample_ring
         (corridor descending_sample_dart delta y_sample).
Proof.
  intros delta y_sample Hdelta Hy Himg.
  destruct Himg as [f [s [Hin [[Hs1 Hs2] [Hx Hpy]]]]].
  pose proof (corridor_px_sample_lt_delta delta y_sample Hdelta Hy) as Hclt.
  pose proof (sample_ring_edge_px_ge f s Hin (conj Hs1 Hs2)) as Hcge.
  unfold corridor in Hclt, Hx. cbn [px] in Hclt, Hx.
  rewrite edge_x_at_descending_sample in Hclt, Hx.
  lra.
Qed.

Lemma sample_delta0_pack :
  exists delta0, 0 < delta0 /\
    sample_ef < corridor_safe_half delta0 /\
    forall delta, 0 < delta < delta0 ->
      forall y, sample_ylo <= y <= sample_yhi ->
        ~ ring_image sample_ring (corridor descending_sample_dart delta y).
Proof.
  exists 1. split; [lra | ].
  split.
  - unfold sample_ef, corridor_safe_half. field_simplify. lra.
  - intros delta Hdelta y Hy.
    exact (sample_clearance_delta delta y Hdelta Hy).
Qed.

Lemma sample_h_base_eq :
  sample_h_base =
  bridge_height_base descending_sample_dart sample_rho
    (corner_delta_for_ef_west descending_sample_dart sample_ef).
Proof.
  unfold sample_h_base, sample_rho, sample_ef, bridge_height_base,
         descending_sample_dart, corner_delta_for_ef_west.
  cbn. field_simplify. lra.
Qed.

Lemma sample_h_base_le_my : sample_h_base <= sample_my.
Proof. unfold sample_h_base, sample_my. lra. Qed.

Lemma corridor_px_sample_lt :
  forall y_sample, sample_h_base <= y_sample <= sample_my ->
    px (corridor descending_sample_dart sample_ef y_sample) < 1.
Proof.
  intros y_sample [Hylo Hyhi].
  unfold corridor. cbn [px].
  rewrite edge_x_at_descending_sample.
  unfold sample_ef, sample_h_base, sample_my in *.
  assert (Hle : (2 - y_sample) / 2 - 1 / 10 <= 21 / 50) by nra.
  lra.
Qed.

Lemma sample_clearance :
  forall y_sample, sample_h_base <= y_sample <= sample_my ->
    ~ ring_image sample_ring
         (corridor descending_sample_dart sample_ef y_sample).
Proof.
  intros y_sample Hy Himg.
  destruct Himg as [f [s [Hin [[Hs1 Hs2] [Hx Hpy]]]]].
  pose proof (corridor_px_sample_lt y_sample Hy) as Hclt.
  pose proof (sample_ring_edge_px_ge f s Hin (conj Hs1 Hs2)) as Hcge.
  unfold corridor in Hclt, Hx. cbn [px] in Hclt, Hx.
  rewrite edge_x_at_descending_sample in Hclt, Hx.
  unfold sample_ef in Hclt, Hx.
  lra.
Qed.

(* Headline west transport on the concrete sample: corner -> straddle west. *)
Lemma descending_sample_west_transport :
  connected_in_complement_cont sample_ring
    (point_at (dbase descending_sample_dart)
       (corner_sample_out (ddir descending_sample_dart) sample_rho
          (corner_delta_for_ef_west descending_sample_dart sample_ef)))
    (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my).
Proof.
  apply (along_dart_base_to_straddle_west sample_ring descending_sample_dart
           sample_rho sample_ef sample_my sample_h_base).
  - exact descending_sample_dart_vy.
  - exact sample_h_base_eq.
  - exact sample_h_base_le_my.
  - exact sample_clearance.
Qed.

(* Packaged west transport via `along_dart_base_to_straddle_west_clear` and
   `corridor_ef_inherits_clearance` on the uniform delta0 window. *)
Lemma descending_sample_west_transport_clear :
  connected_in_complement_cont sample_ring
    (point_at (dbase descending_sample_dart)
       (corner_sample_out (ddir descending_sample_dart) sample_rho
          (corner_delta_for_ef_west descending_sample_dart sample_ef)))
    (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my).
Proof.
  apply (along_dart_base_to_straddle_west_clear sample_D sample_ring
           descending_sample_dart sample_rho sample_ef sample_my sample_h_base
           sample_ylo sample_yhi).
  - exact sample_ring_taut.
  - exact sample_pairwise_twin_aware.
  - exact sample_no_foreign_twin_aware.
  - simpl. left. reflexivity.
  - exact sample_ring_edges_in_D.
  - right. exact sample_span.
  - unfold sample_ylo, sample_yhi. lra.
  - exact descending_sample_dart_vy.
  - exact sample_h_base_eq.
  - repeat split; unfold sample_ylo, sample_h_base, sample_my, sample_yhi; lra.
  - unfold sample_ef. lra.
  - destruct sample_delta0_pack as [delta0 [Hd0 [Hhalf Hclear]]].
    exists delta0. eauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions along_dart_base_to_straddle_west.
Print Assumptions along_dart_base_to_straddle_west_clear.
Print Assumptions descending_sample_west_transport_clear.
Print Assumptions along_dart_base_to_straddle_east.