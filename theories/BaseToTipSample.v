(* ==========================================================================
   BaseToTipSample.v

   [C-3e step C, layer 5] Representative exercise on a concrete
   descending dart: base (0,2) -> tip (1,0) inside the 10x12 rectangle
   ring, every premise discharged by closed-form computation.

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
From NTS.Proofs Require Import BaseToTipAlongDart.
From NTS.Proofs Require Import BaseToTipCorridorSafe.
From NTS.Proofs Require Import BaseToTipTransportHooks.

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

Definition sample_ef : R := 1 / 10.
Definition sample_rho : R := 1 / 2.
Definition sample_my : R := 24 / 25.
Definition sample_h_base : R := 24 / 25.
Definition sample_h_tip : R := 24 / 25.
Definition sample_ring : Ring := rect_ring 10 10 12 12.
Definition sample_ylo : R := 1 / 100.
Definition sample_yhi : R := 99 / 50.
Definition sample_D : list Dart :=
  descending_sample_dart :: ring_edges sample_ring.

Lemma edge_x_at_sample_closed :
  edge_x_at descending_sample_dart sample_my = 13 / 25.
Proof.
  unfold descending_sample_dart, edge_x_at, sample_my. cbn.
  field_simplify. lra.
Qed.

Lemma straddle_west_target_sample_closed :
  corridor descending_sample_dart sample_ef sample_my =
    mkPoint (13 / 25 - sample_ef) sample_my.
Proof.
  rewrite straddle_west_eq_corridor, edge_x_at_sample_closed.
  reflexivity.
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

Lemma sample_h_tip_eq :
  sample_h_tip =
  bridge_height_tip descending_sample_dart sample_rho
    (corner_delta_for_ef_west descending_sample_dart sample_ef).
Proof.
  unfold sample_h_tip, sample_rho, sample_ef, bridge_height_tip,
         descending_sample_dart, corner_delta_for_ef_west.
  cbn. field_simplify. lra.
Qed.

Lemma sample_my_le_h_tip : sample_my <= sample_h_tip.
Proof. unfold sample_my, sample_h_tip. lra. Qed.

Lemma sample_h_tip_le_yhi : sample_h_tip <= sample_yhi.
Proof. unfold sample_h_tip, sample_yhi. lra. Qed.

Lemma sample_ef_lt_threshold_third :
  sample_ef < corridor_safe_threshold 1 / 3.
Proof.
  unfold sample_ef, corridor_safe_threshold. field_simplify. lra.
Qed.

Lemma sample_straddle_chord_clear :
  forall t, 0 <= t <= 1 ->
    ring_complement sample_ring
      (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef
                  + t * (2 * sample_ef)) sample_my).
Proof.
  intros t [Ht0 Ht1] Himg.
  destruct Himg as [f [s [Hin [[Hs1 Hs2] [Hx Hpy]]]]].
  pose proof (sample_ring_edge_px_ge f s Hin (conj Hs1 Hs2)) as Hpx_ge.
  rewrite edge_x_at_descending_sample in Hx.
  unfold sample_my, sample_ef in Hx.
  assert (Hpx_lt : (2 - 24 / 25) / 2 - 1 / 10 + t * (2 / 10) < 10) by nra.
  cbn [px] in Hx, Hpx_ge.
  lra.
Qed.

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

Lemma sample_dart_not_on_ring :
  ~ In descending_sample_dart (ring_edges sample_ring).
Proof.
  intro Hin.
  unfold sample_ring, descending_sample_dart in Hin.
  rewrite ring_edges_rect in Hin.
  cbn [In] in Hin.
  destruct Hin as [He | [He | [He | [He | []]]]].
  all: injection He; intros; lra.
Qed.

(* Foreign-dart application: both exact `face_transport_premise` straddle
   targets at `sample_my` (dart off-ring, so east chord is valid). *)
Lemma descending_sample_corridor_safe_for_ef :
  let p_west :=
    mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my in
  let p_east :=
    mkPoint (edge_x_at descending_sample_dart sample_my + sample_ef) sample_my in
  connected_in_complement_cont sample_ring
    (corner_sample_left descending_sample_dart sample_rho sample_ef) p_west /\
  connected_in_complement_cont sample_ring
    (corner_sample_right descending_sample_dart sample_rho sample_ef) p_west /\
  connected_in_complement_cont sample_ring
    (corner_sample_right descending_sample_dart sample_rho sample_ef) p_east.
Proof.
  assert (Hwest :
    connected_in_complement_cont sample_ring
      (corner_sample_left descending_sample_dart sample_rho sample_ef)
      (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my) /\
    connected_in_complement_cont sample_ring
      (corner_sample_right descending_sample_dart sample_rho sample_ef)
      (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my)).
  { apply (corridor_safe_for_ef_west sample_D sample_ring descending_sample_dart
              sample_rho sample_ef sample_my sample_h_base sample_h_tip
              sample_ylo sample_yhi 1).
    - exact sample_ring_taut.
    - exact sample_pairwise_twin_aware.
    - exact sample_no_foreign_twin_aware.
    - simpl. left. reflexivity.
    - exact sample_ring_edges_in_D.
    - right. exact sample_span.
    - unfold sample_ylo, sample_yhi. lra.
    - exact descending_sample_dart_vy.
    - exact sample_h_base_eq.
    - exact sample_h_tip_eq.
    - repeat split; unfold sample_ylo, sample_h_base, sample_my, sample_h_tip, sample_yhi; lra.
    - lra.
    - unfold sample_ef. lra.
    - exact sample_ef_lt_threshold_third.
    - intros delta Hdelta y Hy.
      exact (sample_clearance_delta delta y Hdelta Hy). }
  destruct Hwest as [Hleft Hright].
  apply (foreign_dart_corridor_safe_for_ef sample_ring descending_sample_dart
           sample_rho sample_ef sample_my Hleft Hright).
  - exact sample_dart_not_on_ring.
  - exact sample_straddle_chord_clear.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions descending_sample_corridor_safe_for_ef.
Print Assumptions descending_sample_west_transport_clear.
