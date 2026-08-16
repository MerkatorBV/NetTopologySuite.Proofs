(* ==========================================================================
   BaseToTipCorridorSafe.v

   [C-3e step C, layer 3] Packaged with walk-dart clearance + ef
   half-threshold (the _clear headline forms), the corner-sample
   endpoints, the straddle-pair chord algebra, and the
   corridor_safe_for_ef* discharge family (west / east / foreign).

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
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth Direction
                               Dart DartAngularOrder PointInRingTangents
                               JordanCurveSeam JCT JCTHugStep JCTMinOpenStep
                               JCTTautClearance JCTNesting GeneralTautBridge
                               RingClearance SectorPath CornerSamples CornerConnector
                               JCTCorridor StraddleSides MirrorCorridor DartSideKit
                               HandoffWedge WalkCorridor FaceTwinAware HBridgeCoreSlice
                               RingExtract RectangleJCT.
From NTS.Proofs Require Export CornerCorridorBridge C3eEfCorridorAssumption
                               HandoffConnector.

Import ListNotations.
Local Open Scope R_scope.
(* §C-3e-C  Along-dart headline -> straddle (edge_x_at d my ± ef, my).        *)
From NTS.Proofs Require Import BaseToTipDelta.
From NTS.Proofs Require Import BaseToTipAlongDart.

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

Theorem along_dart_base_to_straddle_east_clear :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base ylo yhi : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    ylo <= h_base <= my /\ my <= yhi ->
    0 < ef ->
    (exists delta0, 0 < delta0 /\
       ef < corridor_safe_half delta0 /\
       forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor_east d delta y)) ->
    connected_in_complement_cont r
      (point_at (dbase d)
         (corner_sample_out (ddir d) rho (corner_delta_for_ef_east d ef)))
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros D r d rho ef my h_base ylo yhi Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hasc Hhbase [[Hhlo Hhhi] Hmhi] Hef
         [delta0 [Hd0 [Hhalf Hclear]]].
  apply (along_dart_base_to_straddle_east r d rho ef my h_base Hasc Hhbase).
  - exact Hhhi.
  - intros y Hy.
    apply (corridor_ef_inherits_clearance_east d r delta0 ef y ylo yhi Hd0 Hef Hhalf Hle).
    + exact Hclear.
    + lra.
Qed.

(* C-3e-4 corner endpoints for the along-dart headline (base = left, tip = right). *)
Definition corner_sample_left (d : Dart) (rho ef : R) : Point :=
  point_at (dbase d)
    (corner_sample_out (ddir d) rho (corner_delta_for_ef_west d ef)).

Definition corner_sample_right (d : Dart) (rho ef : R) : Point :=
  point_at (dtip d)
    (corner_sample_in (point_diff (dbase d) (dtip d)) rho
       (corner_delta_for_ef_west d ef)).

(* Exact straddle pair named as in `face_transport_premise` (HBridgeCoreSlice.v). *)
Lemma face_transport_straddle_pair_eq :
  forall (d : Dart) (my ef : R),
    let p1 := mkPoint (edge_x_at d my - ef) my in
    let p2 := mkPoint (edge_x_at d my + ef) my in
    p1 = corridor d ef my /\ p2 = corridor_east d ef my.
Proof.
  intros d my ef. split; [ exact (straddle_west_eq_corridor d my ef)
                           | exact (straddle_east_eq_corridor_east d my ef) ].
Qed.

(* FOREIGN-DART chord only: when `d` is off `ring_edges r`, the horizontal
   segment between p_west and p_east at `my` need not meet the ring (the
   carrier midpoint `(edge_x_at d my, my)` is avoided because `d` is not a
   ring edge).  Do NOT use on ring darts in `face_transport_premise`'s
   `ring_of_chain (d :: c)` — there the carrier lies on the cycle. *)
Lemma foreign_dart_straddle_pair_chord_at_my :
  forall (r : Ring) (d : Dart) (ef my : R),
    ~ In d (ring_edges r) ->
    (forall t, 0 <= t <= 1 ->
       ring_complement r
         (mkPoint (edge_x_at d my - ef + t * (2 * ef)) my)) ->
    connected_in_complement_cont r
      (mkPoint (edge_x_at d my - ef) my)
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros r d ef my Hdedge Hchord.
  set (v := mkPoint (edge_x_at d my) my).
  set (A := mkVec (- ef) 0).
  set (B := mkVec ef 0).
  assert (Hwest : point_at v A = mkPoint (edge_x_at d my - ef) my).
  { unfold point_at, A, v. cbn. f_equal; ring. }
  assert (Heast : point_at v B = mkPoint (edge_x_at d my + ef) my).
  { unfold point_at, B, v. cbn. f_equal; ring. }
  assert (Hhop : forall t, 0 <= t <= 1 ->
    ring_complement r (point_at v (vaffine t A B))).
  { intros t Ht.
    assert (Hblend : point_at v (vaffine t A B) =
      mkPoint (edge_x_at d my - ef + t * (2 * ef)) my).
    { unfold point_at, vaffine, vadd, vscale, A, B, v. cbn. f_equal; ring. }
    rewrite Hblend. exact (Hchord t Ht). }
  pose proof (hop_connected r v A B Hhop) as Hconn.
  rewrite Hwest, Heast in Hconn.
  exact Hconn.
Qed.

Definition corner_sample_left_east (d : Dart) (rho ef : R) : Point :=
  point_at (dbase d)
    (corner_sample_out (ddir d) rho (corner_delta_for_ef_east d ef)).

Theorem along_dart_tip_to_straddle_west_clear :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_tip ylo yhi : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) < 0 ->
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= my ->
    my <= h_tip <= yhi ->
    0 < ef ->
    (exists delta0, 0 < delta0 /\
       ef < corridor_safe_half delta0 /\
       forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor d delta y)) ->
    connected_in_complement_cont r (corner_sample_right d rho ef)
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros D r d rho ef my h_tip ylo yhi Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hdesc Hhtip Hylomy [Hmhi Hthhi] Hef
         [delta0 [Hd0 [Hhalf Hclear]]].
  apply (along_dart_tip_to_straddle_west r d rho ef my h_tip Hdesc).
  - exact Hmhi.
  - exact Hhtip.
  - intros y [Hylo Hyhi].
    apply (corridor_ef_inherits_clearance d r delta0 ef y ylo yhi Hd0 Hef Hhalf Hle).
    + exact Hclear.
    + split; lra.
Qed.

(* C-3e-4 west headline (descending): both corner samples reach the WEST
   `face_transport_premise` target `(edge_x_at d my - ef, my)` via the west
   corridor — no carrier-crossing chord. *)
Theorem corridor_safe_for_ef_west :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base h_tip ylo yhi delta0 : R),
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
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor d delta y)) ->
    let p_west := mkPoint (edge_x_at d my - ef) my in
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
    connected_in_complement_cont r (corner_sample_right d rho ef) p_west.
Proof.
  intros D r d rho ef my h_base h_tip ylo yhi delta0 Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hdesc Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear p_west.
  assert (Hhalf : ef < corridor_safe_half delta0)
    by (apply (ef_lt_threshold_third_implies_half delta0 ef Hd0 Hef); exact Hthird).
  assert (Hmyle : my <= yhi) by (apply (Rle_trans _ _ _ Hmhi Hthhi)).
  assert (Hylomy : ylo <= my).
  { destruct Hhlo as [Hblo Hbmy]. apply (Rle_trans _ _ _ Hblo Hbmy). }
  split.
  - apply (along_dart_base_to_straddle_west_clear D r d rho ef my h_base ylo yhi);
      [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
      | exact Hspan | exact Hle | exact Hdesc | exact Hhbase
      | exact (conj Hhlo Hmyle) | exact Hef
      | exists delta0; split; [exact Hd0 | split; [exact Hhalf | exact Hclear]] ].
  - apply (along_dart_tip_to_straddle_west_clear D r d rho ef my h_tip ylo yhi);
      [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
      | exact Hspan | exact Hle | exact Hdesc | exact Hhtip | exact Hylomy
      | repeat split; assumption | exact Hef
      | exists delta0; split; [exact Hd0 | split; [exact Hhalf | exact Hclear]] ].
Qed.

(* C-3e-4 east headline (ascending): base corner reaches the EAST
   `face_transport_premise` target `(edge_x_at d my + ef, my)`. *)
Theorem corridor_safe_for_ef_east :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base ylo yhi delta0 : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    ylo <= h_base <= my /\ my <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor_east d delta y)) ->
    let p_east := mkPoint (edge_x_at d my + ef) my in
    connected_in_complement_cont r (corner_sample_left_east d rho ef) p_east.
Proof.
  intros D r d rho ef my h_base ylo yhi delta0 Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hasc Hhbase [Hhlo Hmhi] Hd0 Hef Hthird Hclear_east p_east.
  assert (Hhalf : ef < corridor_safe_half delta0)
    by (apply (ef_lt_threshold_third_implies_half delta0 ef Hd0 Hef); exact Hthird).
  unfold corner_sample_left_east.
  apply (along_dart_base_to_straddle_east_clear D r d rho ef my h_base ylo yhi);
    [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
    | exact Hspan | exact Hle | exact Hasc | exact Hhbase
    | exact (conj Hhlo Hmhi) | exact Hef
    | exists delta0; split; [exact Hd0 | split; [exact Hhalf | exact Hclear_east]] ].
Qed.

(* FOREIGN-DART packaging: when `d` is not on the ring, both exact straddle
   targets are reachable (east via the foreign chord after tip->west). *)
Theorem foreign_dart_corridor_safe_for_ef :
  forall (r : Ring) (d : Dart) (rho ef my : R),
    let p_west := mkPoint (edge_x_at d my - ef) my in
    let p_east := mkPoint (edge_x_at d my + ef) my in
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west ->
    connected_in_complement_cont r (corner_sample_right d rho ef) p_west ->
    ~ In d (ring_edges r) ->
    (forall t, 0 <= t <= 1 ->
       ring_complement r (mkPoint (edge_x_at d my - ef + t * (2 * ef)) my)) ->
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
    connected_in_complement_cont r (corner_sample_right d rho ef) p_west /\
    connected_in_complement_cont r (corner_sample_right d rho ef) p_east.
Proof.
  intros r d rho ef my p_west p_east Hleft Hright Hdedge Hchord.
  split; [ exact Hleft | split; [ exact Hright | ] ].
  apply (connected_in_complement_cont_trans r
           (corner_sample_right d rho ef) p_west p_east).
  - exact Hright.
  - exact (foreign_dart_straddle_pair_chord_at_my r d ef my Hdedge Hchord).
Qed.

(* Foreign-dart branch of the C-3e-4 headline: both ±ef targets connected. *)
Theorem corridor_safe_for_ef_foreign :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base h_tip ylo yhi delta0 : R),
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
    h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor d delta y)) ->
    ~ In d (ring_edges r) ->
    (forall t, 0 <= t <= 1 ->
       ring_complement r (mkPoint (edge_x_at d my - ef + t * (2 * ef)) my)) ->
    let p_west := mkPoint (edge_x_at d my - ef) my in
    let p_east := mkPoint (edge_x_at d my + ef) my in
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
    connected_in_complement_cont r (corner_sample_right d rho ef) p_west /\
    connected_in_complement_cont r (corner_sample_right d rho ef) p_east.
Proof.
  intros D r d rho ef my h_base h_tip ylo yhi delta0 Htaut Hcross Hforeign Hx HringD
         Hspan Hle Hdesc Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear Hdedge Hchord
         p_west p_east.
  destruct (corridor_safe_for_ef_west D r d rho ef my h_base h_tip ylo yhi delta0
              Htaut Hcross Hforeign Hx HringD Hspan Hle Hdesc Hhbase Hhtip
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear) as [Hleft Hright].
  apply (foreign_dart_corridor_safe_for_ef r d rho ef my Hleft Hright Hdedge Hchord).
Qed.

(* C-3e-4 headline: names the exact `face_transport_premise` pair and wires
   west (descending) / east (ascending) corridor rides.
   The first conj gives UNCONDITIONAL exact targets
   `(edge_x_at d my - ef, my)` / `(edge_x_at d my + ef, my)` via
   `face_transport_straddle_pair_eq`.  Connection facts are case-split
   (ring membership × vy sign); ring-dart east at `my` on descending darts
   is deferred to C-3f orbit (carrier blocks same-height chord). *)
Theorem corridor_safe_for_ef :
  forall (D : list Dart) (r : Ring) (d : Dart) (rho ef my h_base h_tip ylo yhi delta0 : R),
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    let p_west := mkPoint (edge_x_at d my - ef) my in
    let p_east := mkPoint (edge_x_at d my + ef) my in
    (p_west = corridor d ef my /\ p_east = corridor_east d ef my) /\
    ((In d (ring_edges r) /\ vy (ddir d) < 0 ->
      h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
      h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
      (forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor d delta y)) ->
      connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
      connected_in_complement_cont r (corner_sample_right d rho ef) p_west)) /\
    ((In d (ring_edges r) /\ vy (ddir d) > 0 ->
      h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
      (forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor_east d delta y)) ->
      connected_in_complement_cont r (corner_sample_left_east d rho ef) p_east)) /\
    ((~ In d (ring_edges r) /\ vy (ddir d) < 0 ->
      h_base = bridge_height_base d rho (corner_delta_for_ef_west d ef) ->
      h_tip = bridge_height_tip d rho (corner_delta_for_ef_west d ef) ->
      (forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor d delta y)) ->
      (forall t, 0 <= t <= 1 ->
         ring_complement r (mkPoint (edge_x_at d my - ef + t * (2 * ef)) my)) ->
      connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
      connected_in_complement_cont r (corner_sample_right d rho ef) p_west /\
      connected_in_complement_cont r (corner_sample_right d rho ef) p_east)).
Proof.
  intros D r d rho ef my h_base h_tip ylo yhi delta0 Htaut Hcross Hforeign Hx HringD
         Hspan Hle [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird p_west p_east.
  destruct (face_transport_straddle_pair_eq d my ef) as [Heq_west Heq_east].
  assert (Hmyle : my <= yhi) by (apply (Rle_trans _ _ _ Hmhi Hthhi)).
  split.
  { split; [ exact Heq_west | exact Heq_east ]. }
  split.
  { intros [Hinring Hdesc] Hhbase' Hhtip' Hclear.
    apply (corridor_safe_for_ef_west D r d rho ef my h_base h_tip ylo yhi delta0);
      [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
      | exact Hspan | exact Hle | exact Hdesc | exact Hhbase' | exact Hhtip'
      | exact (conj Hhlo (conj Hmhi Hthhi)) | exact Hd0 | exact Hef | exact Hthird
      | exact Hclear ]. }
  split.
  { intros [Hinring Hasc] Hhbase' Hclear_east.
    apply (corridor_safe_for_ef_east D r d rho ef my h_base ylo yhi delta0);
      [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
      | exact Hspan | exact Hle | exact Hasc | exact Hhbase'
      | exact (conj Hhlo Hmyle) | exact Hd0 | exact Hef | exact Hthird
      | exact Hclear_east ]. }
  { intros [Hdedge Hdesc] Hhbase' Hhtip' Hclear Hchord.
    apply (corridor_safe_for_ef_foreign D r d rho ef my h_base h_tip ylo yhi delta0);
      [ exact Htaut | exact Hcross | exact Hforeign | exact Hx | exact HringD
      | exact Hspan | exact Hle | exact Hdesc | exact Hhbase' | exact Hhtip'
      | exact (conj Hhlo (conj Hmhi Hthhi)) | exact Hd0 | exact Hef | exact Hthird
      | exact Hclear | exact Hdedge | exact Hchord ]. }
Qed.


(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions along_dart_base_to_straddle_west_clear.
Print Assumptions along_dart_base_to_straddle_east_clear.
Print Assumptions along_dart_tip_to_straddle_west_clear.
Print Assumptions corridor_safe_for_ef.
Print Assumptions corridor_safe_for_ef_west.
Print Assumptions corridor_safe_for_ef_east.
Print Assumptions foreign_dart_corridor_safe_for_ef.
Print Assumptions face_transport_straddle_pair_eq.
