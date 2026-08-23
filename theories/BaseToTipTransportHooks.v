(* ==========================================================================
   BaseToTipTransportHooks.v

   [C-3e step C, layer 4] The ring-dart / foreign face_transport_premise
   apply hooks (HBridgeCoreSlice.v SS2 discharge), the c3e ring
   complement-via-connected lemmas, and the connected straddle
   headlines.

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

(* Downstream discharge for `face_transport_premise` (HBridgeCoreSlice.v §2):
   the premise's cycle ring has `d` ON the ring (`ring_edges r = d :: c`);
   descending ring dart — west exact target connected from both corners.
   East at `my` on ring darts deferred to C-3f orbit. *)
Lemma face_transport_premise_ring_dart_west_straddle_connected :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
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
    connected_in_complement_cont r (corner_sample_left d rho ef)
      (mkPoint (edge_x_at d my - ef) my) /\
    connected_in_complement_cont r (corner_sample_right d rho ef)
      (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hdesc
         Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear.
  destruct (corridor_safe_for_ef D r d rho ef my h_base h_tip ylo yhi delta0
              Htaut Hcross Hforeign Hx HringD Hspan Hle
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird) as [_ [Hwest [_ _]]].
  apply (Hwest (conj Hinring Hdesc) Hhbase Hhtip Hclear).
Qed.

(* Ascending ring dart — east exact target connected from base east corner. *)
Lemma face_transport_premise_ring_dart_east_straddle_connected :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor_east d delta y)) ->
    connected_in_complement_cont r (corner_sample_left_east d rho ef)
      (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hasc
         Hhbase [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear_east.
  destruct (corridor_safe_for_ef D r d rho ef my h_base h_tip ylo yhi delta0
              Htaut Hcross Hforeign Hx HringD Hspan Hle
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird) as [_ [_ [Heast _]]].
  apply (Heast (conj Hinring Hasc) Hhbase Hclear_east).
Qed.

(* Ring-dart packaging: exact ±ef target names + orientation-split connections.
   Descending: both corners -> west (`-ef`); ascending: base east corner -> `+ef`.
   Cross-orientation target on ring darts (descending `+ef`, ascending `-ef`)
   is deferred to C-3f orbit (carrier blocks same-height chord). *)
Lemma face_transport_premise_ring_dart_straddle_pair_connected :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
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
    let p_east := mkPoint (edge_x_at d my + ef) my in
    (p_west = corridor d ef my /\ p_east = corridor_east d ef my) /\
    (vy (ddir d) < 0 ->
      connected_in_complement_cont r (corner_sample_left d rho ef) p_west /\
      connected_in_complement_cont r (corner_sample_right d rho ef) p_west) /\
    (vy (ddir d) > 0 ->
      h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
      (forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor_east d delta y)) ->
      connected_in_complement_cont r (corner_sample_left_east d rho ef) p_east).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle
         Hhbase_west Hhtip_west [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear_west
         p_west p_east.
  destruct (face_transport_straddle_pair_eq d my ef) as [Heq_west Heq_east].
  split.
  { split; [ exact Heq_west | exact Heq_east ]. }
  split.
  - intros Hdesc.
    apply (face_transport_premise_ring_dart_west_straddle_connected E D r d c
             rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
             Hforeign Hx HdE HringD Hspan Hle Hdesc Hhbase_west Hhtip_west
             (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_west).
  - intros Hasc Hhbase_east Hclear_east.
    apply (face_transport_premise_ring_dart_east_straddle_connected E D r d c
             rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
             Hforeign Hx HdE HringD Hspan Hle Hasc Hhbase_east
             (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_east).
Qed.

(* Premise-layer apply hooks (HBridgeCoreSlice cannot import this file). *)
Lemma face_transport_premise_ring_dart_west_straddle_in_complement :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
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
    ring_complement r (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hdesc
         Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear.
  destruct (face_transport_premise_ring_dart_west_straddle_connected E D r d c
              rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
              Hforeign Hx HdE HringD Hspan Hle Hdesc Hhbase Hhtip
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear) as [Hconn _].
  apply (face_transport_straddle_target_in_complement r _ _ Hconn).
Qed.

Lemma face_transport_premise_ring_dart_east_straddle_in_complement :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor_east d delta y)) ->
    ring_complement r (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hasc
         Hhbase [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear_east.
  pose proof (face_transport_premise_ring_dart_east_straddle_connected E D r d c
               rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
               Hforeign Hx HdE HringD Hspan Hle Hasc Hhbase
               (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_east) as Hconn.
  apply (face_transport_straddle_target_in_complement r _ _ Hconn).
Qed.

Lemma face_transport_premise_ring_dart_straddle_pair_in_complement :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
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
    let p_east := mkPoint (edge_x_at d my + ef) my in
    (p_west = corridor d ef my /\ p_east = corridor_east d ef my) /\
    (vy (ddir d) < 0 -> ring_complement r p_west) /\
    (vy (ddir d) > 0 ->
      h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
      (forall delta, 0 < delta < delta0 ->
         forall y, ylo <= y <= yhi ->
           ~ ring_image r (corridor_east d delta y)) ->
      ring_complement r p_east).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle
         Hhbase_west Hhtip_west [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear_west
         p_west p_east.
  destruct (face_transport_premise_ring_dart_straddle_pair_connected E D r d c
              rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
              Hforeign Hx HdE HringD Hspan Hle Hhbase_west Hhtip_west
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_west) as [Heq [Hwest Heast]].
  split.
  - exact Heq.
  - split.
    + intros Hdesc.
      apply (face_transport_premise_ring_dart_west_straddle_in_complement E D r d c
               rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
               Hforeign Hx HdE HringD Hspan Hle Hdesc Hhbase_west Hhtip_west
               (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_west).
    + intros Hasc Hhbase_east Hclear_east.
      apply (face_transport_premise_ring_dart_east_straddle_in_complement E D r d c
               rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
               Hforeign Hx HdE HringD Hspan Hle Hasc Hhbase_east
               (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_east).
Qed.

(* Foreign-dart discharge: BOTH exact ±ef targets connected and in complement. *)
Lemma face_transport_premise_foreign_straddle_pair_in_complement :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    ~ In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
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
    (forall t, 0 <= t <= 1 ->
       ring_complement r (mkPoint (edge_x_at d my - ef + t * (2 * ef)) my)) ->
    let p_west := mkPoint (edge_x_at d my - ef) my in
    let p_east := mkPoint (edge_x_at d my + ef) my in
    (p_west = corridor d ef my /\ p_east = corridor_east d ef my) /\
    ring_complement r p_west /\ ring_complement r p_east.
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hdedge Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hdesc
         Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear Hchord p_west p_east.
  destruct (face_transport_straddle_pair_eq d my ef) as [Heq_west Heq_east].
  destruct (corridor_safe_for_ef_foreign D r d rho ef my h_base h_tip ylo yhi delta0
              Htaut Hcross Hforeign Hx HringD Hspan Hle Hdesc Hhbase Hhtip
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear Hdedge Hchord) as [Hleft [Hright Heast]].
  split.
  - split; assumption.
  - apply (face_transport_straddle_complements_of_connected r _ _ _ _ Hleft Heast).
Qed.

(* C-3e → HBridge apply chain: discharge connectivity projects to the
   exact `face_transport_premise` west straddle complement via
   `straddle_transport_clash_from_connected` (HBridgeCoreSlice.v §3). *)
Lemma c3e_ring_west_straddle_complement_via_connected :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
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
    ring_complement r (mkPoint (edge_x_at d my - ef) my).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hdesc
         Hhbase Hhtip [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear.
  destruct (face_transport_premise_ring_dart_west_straddle_connected E D r d c
              rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
              Hforeign Hx HdE HringD Hspan Hle Hdesc Hhbase Hhtip
              (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear) as [Hconn _].
  apply (face_transport_straddle_target_in_complement r _ _ Hconn).
Qed.

Lemma c3e_ring_east_straddle_complement_via_connected :
  forall (E : list Edge) (D : list Dart) (r : Ring) (d : Dart) (c : list Dart)
         (rho ef my h_base h_tip ylo yhi delta0 : R),
    face_transport_premise E ->
    r = ring_of_chain (d :: c) ->
    In d (ring_edges r) ->
    ring_taut r ->
    pairwise_no_proper_cross_twin_aware D ->
    no_foreign_vertex_twin_aware D ->
    In d D ->
    In d E ->
    (forall f, In f (ring_edges r) -> In f D) ->
    ((py (fst d) < ylo /\ yhi < py (snd d)) \/
     (py (snd d) < ylo /\ yhi < py (fst d))) ->
    ylo <= yhi ->
    vy (ddir d) > 0 ->
    h_base = bridge_height_base d rho (corner_delta_for_ef_east d ef) ->
    ylo <= h_base <= my /\ my <= h_tip <= yhi ->
    0 < delta0 ->
    0 < ef ->
    ef < corridor_safe_threshold delta0 / 3 ->
    (forall delta, 0 < delta < delta0 ->
       forall y, ylo <= y <= yhi ->
         ~ ring_image r (corridor_east d delta y)) ->
    ring_complement r (mkPoint (edge_x_at d my + ef) my).
Proof.
  intros E D r d c rho ef my h_base h_tip ylo yhi delta0
         Hprem Hr Hinring Htaut Hcross Hforeign Hx HdE HringD Hspan Hle Hasc
         Hhbase [Hhlo [Hmhi Hthhi]] Hd0 Hef Hthird Hclear_east.
  pose proof (face_transport_premise_ring_dart_east_straddle_connected E D r d c
               rho ef my h_base h_tip ylo yhi delta0 Hprem Hr Hinring Htaut Hcross
               Hforeign Hx HdE HringD Hspan Hle Hasc Hhbase
               (conj Hhlo (conj Hmhi Hthhi)) Hd0 Hef Hthird Hclear_east) as Hconn.
  apply (face_transport_straddle_target_in_complement r _ _ Hconn).
Qed.

(* Discharge hook for `face_transport_premise` (HBridgeCoreSlice.v §2): west
   straddle target connected from corner_sample_left on descending darts. *)
Lemma face_transport_west_straddle_headline_connected :
  forall (r : Ring) (d : Dart) (rho ef my : R),
    let p_west := mkPoint (edge_x_at d my - ef) my in
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west ->
    p_west = corridor d ef my /\
    connected_in_complement_cont r (corner_sample_left d rho ef) p_west.
Proof.
  intros r d rho ef my p_west Hconn.
  destruct (face_transport_straddle_pair_eq d my ef) as [Heq _].
  split; [ exact Heq | exact Hconn ].
Qed.

Lemma face_transport_east_straddle_headline_connected :
  forall (r : Ring) (d : Dart) (rho ef my : R),
    let p_east := mkPoint (edge_x_at d my + ef) my in
    connected_in_complement_cont r (corner_sample_left_east d rho ef) p_east ->
    p_east = corridor_east d ef my /\
    connected_in_complement_cont r (corner_sample_left_east d rho ef) p_east.
Proof.
  intros r d rho ef my p_east Hconn.
  destruct (face_transport_straddle_pair_eq d my ef) as [_ Heq].
  split; [ exact Heq | exact Hconn ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions face_transport_premise_ring_dart_west_straddle_connected.
Print Assumptions face_transport_premise_ring_dart_east_straddle_connected.
Print Assumptions face_transport_premise_ring_dart_straddle_pair_connected.
Print Assumptions face_transport_premise_ring_dart_west_straddle_in_complement.
Print Assumptions face_transport_premise_ring_dart_east_straddle_in_complement.
Print Assumptions face_transport_premise_ring_dart_straddle_pair_in_complement.
Print Assumptions face_transport_premise_foreign_straddle_pair_in_complement.
Print Assumptions face_transport_west_straddle_headline_connected.
Print Assumptions face_transport_east_straddle_headline_connected.
