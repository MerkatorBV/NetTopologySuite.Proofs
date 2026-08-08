(* ==========================================================================
   NetTopologySuite.Proofs.EdgeFaceBridgeBarrier
   ----------------------------------------------------------------------------
   extract_rings_valid R5, H_bridge rung: carrier exclusivity, singleton-fan disconnect, not_adj / penult barriers (rungs 3b-ii, 3b-iii).

   Split (2026-08) from the former monolithic EdgeFaceBridge.v; original
   §-numbers are preserved so docs/extract-faces-bridge.md §19 and the
   verified-claims row remain accurate.  EdgeFaceBridge.v is the re-export
   umbrella (clients keep `Require Import EdgeFaceBridge`).

   Sections: §3b-ii (singleton-fan), §3b-iii (rotation-system barrier core, pre-premise).

   No `Admitted`, no `Axiom`, no `Parameter`.  The planar same-face
   => bridge seam is the named premise `H_bridge_premise` (Capstone),
   discharged downstream in HBridgeEuler.v.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude / Grok
   ========================================================================== *)
From Stdlib Require Import Reals Lra List Lia.
From Stdlib Require Import Program.Equality.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Dart DartNextSpec DartAngularOrder OrbitCycle
                               DartFace FaceChain RingSimple FaceRingSimple
                               FaceOrbitSep ExtractFaces EdgeConnectivity
                               NodedGeneralPosition VertexGeneralPosition
                               NoShortFaces FaceTwinAware
                               EdgeFaceBridgeIncidence EdgeFaceBridgeTwinPath.

Import ListNotations.
(* -------------------------------------------------------------------------- *)
(* §3b-ii  Carrier adjacency + singleton-fan disconnect (dumbbell base case).   *)
(* -------------------------------------------------------------------------- *)

Lemma dart_eq_of_endpoints :
  forall d1 d2 : Dart,
    dbase d1 = dbase d2 -> dtip d1 = dtip d2 -> d1 = d2.
Proof.
  intros [a b] [c d] Hba Hbd. f_equal; assumption.
Qed.

Lemma outgoing_eq_singleton_in :
  forall v D d x,
    outgoing v D = [d] ->
    In x (outgoing v D) ->
    x = d.
Proof.
  intros v D d x H Hx. rewrite H in Hx. apply in_inv in Hx.
  destruct Hx as [-> | Hnil]; [ reflexivity | destruct Hnil ].
Qed.

Lemma adj_dbase_dtip_witness_carrier :
  forall E d ec,
    In d (darts_of E) ->
    dbase d <> dtip d ->
    In ec E ->
    ((fst ec = dbase d /\ snd ec = dtip d) \/
     (fst ec = dtip d /\ snd ec = dbase d)) ->
    ec = d \/ ec = twin d.
Proof.
  intros E d ec Hd Hne Hin Hor.
  destruct ec as [a b], d as [db dt]. cbn [fst snd dbase dtip twin] in *.
  destruct Hor as [[Hba Hbt] | [Hab Hbb]].
  - left. subst a b. reflexivity.
  - right. subst a b. reflexivity.
Qed.

Lemma adj_E_minus_dbase_dtip_iff_twin_in_E :
  forall E d,
    In d (darts_of E) ->
    In d E ->
    dbase d <> dtip d ->
    adj (E_minus E d) (dbase d) (dtip d) <->
    In (twin d) E.
Proof.
  intros E d Hd Hin Hne. split.
  - intros [ec [Hec Hor]].
    apply in_E_minus in Hec. destruct Hec as [HinE Hned].
    destruct (adj_dbase_dtip_witness_carrier E d ec Hd Hne HinE Hor) as [-> | Htwin].
    + contradiction.
    + rewrite <- Htwin. exact HinE.
  - intros HinTwin.
    unfold adj. exists (twin d). split.
    + apply in_E_minus. split.
      * exact HinTwin.
      * intro H. exfalso. apply (twin_neq_self d Hne). exact H.
    + right. destruct (twin_edge_endpoints_swap d) as [Hfst Hsnd]. split; assumption.
Qed.

Lemma not_adj_E_minus_from_dbase_out :
  forall E d u,
    (forall ec, In ec (outgoing (dbase d) (darts_of E)) -> ec = d) ->
    In d (darts_of E) ->
    In d E ->
    ~ In (twin d) E ->
    u <> dbase d ->
    ~ adj (E_minus E d) (dbase d) u.
Proof.
  intros E d u Hout Hd Hin Hntwin Hu Hadj.
  destruct Hadj as [ec [Hec Hor]].
  apply in_E_minus in Hec. destruct Hec as [HinE Hned].
  destruct Hor as [[Hfu Hsu] | [Hfu Hsu]].
  - assert (Hin_out : In ec (outgoing (dbase d) (darts_of E))).
    { apply in_outgoing. split.
      - apply in_darts_of_orig. exact HinE.
      - unfold dbase. rewrite Hfu. reflexivity. }
    assert (Hecd : ec = d) by (apply Hout; exact Hin_out).
    rewrite Hecd in Hned. contradiction.
  - assert (Hin_out : In (twin ec) (outgoing (dbase d) (darts_of E))).
    { apply in_outgoing. split.
      - apply in_darts_of_twin. exact HinE.
      - rewrite dbase_twin. unfold dbase, dtip in Hsu. exact Hsu. }
    assert (Htecd : twin ec = d) by (apply Hout; exact Hin_out).
    assert (Hecd : ec = twin d).
    { rewrite <- (twin_involutive d) in Htecd. apply twin_inj. exact Htecd. }
    rewrite Hecd in HinE. contradiction.
Qed.

Lemma not_adj_E_minus_from_dbase_singleton :
  forall E d u,
    In d (darts_of E) ->
    In d E ->
    ~ In (twin d) E ->
    outgoing (dbase d) (darts_of E) = [d] ->
    u <> dbase d ->
    ~ adj (E_minus E d) (dbase d) u.
Proof.
  intros E d u Hd Hin Hntwin Hsing Hu Hadj.
  apply (not_adj_E_minus_from_dbase_out E d u
    (fun ec Hin_out =>
      @outgoing_eq_singleton_in (dbase d) (darts_of E) d ec Hsing Hin_out)
    Hd Hin Hntwin Hu Hadj).
Qed.

Lemma not_adj_E_minus_to_dtip_out :
  forall E d u,
    (forall ec, In ec (outgoing (dtip d) (darts_of E)) -> ec = twin d) ->
    In d (darts_of E) ->
    In (twin d) E ->
    ~ In d E ->
    u <> dtip d ->
    ~ adj (E_minus E (twin d)) u (dtip d).
Proof.
  intros E d u Hout Hd HinTwin Hnd Hu Hadj.
  destruct Hadj as [ec [Hec Hor]].
  apply in_E_minus in Hec. destruct Hec as [HinE Hned].
  destruct Hor as [[Hfu Hsu] | [Hfu Hsu]].
  - assert (Hin_out : In (twin ec) (outgoing (dtip d) (darts_of E))).
    { apply in_outgoing. split.
      - apply in_darts_of_twin. exact HinE.
      - rewrite dbase_twin. unfold dbase, dtip in Hsu. exact Hsu. }
    assert (Htecd : twin ec = twin d) by (apply Hout; exact Hin_out).
    assert (Hecd : ec = d).
    { rewrite <- (twin_involutive ec) in Htecd. apply twin_inj. exact Htecd. }
    rewrite Hecd in HinE. contradiction.
  - assert (Hin_out : In ec (outgoing (dtip d) (darts_of E))).
    { apply in_outgoing. split.
      - apply in_darts_of_orig. exact HinE.
      - unfold dbase, dtip in Hfu. exact Hfu. }
    assert (Hecd : ec = twin d) by (apply Hout; exact Hin_out).
    rewrite Hecd in Hned. contradiction.
Qed.

Lemma not_adj_E_minus_to_dtip_singleton :
  forall E d u,
    In d (darts_of E) ->
    In (twin d) E ->
    ~ In d E ->
    outgoing (dtip d) (darts_of E) = [twin d] ->
    u <> dtip d ->
    ~ adj (E_minus E (twin d)) u (dtip d).
Proof.
  intros E d u Hd HinTwin Hnd Hsing Hu Hadj.
  apply (not_adj_E_minus_to_dtip_out E d u
    (fun ec Hin_out =>
      @outgoing_eq_singleton_in (dtip d) (darts_of E) (twin d) ec Hsing Hin_out)
    Hd HinTwin Hnd Hu Hadj).
Qed.

Lemma reachable_E_minus_from_dbase_singleton :
  forall E d u,
    In d (darts_of E) ->
    In d E ->
    ~ In (twin d) E ->
    outgoing (dbase d) (darts_of E) = [d] ->
    reachable (E_minus E d) (dbase d) u -> u = dbase d.
Proof.
  intros E d u Hd Hin Hntwin Hsing Hreach.
  assert (Hmain :
    forall (u0 : Point) (Hsing0 : outgoing (dbase d) (darts_of E) = [d])
      (Hreach0 : reachable (E_minus E d) (dbase d) u0), u0 = dbase d).
  { clear u Hsing Hreach.
    intros u0 Hsing0 Hreach0.
    assert (singleton_fan : outgoing (dbase d) (darts_of E) = [d]) by exact Hsing0.
    clear Hsing0.
    remember (dbase d) as b eqn:Hb.
    pose proof Hb as Hbb.
    set (stay_at_b := fun (s t : Point) => s = b -> t = b).
    assert (Hstay : stay_at_b b u0).
    { apply (@reachable_ind (E_minus E d) stay_at_b).
      { intros s Hprem. destruct Hprem. reflexivity. }
      { intros p v w Hadj Htail IH Hprem.
        subst p.
        destruct (point_eq_dec v b) as [Hv | Hvneq].
        - destruct Hv as [->]. eauto.
        - exfalso.
          assert (Hsf : outgoing (dbase d) (darts_of E) = [d]).
          { exact (eq_ind b (fun p => outgoing p (darts_of E) = [d]) singleton_fan (dbase d) Hbb). }
          assert (Hadj' : adj (E_minus E d) (dbase d) v).
          { exact (eq_ind b (fun p => adj (E_minus E d) p v) Hadj (dbase d) Hbb). }
          assert (Hvneq' : v <> dbase d).
          { intro Heq. apply Hvneq. rewrite <- Hbb in Heq. exact Heq. }
          apply (not_adj_E_minus_from_dbase_singleton E d v Hd Hin Hntwin Hsf Hvneq' Hadj'). }
      { exact Hreach0. } }
    destruct Hb as [->]. apply Hstay. reflexivity. }
  apply (Hmain u Hsing). exact Hreach.
Qed.

Lemma reachable_E_minus_to_dtip_singleton :
  forall E d u,
    In d (darts_of E) ->
    In (twin d) E ->
    ~ In d E ->
    outgoing (dtip d) (darts_of E) = [twin d] ->
    reachable (E_minus E (twin d)) u (dtip d) -> u = dtip d.
Proof.
  intros E d u Hd HinTwin Hnd Hsing Hreach.
  assert (Hmain :
    forall (u0 : Point) (Hsing0 : outgoing (dtip d) (darts_of E) = [twin d])
      (Hreach0 : reachable (E_minus E (twin d)) u0 (dtip d)), u0 = dtip d).
  { clear u Hsing Hreach.
    intros u0 Hsing0 Hreach0.
    assert (singleton_fan : outgoing (dtip d) (darts_of E) = [twin d]) by exact Hsing0.
    clear Hsing0.
    remember (dtip d) as t eqn:Ht.
    pose proof Ht as Htt.
    set (end_at_t := fun (s u : Point) => u = t -> s = t).
    assert (Hend : end_at_t u0 t).
    { apply (@reachable_ind (E_minus E (twin d)) end_at_t).
      { intros s Hprem. destruct Hprem. reflexivity. }
      { intros u1 v w Hadj Htail IH Hprem.
        assert (Hv := IH Hprem). subst w. subst v.
        destruct (point_eq_dec u1 t) as [Htip | Hneq].
        - destruct Htip as [->]. reflexivity.
        - exfalso.
          assert (Hsf : outgoing (dtip d) (darts_of E) = [twin d]).
          { exact (eq_ind t (fun p => outgoing p (darts_of E) = [twin d]) singleton_fan (dtip d) Htt). }
          assert (Hadj' : adj (E_minus E (twin d)) u1 (dtip d)).
          { exact (eq_ind t (fun p => adj (E_minus E (twin d)) u1 p) Hadj (dtip d) Htt). }
          assert (Hneq' : u1 <> dtip d).
          { intro Heq. apply Hneq. rewrite <- Htt in Heq. exact Heq. }
          apply (not_adj_E_minus_to_dtip_singleton E d u1 Hd HinTwin Hnd Hsf Hneq' Hadj'). }
      { exact Hreach0. } }
    destruct Ht as [->]. apply Hend. reflexivity. }
  apply (Hmain u Hsing). exact Hreach.
Qed.

Lemma same_face_twin_disconnect_singleton_out :
  forall E d,
    In d (darts_of E) ->
    In d E ->
    ~ In (twin d) E ->
    dbase d <> dtip d ->
    outgoing (dbase d) (darts_of E) = [d] ->
    ~ reachable (E_minus E d) (dbase d) (dtip d).
Proof.
  intros E d Hd Hin Hntwin Hne Hsing.
  intro Hreach.
  assert (Heq := reachable_E_minus_from_dbase_singleton E d (dtip d) Hd Hin Hntwin Hsing Hreach).
  apply Hne. symmetry. exact Heq.
Qed.

Lemma same_face_twin_disconnect_singleton_twin :
  forall E d,
    In d (darts_of E) ->
    In (twin d) E ->
    ~ In d E ->
    dbase d <> dtip d ->
    outgoing (dtip d) (darts_of E) = [twin d] ->
    ~ reachable (E_minus E (twin d)) (dbase d) (dtip d).
Proof.
  intros E d Hd HinTwin Hnd Hne Hsing.
  intro Hreach.
  assert (Heq := reachable_E_minus_to_dtip_singleton E d (dbase d) Hd HinTwin Hnd Hsing Hreach).
  apply Hne. exact Heq.
Qed.

Lemma same_face_twin_disconnect_e_eq_d_singleton :
  forall E d e,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    In d E ->
    ~ In (twin d) E ->
    dbase d <> dtip d ->
    same_face (darts_of E) d (twin d) ->
    In e E ->
    e = d ->
    outgoing (dbase d) (darts_of E) = [d] ->
    ~ reachable (E_minus E e) (dbase d) (dtip d).
Proof.
  intros E d e _ _ Hd Hin Hntwin Hne _ _ He Hsing.
  subst e. apply same_face_twin_disconnect_singleton_out; assumption.
Qed.

Lemma same_face_twin_disconnect_e_eq_twin_singleton :
  forall E d e,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    dbase d <> dtip d ->
    same_face (darts_of E) d (twin d) ->
    In e E ->
    e = twin d ->
    In (twin d) E ->
    ~ In d E ->
    outgoing (dtip d) (darts_of E) = [twin d] ->
    ~ reachable (E_minus E e) (dbase d) (dtip d).
Proof.
  intros E d e _ _ Hd Hne _ _ He Htwin Hnd Hsing.
  subst e. apply same_face_twin_disconnect_singleton_twin; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3b-iii  Rotation-system disconnectivity core (Rung 3b close-out).          *)
(* -------------------------------------------------------------------------- *)

(* A non-degenerate segment properly crosses its own reversal (midpoint witness). *)
Lemma seg_properly_crosses_reversal :
  forall p q : Point, p <> q ->
    segments_intersect_properly p q q p.
Proof.
  intros p q _.
  unfold segments_intersect_properly.
  exists (1/2), (1/2).
  repeat split; try lra.
Qed.

(* Both orientations present in `E` refute undirected pairwise general position. *)
Lemma twin_orientations_properly_cross_in_E :
  forall (E : list Edge) (d : Dart),
    In d E -> In (twin d) E -> dbase d <> dtip d ->
    ~ pairwise_no_proper_cross E.
Proof.
  intros E d Hd Htwin Hne Hpw.
  assert (Hne' : d <> twin d).
  { intro Heq. apply (twin_neq_self d Hne). symmetry. exact Heq. }
  apply (Hpw d (twin d) Hd Htwin Hne').
  destruct d as [p q]. cbn [fst snd twin] in *.
  apply seg_properly_crosses_reversal. exact Hne.
Qed.

(* Well-noded survivor lists carry each undirected carrier at most once. *)
Lemma same_face_twin_carrier_exclusive_d :
  forall (E : list Edge) (d : Dart),
    well_noded_darts E ->
    In d E ->
    ~ In (twin d) E.
Proof.
  intros E d (Hgp & Hprop & _) Hd Htwin.
  assert (Hne : dbase d <> dtip d).
  { apply dart_endpoints_ne_of_proper. exact (Hprop d (in_darts_of_orig E d Hd)). }
  assert (Hne' : d <> twin d).
  { intro Heq. apply (twin_neq_self d Hne). symmetry. exact Heq. }
  pose proof (noded_gp_pairwise E Hgp) as Hpair.
  apply (Hpair d (twin d) Hd Htwin Hne').
  destruct d as [p q]. cbn [fst snd twin] in *.
  apply seg_properly_crosses_reversal. exact Hne.
Qed.

Lemma same_face_twin_carrier_exclusive_twin :
  forall (E : list Edge) (d : Dart),
    well_noded_darts E ->
    In (twin d) E ->
    ~ In d E.
Proof.
  intros E d Hwn Htwin Hd.
  assert (Hnt := same_face_twin_carrier_exclusive_d E (twin d) Hwn Htwin).
  rewrite twin_involutive in Hnt.
  apply Hnt. exact Hd.
Qed.

Lemma adj_E_minus_dtip_dbase_iff_d_in_E :
  forall E d,
    In d (darts_of E) ->
    In (twin d) E ->
    dbase d <> dtip d ->
    adj (E_minus E (twin d)) (dbase d) (dtip d) <->
    In d E.
Proof.
  intros E d Hd HinTwin Hne. split.
  - intros [ec [Hec Hor]].
    apply in_E_minus in Hec. destruct Hec as [HinE Hned].
    destruct (adj_dbase_dtip_witness_carrier E d ec Hd Hne HinE Hor) as [-> | Htwin].
    + exact HinE.
    + exfalso. apply Hned. exact Htwin.
  - intros Hin.
    unfold adj. exists d. split.
    + apply in_E_minus. split.
      * exact Hin.
      * intro H. exfalso. apply (twin_neq_self d Hne). symmetry. exact H.
    + left. split; reflexivity.
Qed.

Lemma not_adj_E_minus_dtip_dbase_when_twin_carrier :
  forall E d,
    In d (darts_of E) ->
    dbase d <> dtip d ->
    In (twin d) E ->
    ~ In d E ->
    ~ adj (E_minus E (twin d)) (dtip d) (dbase d).
Proof.
  intros E d Hd Hne HinTwin Hnd Hadj.
  apply adj_sym in Hadj.
  destruct (adj_E_minus_dtip_dbase_iff_d_in_E E d Hd HinTwin Hne) as [Hadj_to_In _].
  apply Hadj_to_In in Hadj. exact (Hnd Hadj).
Qed.

Lemma not_adj_E_minus_dbase_dtip_when_d_carrier :
  forall E d,
    In d (darts_of E) ->
    dbase d <> dtip d ->
    In d E ->
    ~ In (twin d) E ->
    ~ adj (E_minus E d) (dbase d) (dtip d).
Proof.
  intros E d Hd Hne Hin Hntwin Hadj.
  destruct (adj_E_minus_dbase_dtip_iff_twin_in_E E d Hd Hin Hne) as [Hadj_to_In _].
  apply Hadj_to_In in Hadj. exact (Hntwin Hadj).
Qed.

Lemma not_adj_E_minus_dtip_dbase_when_d_carrier :
  forall E d,
    In d (darts_of E) ->
    dbase d <> dtip d ->
    In d E ->
    ~ In (twin d) E ->
    ~ adj (E_minus E d) (dtip d) (dbase d).
Proof.
  intros E d Hd Hne Hin Hntwin Hadj.
  apply adj_sym in Hadj.
  apply (not_adj_E_minus_dbase_dtip_when_d_carrier E d Hd Hne Hin Hntwin Hadj).
Qed.

Lemma not_adj_E_minus_dbase_dtip_when_twin_carrier :
  forall E d,
    In d (darts_of E) ->
    dbase d <> dtip d ->
    In (twin d) E ->
    ~ In d E ->
    ~ adj (E_minus E (twin d)) (dbase d) (dtip d).
Proof.
  intros E d Hd Hne HinTwin Hnd Hadj.
  destruct (adj_E_minus_dtip_dbase_iff_d_in_E E d Hd HinTwin Hne) as [Hadj_to_In _].
  apply Hadj_to_In in Hadj. exact (Hnd Hadj).
Qed.

Lemma not_adj_E_minus_dtip_dbase_at :
  forall E d u,
    In d (darts_of E) ->
    dbase d <> dtip d ->
    In d E ->
    ~ In (twin d) E ->
    u = dbase d ->
    ~ adj (E_minus E d) (dtip d) u.
Proof.
  intros E d u Hd Hne Hin Hntwin Hu Hadj.
  subst u.
  apply (not_adj_E_minus_dtip_dbase_when_d_carrier E d Hd Hne Hin Hntwin).
  exact Hadj.
Qed.

Lemma not_adj_E_minus_dbase_dtip_at :
  forall E d u,
    In d (darts_of E) ->
    dbase d <> dtip d ->
    In (twin d) E ->
    ~ In d E ->
    u = dtip d ->
    ~ adj (E_minus E (twin d)) (dbase d) u.
Proof.
  intros E d u Hd Hne HinTwin Hnd Hu Hadj.
  subst u.
  apply (not_adj_E_minus_dbase_dtip_when_twin_carrier E d Hd Hne HinTwin Hnd).
  exact Hadj.
Qed.

Definition dart_endpoints_ne (d : Dart) : Prop :=
  dbase d <> dtip d.

Lemma dart_endpoints_neE :
  forall d, dart_endpoints_ne d -> dbase d <> dtip d.
Proof. intros d H. exact H. Qed.

(* A nontrivial `E_minus` step into `dbase d` is witnessed by an outgoing dart at
   `dbase d` other than the removed carrier `d`. *)
Lemma adj_E_minus_penult_to_dbase :
  forall E d u,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    In d E ->
    ~ In (twin d) E ->
    u <> dbase d ->
    adj (E_minus E d) u (dbase d) ->
    exists ec,
      In ec (outgoing (dbase d) (darts_of E)) /\
      ec <> d /\
      u = dtip ec.
Proof.
  intros E d u Hfan Hd Hin Hntwin Huneq Hadj.
  destruct Hadj as [ec [Hec Hor]].
  apply in_E_minus in Hec. destruct Hec as [HinE Hned].
  assert (HecD : In ec (darts_of E)) by (apply in_darts_of_orig; exact HinE).
  destruct Hor as [[Hfu Hsu] | [Hfu Hsu]].
  - set (ec' := twin ec).
    assert (HtwD : In ec' (darts_of E)) by (apply in_darts_of_twin; exact HinE).
    assert (Hned' : ec' <> d).
    { intro Heq'. apply Hntwin.
      assert (Ht : ec = twin d).
      { apply twin_inj. rewrite twin_involutive. rewrite <- Heq'. reflexivity. }
      rewrite Ht in HinE. exact HinE. }
    exists ec'. repeat split.
    + apply in_outgoing. split; [ exact HtwD | ].
      unfold ec'. rewrite dbase_twin. cbn [dtip] in Hsu. exact Hsu.
    + exact Hned'.
    + unfold ec'. cbn [dbase dtip]. rewrite dtip_twin. cbn [dbase]. symmetry. exact Hfu.
  - exists ec. repeat split.
    + apply in_outgoing. split; [ exact HecD | cbn [dbase]; exact Hfu ].
    + intro Heq. apply Hned. exact Heq.
    + cbn [dtip]. symmetry. exact Hsu.
Qed.

(* Mirror: a nontrivial step into `dtip d` uses an outgoing dart at `dtip d`
   other than the removed carrier `twin d`. *)
Lemma adj_E_minus_penult_to_dtip :
  forall E d u,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    In (twin d) E ->
    ~ In d E ->
    u <> dtip d ->
    adj (E_minus E (twin d)) u (dtip d) ->
    exists ec,
      In ec (outgoing (dtip d) (darts_of E)) /\
      ec <> twin d /\
      u = dtip ec.
Proof.
  intros E d u Hfan Hd HinTwin Hnd Huneq Hadj.
  destruct Hadj as [ec [Hec Hor]].
  apply in_E_minus in Hec. destruct Hec as [HinE Hned].
  assert (HecD : In ec (darts_of E)) by (apply in_darts_of_orig; exact HinE).
  destruct Hor as [[Hfu Hsu] | [Hfu Hsu]].
  - set (ec' := twin ec).
    assert (HtwD : In ec' (darts_of E)) by (apply in_darts_of_twin; exact HinE).
    assert (Hned' : ec' <> twin d).
    { intro Heq'. apply Hnd.
      assert (Ht : ec = d) by (apply twin_inj; unfold ec' in Heq'; exact Heq').
      rewrite Ht in HinE. exact HinE. }
    exists ec'. repeat split.
    + apply in_outgoing. split; [ exact HtwD | ].
      unfold ec'. rewrite dbase_twin. cbn [dtip] in Hsu. exact Hsu.
    + exact Hned'.
    + unfold ec'. cbn [dbase dtip]. rewrite dtip_twin. cbn [dbase]. symmetry. exact Hfu.
  - exists ec. repeat split.
    + apply in_outgoing. split; [ exact HecD | cbn [dbase]; exact Hfu ].
    + intro Heq. apply Hned. exact Heq.
    + cbn [dtip]. symmetry. exact Hsu.
Qed.

Lemma neq_eq_False {T : Type} (x y : T) : x <> y -> x = y -> False.
Proof. intros Hneq Heq. apply Hneq. exact Heq. Qed.

Lemma outgoing_dbase_tip_ne_dtip :
  forall E d ec,
    In d (darts_of E) ->
    dart_endpoints_ne d ->
    In ec (outgoing (dbase d) (darts_of E)) ->
    ec <> d ->
    dtip ec <> dtip d.
Proof.
  intros E d ec Hd Hde Hout Hecd Htip.
  assert (Hbase : dbase ec = dbase d)
    by (apply outgoing_base with (D := darts_of E); exact Hout).
  apply Hecd. apply dart_eq_of_endpoints; [ exact Hbase | exact Htip ].
Qed.

Lemma outgoing_dtip_tip_ne_dbase :
  forall E d ec,
    In d (darts_of E) ->
    dart_endpoints_ne d ->
    In ec (outgoing (dtip d) (darts_of E)) ->
    ec <> twin d ->
    dtip ec <> dbase d.
Proof.
  intros E d ec Hd Hde Hout Hecd Htip.
  assert (Hbase : dbase ec = dtip d)
    by (apply outgoing_base with (D := darts_of E); exact Hout).
  apply Hecd. apply dart_eq_of_endpoints; [ exact Hbase | exact Htip ].
Qed.

Lemma adj_E_minus_loop_endpoints_ne :
  forall (E : list Edge) (e ec : Edge),
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In ec (E_minus E e) ->
    fst ec = snd ec ->
    False.
Proof.
  intros E e ec Hfan HinE Heq.
  apply in_E_minus in HinE. destruct HinE as [HinEc _].
  assert (HecD : In ec (darts_of E)) by (apply in_darts_of_orig; exact HinEc).
  destruct ec as [a b]. cbn [fst snd] in Heq |- *.
  assert (Hprop : dbase (a, b) <> dtip (a, b)).
  { apply dart_endpoints_ne_of_proper.
    apply dart_proper_of_fan with (D := darts_of E); assumption. }
  cbn in Hprop. rewrite Heq in Hprop. apply Hprop. reflexivity.
Qed.
(* -------------------------------------------------------------------------- *)
(* Axiom audit (barrier layer).                                               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions seg_properly_crosses_reversal.
Print Assumptions same_face_twin_carrier_exclusive_d.
Print Assumptions not_adj_E_minus_dbase_dtip_at.
Print Assumptions adj_E_minus_penult_to_dbase.
Print Assumptions same_face_twin_disconnect_singleton_out.
