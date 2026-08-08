(* ==========================================================================
   NetTopologySuite.Proofs.EdgeFaceBridgeTwinPath
   ----------------------------------------------------------------------------
   extract_rings_valid R5, H_bridge rung: twin step index, first-twin scan, E_minus walk adjacency, face-prefix loop (rung 3 / 3b-i).

   Split (2026-08) from the former monolithic EdgeFaceBridge.v; original
   §-numbers are preserved so docs/extract-faces-bridge.md §19 and the
   verified-claims row remain accurate.  EdgeFaceBridge.v is the re-export
   umbrella (clients keep `Require Import EdgeFaceBridge`).

   Sections: §3 (Toward same_face_twin_is_cut).

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
                               EdgeFaceBridgeIncidence.

Import ListNotations.
(* -------------------------------------------------------------------------- *)
(* §3  Toward same_face_twin_is_cut (Rung 3).                                   *)
(* -------------------------------------------------------------------------- *)

Lemma all_proper_darts_of_fan :
  forall D, (forall v : Point, fan_ok (outgoing v D)) -> all_proper_darts D.
Proof.
  intros D Hfan d Hd. apply dart_proper_of_fan with (D := D); assumption.
Qed.

Lemma face_period_ge3_of_fan_nospur :
  forall E d,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    (3 <= face_period (darts_of E) d)%nat.
Proof.
  intros E d Hfan Hns Hd.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  assert (Hshort : no_short_faces D).
  { apply no_short_faces_of_proper_nospur; [ exact Hok | | exact Hns ].
    apply all_proper_darts_of_fan. exact Hfan. }
  unfold no_short_faces in Hshort. exact (Hshort d Hd).
Qed.

Lemma same_face_twin_step_index :
  forall E d,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    exists k, (k < face_period (darts_of E) d)%nat /\
      iter (fstep (darts_of E)) k d = twin d.
Proof.
  intros E d Hfan Hd Hsf.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  assert (Htwin : In (twin d) (dart_walk D d (face_period D d))).
  { subst D; apply same_face_twin_in_period_walk; assumption. }
  apply dart_walk_iter_iff in Htwin.
  destruct Htwin as [k [Hk Hit]]. exists k. split; [ exact Hk | exact Hit ].
Qed.

Lemma same_face_twin_step_not_one :
  forall E d k,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    iter (fstep (darts_of E)) k d = twin d ->
    (2 <= k)%nat.
Proof.
  intros E d k Hfan Hns Hd Hit.
  assert (Hne : dbase d <> dtip d).
  { apply dart_endpoints_ne_of_proper.
    apply dart_proper_of_fan with (D := darts_of E) (d := d); [ exact Hd | exact Hfan ]. }
  destruct k as [| k']; cbn [iter] in Hit.
  - exfalso. apply (twin_neq_self d Hne). symmetry. exact Hit.
  - destruct k' as [| k'']; [ | lia ].
    exfalso. apply (Hns d Hd). exact Hit.
Qed.

(* First index on a candidate list where `fstep^k d` reaches `twin d`. *)
Fixpoint first_twin_at (D : list Dart) (d : Dart) (l : list nat) : nat :=
  match l with
  | [] => O
  | k :: rest =>
      if dart_eq_dec (iter (fstep D) k d) (twin d)
      then k
      else first_twin_at D d rest
  end.

Lemma first_twin_at_finds :
  forall D d l,
    (exists k, In k l /\ iter (fstep D) k d = twin d) ->
    In (first_twin_at D d l) l /\
    iter (fstep D) (first_twin_at D d l) d = twin d.
Proof.
  intros D d l. induction l as [| k0 rest IH]; intros [k [Hk Hret]].
  - destruct Hk.
  - cbn [first_twin_at].
    destruct (dart_eq_dec (iter (fstep D) k0 d) (twin d)) as [E | E].
    + split; [ left; reflexivity | exact E ].
    + destruct Hk as [-> | Hk].
      * contradiction.
      * destruct (IH (ex_intro _ k (conj Hk Hret))) as [Hin Hr].
        split; [ right; exact Hin | exact Hr ].
Qed.

Fixpoint first_twin_scan (D : list Dart) (d : Dart) (rem m : nat) {struct rem} : nat :=
  match rem with
  | O => O
  | S rem' =>
      if dart_eq_dec (iter (fstep D) m d) (twin d)
      then m
      else first_twin_scan D d rem' (S m)
  end.

Lemma first_twin_at_seq_shift :
  forall D d m n, first_twin_at D d (seq m n) = first_twin_scan D d n m.
Proof.
  intros D d m n. revert D m.
  induction n as [| n' IHn']; intros D m.
  - reflexivity.
  - cbn [seq first_twin_at first_twin_scan].
    destruct (dart_eq_dec (iter (fstep D) m d) (twin d)) as [Em | Em].
    + reflexivity.
    + rewrite (IHn' D (S m)). reflexivity.
Qed.

Lemma first_twin_scan_le :
  forall D d rem m k,
    (m <= k < m + rem)%nat ->
    iter (fstep D) k d = twin d ->
    (first_twin_scan D d rem m <= k)%nat.
Proof.
  intros D d rem m k Hrange Hret.
  revert D m Hrange Hret.
  induction rem as [| rem' IHrem']; intros D m [Hm Hk] Hret.
  - lia.
  - cbn [first_twin_scan].
    destruct (dart_eq_dec (iter (fstep D) m d) (twin d)) as [Em | Em].
    + subst. exact Hm.
    + assert (Hm' : (S m <= k < S m + rem')%nat).
      { split.
        - destruct (Nat.eq_dec m k) as [-> | Hneq]; [ exfalso; apply Em; exact Hret | lia ].
        - lia. }
      apply (IHrem' D (S m) Hm' Hret).
Qed.

Lemma first_twin_at_le_seq :
  forall D d n j,
    In j (seq 1 n) ->
    iter (fstep D) j d = twin d ->
    (first_twin_at D d (seq 1 n) <= j)%nat.
Proof.
  intros D d n j Hin Hret.
  apply in_seq in Hin. destruct Hin as [Hj1 Hjn].
  rewrite (first_twin_at_seq_shift D d 1 n).
  apply (first_twin_scan_le D d n 1 j); [ lia | exact Hret ].
Qed.

Lemma first_twin_at_no_earlier_seq :
  forall D d n k,
    In k (seq 1 n) ->
    (k < first_twin_at D d (seq 1 n))%nat ->
    iter (fstep D) k d <> twin d.
Proof.
  intros D d n k Hin Hlt contra.
  assert (Hle := first_twin_at_le_seq D d n k Hin contra).
  rewrite first_twin_at_seq_shift in Hlt, Hle. lia.
Qed.

Lemma iter_lt_face_period_not_self :
  forall D d j,
    arrangement_ok D ->
    In d D ->
    (1 <= j < face_period D d)%nat ->
    iter (fstep D) j d <> d.
Proof.
  intros D d j Hok Hd Hj.
  apply (face_period_no_early_return D d j Hok Hd Hj).
Qed.

Lemma first_twin_at_lt_of_witness :
  forall D d n j,
    (j < face_period D d)%nat ->
    In j (seq 1 n) ->
    iter (fstep D) j d = twin d ->
    (first_twin_at D d (seq 1 n) < face_period D d)%nat.
Proof.
  intros D d n j Hjfp Hin Hret.
  apply (Nat.le_lt_trans (first_twin_at D d (seq 1 n)) j (face_period D d));
    [ apply first_twin_at_le_seq; assumption | exact Hjfp ].
Qed.

Lemma same_face_twin_first_step_index :
  forall E d,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    exists k, (2 <= k < face_period (darts_of E) d)%nat /\
      iter (fstep (darts_of E)) k d = twin d /\
      (forall j, (1 <= j < k)%nat -> iter (fstep (darts_of E)) j d <> twin d).
Proof.
  intros E d Hfan Hns Hd Hsf.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  destruct (same_face_twin_step_index E d Hfan Hd Hsf) as [k0 [Hk0 Hit0]].
  assert (H2 : (2 <= k0)%nat) by (apply (same_face_twin_step_not_one E d k0); assumption).
  destruct (face_period_spec D Hok d Hd) as [Hp _].
  assert (Hin0 : In k0 (seq 1 (face_period D d))).
  { subst D. apply in_seq. lia. }
  set (k := first_twin_at D d (seq 1 (face_period D d))).
  destruct (first_twin_at_finds D d (seq 1 (face_period D d))
              (ex_intro _ k0 (conj Hin0 Hit0))) as [Hin Htwin].
  exists k. repeat split.
  - assert (H2k : (2 <= k)%nat) by (apply (same_face_twin_step_not_one E d k Hfan Hns Hd Htwin)).
    exact H2k.
  - assert (Hk0D : (k0 < face_period D d)%nat) by (subst D; exact Hk0).
    assert (Hkfp := first_twin_at_lt_of_witness D d (face_period D d) k0 Hk0D Hin0 Hit0).
    unfold k. exact Hkfp.
  - exact Htwin.
  - intros j Hj contra.
    unfold k in Hj.
    destruct Hj as [Hj1 Hj2].
    assert (Hk0D : (k0 < face_period D d)%nat) by (subst D; exact Hk0).
    assert (Hkfp := first_twin_at_lt_of_witness D d (face_period D d) k0 Hk0D Hin0 Hit0).
    assert (Hin' : In j (seq 1 (face_period D d))).
    { apply in_seq. split; [ exact Hj1 | ]. unfold k. lia. }
    apply (first_twin_at_no_earlier_seq D d (face_period D d) j Hin' Hj2 contra).
Qed.

Lemma is_cut_edge_of_disconnect :
  forall (E : list Edge) (e : Edge) (u v : Point),
    In e E -> fst e = u -> snd e = v -> u <> v ->
    reachable E u v ->
    ~ reachable (E_minus E e) u v ->
    is_cut_edge E e.
Proof.
  intros E e u v He Hfu Hsv Huv Hreach Hdis.
  unfold is_cut_edge. repeat split.
  - exact He.
  - rewrite Hfu, Hsv. exact Huv.
  - rewrite Hfu, Hsv. exact Hreach.
  - rewrite Hfu, Hsv. exact Hdis.
Qed.

Lemma dart_endpoints_adj_E_minus :
  forall E d e,
    In d (darts_of E) -> dbase d <> dtip d ->
    In e E -> e <> d -> e <> twin d ->
    adj (E_minus E e) (dbase d) (dtip d).
Proof.
  intros E d e Hd Hne He Hned Hntwin.
  destruct (dart_carrier_edge E d Hd) as [ec [Hec Hcase]].
  unfold adj. exists ec. split.
  - apply in_E_minus. split; [ exact Hec | ].
    intro Heq. destruct Hcase as [-> | Htwin].
    + apply Hned. symmetry. exact Heq.
    + apply Hntwin. rewrite <- Heq. exact Htwin.
  - destruct Hcase as [-> | Htwin].
    + left. split; reflexivity.
    + right. rewrite Htwin. split; [ apply dbase_twin | apply dtip_twin ].
Qed.

Lemma is_cut_edge_of_dart_disconnect :
  forall E d e,
    In d (darts_of E) -> dbase d <> dtip d ->
    In e E -> (e = d \/ e = twin d) ->
    ~ reachable (E_minus E e) (dbase d) (dtip d) ->
    is_cut_edge E e.
Proof.
  intros E d e Hd Hne He Hcase Hdis.
  assert (Hreach : reachable E (dbase d) (dtip d))
    by (apply dart_endpoints_reachable; assumption).
  assert (Hprop : fst e <> snd e).
  { apply dart_carrier_proper with (E := E) (d := d) (e := e); assumption. }
  destruct Hcase as [-> | Htwin].
  - apply is_cut_edge_of_disconnect with (u := dbase d) (v := dtip d);
      [ exact He | reflexivity | reflexivity | exact Hne | exact Hreach | exact Hdis ].
  - subst e.
    apply is_cut_edge_of_disconnect with (u := dtip d) (v := dbase d).
    + exact He.
    + apply dbase_twin.
    + apply dtip_twin.
    + exact Hprop.
    + apply reach_sym. exact Hreach.
    + intro Hr. apply Hdis. apply reach_sym in Hr. exact Hr.
Qed.

(* Easy direction: a bypass in `E_minus` refutes `is_cut_edge`. *)
Lemma reachable_E_minus_implies_not_cut :
  forall (E : list Edge) (e : Edge) (u v : Point),
    In e E -> fst e = u -> snd e = v -> u <> v ->
    reachable (E_minus E e) u v ->
    ~ is_cut_edge E e.
Proof.
  intros E e u v He Hfu Hsv Huv Hreach.
  intro Hcut. unfold is_cut_edge in Hcut.
  destruct Hcut as [_ [_ [_ Hdis]]].
  rewrite Hfu, Hsv in Hdis. exact (Hdis Hreach).
Qed.

(* `same_face` with `twin` places both orientations on the period walk, so the
   per-face twin-freeness hypothesis fails (the dumbbell obstruction). *)
Lemma same_face_twin_breaks_face_twin_free :
  forall E d,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    ~ face_twin_free (darts_of E) d (face_period (darts_of E) d).
Proof.
  intros E d Hfan Hd Hsf Htf.
  assert (Hdwalk : In d (dart_walk (darts_of E) d (face_period (darts_of E) d))).
  { apply same_face_refl_on_period_walk; assumption. }
  assert (Htwinwalk : In (twin d) (dart_walk (darts_of E) d (face_period (darts_of E) d))).
  { apply same_face_twin_in_period_walk; assumption. }
  apply (Htf d Hdwalk). exact Htwinwalk.
Qed.

(* Twin occurs at step `k >= 2`; the first `k` face-walk darts join `dbase d`
   to `dtip d` in the full edge graph. *)
Lemma same_face_twin_reachable_k :
  forall E d k,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    (2 <= k)%nat ->
    iter (fstep (darts_of E)) k d = twin d ->
    reachable E (dbase d) (dtip d).
Proof.
  intros E d k Hfan Hd Hk Hit.
  set (D := darts_of E).
  assert (Htw : forall z, In z D -> In (twin z) D)
    by (subst D; apply darts_of_closed_under_twin).
  assert (Hreach : reachable E (dbase d)
      (dtip (last (dart_walk D d k) d))).
  { subst D. apply (dart_walk_endpoints_reachable E d k); [ exact Hfan | exact Hd | lia ]. }
  assert (Hlast : last (dart_walk D d k) d = iter (fstep D) (pred k) d).
  { destruct k as [| k']; [ lia | destruct k' as [| k'']; [ lia | ]].
    apply dart_walk_last. }
  rewrite Hlast in Hreach.
  assert (Htip : dtip (iter (fstep D) (pred k) d) = dtip d).
  { destruct k as [| k']; [ lia | cbn [iter] ].
    assert (Hin : In (iter (fstep D) k' d) D).
    { apply (face_walk_in D Htw d k' Hd). }
    pose proof (dbase_fstep D (iter (fstep D) k' d) Htw Hin) as Hbs.
    assert (Heq : fstep D (iter (fstep D) k' d) = iter (fstep D) (S k') d)
      by (cbn [iter]; reflexivity).
    assert (Hit' : iter (fstep D) (S k') d = twin d) by (subst D; exact Hit).
    rewrite Heq in Hbs. rewrite Hit', dbase_twin in Hbs. symmetry. exact Hbs. }
  rewrite Htip in Hreach. exact Hreach.
Qed.

(* On the period walk, every dart except the carrier orientations stays
   adjacent after removing the carrier edge. *)
Lemma dart_on_walk_endpoints_adj_E_minus :
  forall E d0 e n x,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d0 (darts_of E) ->
    In e E -> (e = d0 \/ e = twin d0) ->
    In x (dart_walk (darts_of E) d0 n) ->
    x <> d0 -> x <> twin d0 ->
    adj (E_minus E e) (dbase x) (dtip x).
Proof.
  intros E d0 e n x Hfan Hd0 He Hcase Hx Hxd Hxtwin.
  assert (HxD : In x (darts_of E)).
  { set (D := darts_of E) in *.
    assert (Htw : forall z, In z D -> In (twin z) D)
      by (subst D; apply darts_of_closed_under_twin).
    apply (dart_walk_subset D Htw n d0 Hd0 x Hx). }
  assert (Hne : dbase x <> dtip x).
  { apply dart_endpoints_ne_of_proper.
    apply dart_proper_of_fan with (D := darts_of E); assumption. }
  assert (Hnex : e <> x).
  { intro H. destruct Hcase as [-> | Ht].
    - apply Hxd. symmetry. exact H.
    - apply Hxtwin. transitivity e; [ symmetry; exact H | exact Ht ]. }
  assert (Hnetx : e <> twin x).
  { intro H. destruct Hcase as [-> | Ht].
    - apply Hxtwin. symmetry. apply twin_inj. rewrite twin_involutive. exact H.
    - apply Hxd. apply twin_inj. rewrite <- Ht, H. reflexivity. }
  apply dart_endpoints_adj_E_minus with (d := x); assumption.
Qed.

(* After removing a carrier dart, the face-prefix walk from `dtip d0` loops at
   `dtip d0` once the twin step is reached (Rung 3b path layer). *)
Lemma same_face_twin_prefix_loop_E_minus :
  forall E d0 e,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    In d0 (darts_of E) ->
    same_face (darts_of E) d0 (twin d0) ->
    In e E -> (e = d0 \/ e = twin d0) ->
    reachable (E_minus E e) (dtip d0) (dtip d0).
Proof.
  intros E d0 e Hfan Hns Hd0 Hsf He Hcase.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  assert (Htw : forall z, In z D -> In (twin z) D) by (subst D; apply darts_of_closed_under_twin).
  destruct (same_face_twin_first_step_index E d0 Hfan Hns Hd0 Hsf) as
    [k [Hk2 [Htwin Hbefore]]].
  assert (Hloop : forall m, (1 <= m < k)%nat ->
      reachable (E_minus E e) (dtip d0) (dtip (iter (fstep D) m d0))).
  { intros m Hm.
    induction m as [| m IHm]; [ lia | destruct m as [| m'] ].
    - cbn [iter]. apply reach_one.
      assert (Hb := dbase_fstep D d0 Htw Hd0).
      rewrite <- Hb.
      assert (Hx : In (fstep D d0) (dart_walk D d0 2)).
      { apply dart_walk_iter_iff. exists 1%nat. split; [ lia | reflexivity ]. }
      apply (dart_on_walk_endpoints_adj_E_minus E d0 e 2%nat (fstep D d0)
          Hfan Hd0 He Hcase Hx).
      { apply (fstep_neq_self_of_proper D d0 Htw Hd0).
        apply dart_proper_of_fan with (D := D); assumption. }
      { intro H. apply (Hbefore 1%nat); [ destruct Hm; lia | exact H ]. }
    - assert (Hm' : (1 <= S m' < k)%nat) by lia.
      assert (Hx : In (iter (fstep D) (S m') d0) (dart_walk D d0 (S (S m')))).
      { apply dart_walk_iter_iff. exists (S m'). split; [ lia | reflexivity ]. }
      apply reach_trans with (dtip (iter (fstep D) (S m') d0)).
      { exact (IHm Hm'). }
      { apply reach_one.
        assert (Hin : In (iter (fstep D) (S m') d0) D).
        { apply (face_walk_in D Htw d0 (S m') Hd0). }
        assert (Hb := dbase_fstep D (iter (fstep D) (S m') d0) Htw Hin).
        assert (Hx' : In (fstep D (iter (fstep D) (S m') d0))
                    (dart_walk D d0 (S (S (S m'))))).
        { apply dart_walk_iter_iff. exists (S (S m')). split; [ lia | cbn [iter]; reflexivity ]. }
        rewrite <- Hb.
        apply (dart_on_walk_endpoints_adj_E_minus E d0 e (S (S (S m')))
          (fstep D (iter (fstep D) (S m') d0)) Hfan Hd0 He Hcase Hx').
        { intro H.
          exfalso.
          apply (iter_lt_face_period_not_self D d0 (S (S m')) Hok Hd0).
          { destruct Hm as [Hm1 Hm2]. split; [ lia | ].
            apply (Nat.lt_trans _ k _); [ exact Hm2 | destruct Hk2; subst D; lia ]. }
          cbn [iter]. exact H. }
        { intro H. apply (Hbefore (S (S m'))).
          destruct Hm as [Hm1 Hm2]. split; lia.
          cbn [iter]; exact H. } } }
  assert (Hend : dtip (iter (fstep D) (pred k) d0) = dtip d0).
  { destruct k as [| k']; [ lia | cbn [pred] ].
    assert (Hin : In (iter (fstep D) k' d0) D).
    { apply (face_walk_in D Htw d0 k' Hd0). }
    pose proof (dbase_fstep D (iter (fstep D) k' d0) Htw Hin) as Hbs.
    assert (Heq : fstep D (iter (fstep D) k' d0) = iter (fstep D) (S k') d0)
      by (cbn [iter]; reflexivity).
    assert (Htwin' : iter (fstep D) (S k') d0 = twin d0) by (subst D; exact Htwin).
    rewrite Heq in Hbs. rewrite Htwin', dbase_twin in Hbs. symmetry. exact Hbs. }
  assert (Hpred : (1 <= pred k < k)%nat).
  { destruct k as [| k']; [ lia | destruct k' as [| k'']; [ lia | lia ] ]. }
  apply reach_trans with (dtip (iter (fstep D) (pred k) d0)).
  - apply (Hloop (pred k) Hpred).
  - rewrite Hend. apply reach_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit (twin-path layer).                                             *)
(* -------------------------------------------------------------------------- *)

Print Assumptions face_period_ge3_of_fan_nospur.
Print Assumptions same_face_twin_step_index.
Print Assumptions is_cut_edge_of_dart_disconnect.
Print Assumptions reachable_E_minus_implies_not_cut.
Print Assumptions same_face_twin_breaks_face_twin_free.
Print Assumptions same_face_twin_reachable_k.
Print Assumptions dart_on_walk_endpoints_adj_E_minus.
Print Assumptions same_face_twin_first_step_index.
Print Assumptions same_face_twin_prefix_loop_E_minus.
