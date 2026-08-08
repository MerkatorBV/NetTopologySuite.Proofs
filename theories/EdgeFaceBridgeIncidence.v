(* ==========================================================================
   NetTopologySuite.Proofs.EdgeFaceBridgeIncidence
   ----------------------------------------------------------------------------
   extract_rings_valid R5, H_bridge rung: dart↔edge incidence + same_face↔dart_walk linkage (rungs 1–2).

   Split (2026-08) from the former monolithic EdgeFaceBridge.v; original
   §-numbers are preserved so docs/extract-faces-bridge.md §19 and the
   verified-claims row remain accurate.  EdgeFaceBridge.v is the re-export
   umbrella (clients keep `Require Import EdgeFaceBridge`).

   Sections: §1 (incidence), §2 (face-walk linkage).

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
                               NoShortFaces FaceTwinAware.

Import ListNotations.
(* -------------------------------------------------------------------------- *)
(* §1  Dart ↔ edge incidence (Edge = Dart in this corpus).                     *)
(* -------------------------------------------------------------------------- *)

Lemma dart_in_darts_of_cases :
  forall E d, In d (darts_of E) -> In d E \/ In (twin d) E.
Proof.
  intros E d H. unfold darts_of in H. apply in_app_or in H.
  destruct H as [H | H]; [ left; exact H | right ].
  apply in_map_iff in H. destruct H as [e [Heq Hin]]. rewrite <- Heq, twin_involutive.
  exact Hin.
Qed.

Lemma twin_in_darts_of_orig :
  forall E e, In e E -> In (twin e) (darts_of E).
Proof. intros E e H. apply in_darts_of_twin. exact H. Qed.

Lemma twin_edge_endpoints_swap :
  forall d, fst (twin d) = dtip d /\ snd (twin d) = dbase d.
Proof. intros d. rewrite dbase_twin, dtip_twin. split; reflexivity. Qed.

(* An edge of `E` carrying the same undirected segment as dart `d`. *)
Lemma dart_carrier_edge :
  forall E d, In d (darts_of E) ->
    exists e, In e E /\ (e = d \/ e = twin d).
Proof.
  intros E d H.
  destruct (dart_in_darts_of_cases E d H) as [Hd | Ht].
  - exists d. split; [ exact Hd | left; reflexivity ].
  - exists (twin d). split; [ exact Ht | right; reflexivity ].
Qed.

Lemma dart_carrier_proper :
  forall E d e,
    In d (darts_of E) -> dbase d <> dtip d ->
    In e E -> (e = d \/ e = twin d) ->
    fst e <> snd e.
Proof.
  intros E d e Hd Hne He [-> | ->].
  - cbn. exact Hne.
  - destruct (twin_edge_endpoints_swap d) as [Hfst Hsnd].
    rewrite Hfst, Hsnd. intro Heq. apply Hne. symmetry. exact Heq.
Qed.

Lemma dart_carrier_endpoints :
  forall E d e,
    In d (darts_of E) -> dbase d <> dtip d ->
    In e E -> (e = d \/ e = twin d) ->
    (fst e = dbase d /\ snd e = dtip d) \/
    (fst e = dtip d /\ snd e = dbase d).
Proof.
  intros E d e Hd Hne He Hcase.
  destruct Hcase as [-> | Htwin].
  - left. split; reflexivity.
  - right. destruct (twin_edge_endpoints_swap d) as [Hfst Hsnd].
    subst e. split; [ exact Hfst | exact Hsnd ].
Qed.

(* Endpoints of a proper dart are adjacent in the edge graph. *)
Lemma dart_endpoints_adj :
  forall E d, In d (darts_of E) -> dbase d <> dtip d ->
    adj E (dbase d) (dtip d).
Proof.
  intros E d Hd Hne.
  destruct (dart_carrier_edge E d Hd) as [e [He Hcase]].
  destruct Hcase as [-> | Htwin].
  - apply adj_edge. exact He.
  - assert (He' : In (twin d) E) by (rewrite <- Htwin; exact He).
    unfold adj. exists (twin d). split; [ exact He' | ].
    right. split; [ apply dbase_twin | apply dtip_twin ].
Qed.

(* Every graph adjacency step is witnessed by a dart of `darts_of E`. *)
Lemma adj_dart_carrier :
  forall E u v,
    adj E u v ->
    exists x, In x (darts_of E) /\
      ((dbase x = u /\ dtip x = v) \/ (dbase x = v /\ dtip x = u)).
Proof.
  intros E u v [e [He Hor]].
  destruct Hor as [[Hfu Hsv] | [Hfu Hsv]].
  - exists e. split; [ apply in_darts_of_orig; exact He | left; split; assumption ].
  - exists (twin e). split; [ apply in_darts_of_twin; exact He | ].
    left. rewrite dbase_twin, dtip_twin. split; assumption.
Qed.

Lemma adj_E_minus_dart_carrier :
  forall E e0 u v,
    adj (E_minus E e0) u v ->
    exists x, In x (darts_of E) /\
      ((dbase x = u /\ dtip x = v) \/ (dbase x = v /\ dtip x = u)).
Proof.
  intros E e0 u v [e [He Hor]].
  apply in_E_minus in He. destruct He as [Hin Hne].
  destruct Hor as [[Hfu Hsv] | [Hfu Hsv]].
  - exists e. split; [ apply in_darts_of_orig; exact Hin | left; split; assumption ].
  - exists (twin e). split; [ apply in_darts_of_twin; exact Hin | ].
    left. rewrite dbase_twin, dtip_twin. split; assumption.
Qed.

Lemma dart_endpoints_reachable :
  forall E d, In d (darts_of E) -> dbase d <> dtip d ->
    reachable E (dbase d) (dtip d).
Proof.
  intros E d Hd Hne. apply reach_one, dart_endpoints_adj; assumption.
Qed.

Lemma dart_endpoints_ne_of_proper :
  forall d, proper_dart d -> dbase d <> dtip d.
Proof.
  intros d Hpr Heq.
  apply Hpr. unfold ddir. rewrite Heq.
  unfold point_diff, vzero. apply Vec_eq; cbn [vx vy]; ring.
Qed.

Lemma dart_proper_of_fan :
  forall D d, In d D ->
    (forall v : Point, fan_ok (outgoing v D)) ->
    proper_dart d.
Proof.
  intros D d Hd Hfan.
  assert (Ho : In d (outgoing (dbase d) D)).
  { apply in_outgoing. split; [ exact Hd | reflexivity ]. }
  destruct (Hfan (dbase d)) as [Hprop _]. exact (Hprop d Ho).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Face walk ↔ same_face linkage.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma arrangement_ok_of_fan :
  forall E, (forall v, fan_ok (outgoing v (darts_of E))) ->
    arrangement_ok (darts_of E).
Proof. intros E H. apply arrangement_ok_darts_of. exact H. Qed.

Lemma same_face_in_period_walk :
  forall D a b,
    arrangement_ok D -> In a D ->
    same_face D a b ->
    In b (dart_walk D a (face_period D a)).
Proof.
  intros D a b Hok Ha Hsf.
  apply (walk_at_period_iff_same_face D Hok a Ha b). exact Hsf.
Qed.

Lemma same_face_twin_in_period_walk :
  forall E d,
    (forall v, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    In (twin d) (dart_walk (darts_of E) d (face_period (darts_of E) d)).
Proof.
  intros E d Hfan Hd Hsf.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  assert (Ha : In d D) by (subst D; exact Hd).
  apply (same_face_in_period_walk D d (twin d) Hok Ha Hsf).
Qed.

Lemma same_face_refl_on_period_walk :
  forall E d,
    (forall v, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    In d (dart_walk (darts_of E) d (face_period (darts_of E) d)).
Proof.
  intros E d Hfan Hd.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  assert (Ha : In d D) by (subst D; exact Hd).
  apply (same_face_in_period_walk D d d Hok Ha (same_face_refl D d)).
Qed.

Lemma same_face_twin_both_on_period_walk :
  forall E d,
    (forall v, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    In d (dart_walk (darts_of E) d (face_period (darts_of E) d)) /\
    In (twin d) (dart_walk (darts_of E) d (face_period (darts_of E) d)).
Proof.
  intros E d Hfan Hd Hsf. split.
  - apply same_face_refl_on_period_walk; assumption.
  - apply same_face_twin_in_period_walk; assumption.
Qed.

Lemma same_face_of_one_spur_step :
  forall D d, In d D -> fstep D d = twin d -> same_face D d (twin d).
Proof.
  intros D d Hd Hspur. exists 1%nat. cbn [iter]. exact Hspur.
Qed.

(* Every dart on a face walk is a carrier edge of `E` and joins its endpoints. *)
Lemma dart_on_walk_endpoints_adj :
  forall E d n x,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    In x (dart_walk (darts_of E) d n) ->
    adj E (dbase x) (dtip x).
Proof.
  intros E d n x Hfan Hd Hx.
  set (D := darts_of E).
  assert (Htw : forall z, In z D -> In (twin z) D)
    by (apply darts_of_closed_under_twin).
  assert (HxD : In x D) by (apply (dart_walk_subset D Htw n d Hd x Hx)).
  assert (Hne : dbase x <> dtip x).
  { apply dart_endpoints_ne_of_proper.
    apply dart_proper_of_fan with (D := D); assumption. }
  apply dart_endpoints_adj with (d := x); [ exact HxD | exact Hne ].
Qed.

(* Walk-level reachability: `iter (fstep D) n d` is the last dart of a length-(S n)
   walk (`dart_walk_last`), so its tip is reachable from `dbase d` in `E`. *)
Lemma dart_walk_endpoints_reachable_iter :
  forall (E : list Edge) (D : list Dart) (d : Dart) (n : nat),
    D = darts_of E ->
    (forall v : Point, fan_ok (outgoing v D)) ->
    (forall x, In x D -> In (twin x) D) ->
    In d D ->
    reachable E (dbase d) (dtip (iter (fstep D) n d)).
Proof.
  intros E D d n HD Hfan Htw Hd.
  revert d Hd.
  induction n as [| n IHn]; intros d Hd.
  - cbn [iter].
    assert (HdE : In d (darts_of E)) by (rewrite <- HD; exact Hd).
    apply dart_endpoints_reachable with (d := d); [ exact HdE | ].
    apply dart_endpoints_ne_of_proper, dart_proper_of_fan with (D := D); assumption.
  - cbn [iter].
    assert (HdE : In d (darts_of E)) by (rewrite <- HD; exact Hd).
    assert (HfanE : forall v, fan_ok (outgoing v (darts_of E))).
    { intro v. rewrite <- HD. apply Hfan. }
    apply reach_trans with (dtip d).
    + apply reach_one, dart_on_walk_endpoints_adj with (d := d) (n := S n)
        (x := d); [ exact HfanE | exact HdE | left; reflexivity ].
    + rewrite <- (dbase_fstep D d Htw Hd).
      assert (Heq : fstep D (iter (fstep D) n d) = iter (fstep D) n (fstep D d))
        by (symmetry; apply iter_succ_inside).
      rewrite Heq. apply IHn. apply fstep_in; assumption.
Qed.

Lemma dart_walk_endpoints_reachable :
  forall E d n,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    (1 <= n)%nat ->
    reachable E (dbase d)
      (dtip (last (dart_walk (darts_of E) d n) d)).
Proof.
  intros E d n Hfan Hd Hle.
  set (D := darts_of E).
  assert (Htw : forall x, In x D -> In (twin x) D)
    by (apply darts_of_closed_under_twin).
  destruct n as [| n']; [ lia | ].
  assert (Hlast : last (dart_walk D d (S n')) d = iter (fstep D) n' d).
  { apply dart_walk_last. }
  rewrite Hlast.
  apply (dart_walk_endpoints_reachable_iter E D d n'); [ reflexivity | exact Hfan | exact Htw | exact Hd ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit (incidence + walk layer).                                      *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dart_carrier_edge.
Print Assumptions dart_carrier_endpoints.
Print Assumptions dart_endpoints_reachable.
Print Assumptions dart_endpoints_ne_of_proper.
Print Assumptions same_face_twin_in_period_walk.
Print Assumptions same_face_twin_both_on_period_walk.
Print Assumptions dart_on_walk_endpoints_adj.
Print Assumptions dart_walk_endpoints_reachable_iter.
Print Assumptions dart_walk_endpoints_reachable.
