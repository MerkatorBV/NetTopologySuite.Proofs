(* ==========================================================================
   NetTopologySuite.Proofs.EdgeFaceBridgeCapstone
   ----------------------------------------------------------------------------
   extract_rings_valid R5, H_bridge rung: H_bridge_premise + same_face_twin_is_cut + twin-sep packaging + converse (rungs 3b-v, 4, 4b).

   Split (2026-08) from the former monolithic EdgeFaceBridge.v; original
   §-numbers are preserved so docs/extract-faces-bridge.md §19 and the
   verified-claims row remain accurate.  EdgeFaceBridge.v is the re-export
   umbrella (clients keep `Require Import EdgeFaceBridge`).

   Sections: §3b-v (named premise + disconnect + is_cut), §4 (contrapositive), §4b (converse).

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
                               EdgeFaceBridgeIncidence EdgeFaceBridgeTwinPath
                               EdgeFaceBridgeBarrier.

Import ListNotations.
(* ==========================================================================
   THE PLANAR-BRIDGE CORE (Rung 3b-v): formerly the development's one open seam,
   NOW DISCHARGED -- no `Admitted` remains.

   The fact: in a general-position, spur-free arrangement, if a proper dart `d`
   lies on the same face as its twin, then the carrier edge is a bridge --
   removing it (in whichever orientation is present in `E`) strands one endpoint
   from the other.  This is the classical planar theorem "an edge whose two darts
   share a face is a bridge"; it is TRUE.  Its proof is the planar Euler count
   `V - E + F = 1 + C` (the MapCounts / PermCycleCount / NumFacesSplice route):
   removing a same-face edge would SPLIT its face (`F+1`) -- contradicting Euler
   unless it instead DISCONNECTS (`C+1`), which is exactly the bridge conclusion.

   WHY PLANARITY MATTERS: the conclusion is a genus-0 fact.  It is FALSE for a
   non-planar rotation system, where a same-face edge can be a non-separating
   handle rather than a bridge.  Per-vertex `fan_ok` only constrains the angular
   order AT each vertex; it does not pin the genus.  The planar Euler identity
   (`euler_characteristic`) supplies the genus-0 input; it is carried as a NAMED
   hypothesis, never axiomatized.

   HOW IT IS DISCHARGED: rather than an `Admitted` theorem, the fact is carried as
   the named premise `H_bridge_premise E` (below) and threaded through the whole
   chain (`not_reachable_E_minus_*`, `same_face_twin_disconnect`,
   `same_face_twin_is_cut`, `edge_2_connected_twins_sep`, `H_bridge_well_noded`),
   all of which are `Qed` parametrically over it.  The premise is then PROVED
   downstream in `theories/HBridgeEuler.v` (`H_bridge_premise_from_euler`), where
   the full Euler/splice stack is in scope, from the named planar Euler
   hypotheses + `NumFacesSplice.num_faces_E_minus_splice` (face delta) +
   `num_edges_E_minus` (edge delta) via `EulerBridge.H_bridge_core_conclusion_from_euler`.
   The headline `extract_rings_valid` (theories-flocq/OverlayBridge.v) supplies
   those Euler hypotheses, so the corpus has NO `Admitted`; `Print Assumptions` on
   the capstones lists only the standard classical/funext axioms.  Mirrors the
   corpus's named-hypothesis pattern (e.g. parity_characterises_interior_cont). *)
(* The planar same-face=>bridge fact, now carried as a NAMED PREMISE
   `H_bridge_premise E` -- it is no longer an `Admitted` theorem.  It is threaded
   through the chain below and DISCHARGED downstream from the planar Euler
   identity in `theories/HBridgeEuler.v` (`H_bridge_premise_from_euler`), which
   the headline `extract_rings_valid` supplies via named `euler_characteristic`
   hypotheses.  So there is no `Admitted` in this development. *)
Definition H_bridge_premise (E : list Edge) : Prop :=
  forall d : Dart,
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    dart_endpoints_ne d ->
    (In d E -> ~ In (twin d) E ->
       ~ reachable (E_minus E d) (dtip d) (dbase d))
    /\ (In (twin d) E -> ~ In d E ->
       ~ reachable (E_minus E (twin d)) (dbase d) (dtip d)).

(* The two reach-core lemmas are now Qed, derived from the single premise. *)
Lemma not_reachable_E_minus_dtip_dbase :
  forall E d,
    H_bridge_premise E ->
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    noded_general_position E ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    dart_endpoints_ne d ->
    In d E ->
    ~ In (twin d) E ->
    ~ reachable (E_minus E d) (dtip d) (dbase d).
Proof.
  intros E d Hbr Hfan Hgp Hns Hd Hsf Hde Hin Hntwin.
  exact (proj1 (Hbr d Hd Hsf Hde) Hin Hntwin).
Qed.

Lemma not_reachable_E_minus_dbase_dtip :
  forall E d,
    H_bridge_premise E ->
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    noded_general_position E ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    same_face (darts_of E) d (twin d) ->
    dart_endpoints_ne d ->
    In (twin d) E ->
    ~ In d E ->
    ~ reachable (E_minus E (twin d)) (dbase d) (dtip d).
Proof.
  intros E d Hbr Hfan Hgp Hns Hd Hsf Hde HinTwin Hnd.
  exact (proj2 (Hbr d Hd Hsf Hde) HinTwin Hnd).
Qed.

Lemma same_face_twin_disconnect :
  forall (E : list Edge) (d : Dart) (e : Edge),
    H_bridge_premise E ->
    well_noded_darts E ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    dbase d <> dtip d ->
    same_face (darts_of E) d (twin d) ->
    In e E -> (e = d \/ e = twin d) ->
    ~ reachable (E_minus E e) (dbase d) (dtip d).
Proof.
  intros E d e Hbr Hwn Hns Hd Hne Hsf He Hcase.
  assert (Hfan : forall v : Point, fan_ok (outgoing v (darts_of E))).
  { intro v. apply well_noded_fan_ok. exact Hwn. }
  assert (Hgp : noded_general_position E) by (apply (proj1 Hwn)).
  assert (Hdn : dart_endpoints_ne d) by (unfold dart_endpoints_ne; exact Hne).
  destruct Hcase as [-> | ->].
  - assert (Hin : In d E) by exact He.
    assert (Hntwin : ~ In (twin d) E).
    { intro Ht. apply (same_face_twin_carrier_exclusive_d E d Hwn Hin Ht). }
    intro Hreach.
    apply (not_reachable_E_minus_dtip_dbase E d Hbr Hfan Hgp Hns Hd Hsf Hdn Hin Hntwin
      (reach_sym (E_minus E d) (dbase d) (dtip d) Hreach)).
  - assert (HinTwin : In (twin d) E) by exact He.
    assert (Hnd : ~ In d E).
    { intro Hd'. apply (same_face_twin_carrier_exclusive_twin E d Hwn HinTwin Hd'). }
    intro Hreach.
    apply (not_reachable_E_minus_dbase_dtip E d Hbr Hfan Hgp Hns Hd Hsf Hdn HinTwin Hnd).
    exact Hreach.
Qed.

Theorem same_face_twin_is_cut :
  forall (E : list Edge) (d : Dart),
    H_bridge_premise E ->
    well_noded_darts E ->
    no_spurs (darts_of E) ->
    In d (darts_of E) ->
    dbase d <> dtip d ->
    same_face (darts_of E) d (twin d) ->
    exists e : Edge,
      In e E /\ is_cut_edge E e /\ (e = d \/ e = twin d).
Proof.
  intros E d Hbr Hwn Hns Hd Hne Hsf.
  destruct (dart_carrier_edge E d Hd) as [e [He Hcase]].
  exists e. split; [ exact He | split ].
  - apply is_cut_edge_of_dart_disconnect with (d := d); [ exact Hd | exact Hne | exact He | exact Hcase | ].
    apply same_face_twin_disconnect with (E := E) (d := d) (e := e); assumption.
  - exact Hcase.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Contrapositive packaging.                                               *)
(* -------------------------------------------------------------------------- *)

Theorem edge_2_connected_twins_sep :
  forall (E : list Edge),
    H_bridge_premise E ->
    well_noded_darts E ->
    no_spurs (darts_of E) ->
    edge_2_connected E ->
    twins_in_different_faces (darts_of E).
Proof.
  intros E Hbr Hwn Hns H2. unfold twins_in_different_faces.
  intros d Hd Hsf.
  assert (Hne : dbase d <> dtip d).
  { apply dart_endpoints_ne_of_proper.
    destruct Hwn as (_ & Hprop & _).
    exact (Hprop d Hd). }
  destruct (same_face_twin_is_cut E d Hbr Hwn Hns Hd Hne Hsf) as
    [e [He [Hcut Hcase]]].
  apply (H2 e He). exact Hcut.
Qed.

Theorem H_bridge_well_noded :
  forall (E : list Edge),
    H_bridge_premise E ->
    well_noded_darts E ->
    no_spurs (darts_of E) ->
    edge_2_connected E ->
    twins_in_different_faces (darts_of E).
Proof.
  intros E Hbr Hwn Hns H2.
  apply (edge_2_connected_twins_sep E Hbr Hwn Hns H2).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4b  The CONVERSE: twins_in_different_faces -> edge_2_connected.             *)
(*                                                                            *)
(* The easy ("different faces => not a bridge") direction of the rotation-     *)
(* system bridge characterisation -- it needs NO planarity / Euler input       *)
(* (unlike the forward `same_face => cut`, which is genus-0).  If a proper      *)
(* dart `d0` does NOT share a face with its twin, then the REST of `d0`'s face  *)
(* walk (period >= 3 by `no_spurs`) is a bypass from `dtip d0` to `dbase d0`    *)
(* in `E_minus`: every walk dart differs from `d0` (no early return) and from   *)
(* `twin d0` (different faces), so each survives edge removal                   *)
(* (`dart_on_walk_endpoints_adj_E_minus`).                                      *)
(* -------------------------------------------------------------------------- *)

Lemma diff_face_bypass_E_minus :
  forall E d0 e,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    In d0 (darts_of E) ->
    ~ same_face (darts_of E) d0 (twin d0) ->
    In e E -> (e = d0 \/ e = twin d0) ->
    reachable (E_minus E e) (dtip d0) (dbase d0).
Proof.
  intros E d0 e Hfan Hns Hd0 Hdiff He Hcase.
  set (D := darts_of E).
  assert (Hok : arrangement_ok D) by (apply arrangement_ok_of_fan; exact Hfan).
  assert (Htw : forall z, In z D -> In (twin z) D) by (subst D; apply darts_of_closed_under_twin).
  assert (Hge3 : (3 <= face_period D d0)%nat) by (apply face_period_ge3_of_fan_nospur; assumption).
  destruct (face_period_spec D Hok d0 Hd0) as [_ Hpret].
  remember (face_period D d0) as k eqn:Hkeq.
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
      { exact (Hns d0 Hd0). }
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
        { intro H. exfalso.
          apply (iter_lt_face_period_not_self D d0 (S (S m')) Hok Hd0).
          { lia. }
          cbn [iter]. exact H. }
        { intro H. apply Hdiff. exists (S (S m')). cbn [iter]. exact H. } } }
  assert (Hend : dtip (iter (fstep D) (pred k) d0) = dbase d0).
  { destruct k as [| k']; [ lia | cbn [pred] ].
    assert (Hin : In (iter (fstep D) k' d0) D).
    { apply (face_walk_in D Htw d0 k' Hd0). }
    pose proof (dbase_fstep D (iter (fstep D) k' d0) Htw Hin) as Hbs.
    assert (Heq : fstep D (iter (fstep D) k' d0) = iter (fstep D) (S k') d0)
      by (cbn [iter]; reflexivity).
    rewrite Heq in Hbs. rewrite Hpret in Hbs. symmetry. exact Hbs. }
  assert (Hpred : (1 <= pred k < k)%nat) by lia.
  apply reach_trans with (dtip (iter (fstep D) (pred k) d0)).
  - apply (Hloop (pred k) Hpred).
  - rewrite Hend. apply reach_refl.
Qed.

Lemma diff_face_not_cut :
  forall E d0 e,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    In d0 (darts_of E) ->
    dbase d0 <> dtip d0 ->
    ~ same_face (darts_of E) d0 (twin d0) ->
    In e E -> (e = d0 \/ e = twin d0) ->
    ~ is_cut_edge E e.
Proof.
  intros E d0 e Hfan Hns Hd0 Hne Hdiff He Hcase.
  assert (Hby : reachable (E_minus E e) (dtip d0) (dbase d0))
    by (apply (diff_face_bypass_E_minus E d0 e); assumption).
  destruct Hcase as [-> | ->].
  - apply (reachable_E_minus_implies_not_cut E d0 (dbase d0) (dtip d0));
      [ exact He | reflexivity | reflexivity | exact Hne | ].
    apply reach_sym. exact Hby.
  - apply (reachable_E_minus_implies_not_cut E (twin d0) (dtip d0) (dbase d0)).
    + exact He.
    + rewrite dbase_twin. reflexivity.
    + rewrite dtip_twin. reflexivity.
    + apply not_eq_sym. exact Hne.
    + exact Hby.
Qed.

(* Converse of `edge_2_connected_twins_sep` -- and, unlike it, NEEDS NO
   `H_bridge_premise`/Euler.  Together they give the full equivalence
   `edge_2_connected E <-> twins_in_different_faces (darts_of E)` (under
   well_noded + no_spurs, the forward direction modulo the planar premise). *)
Theorem twins_in_different_faces_edge_2_connected :
  forall E,
    well_noded_darts E ->
    no_spurs (darts_of E) ->
    twins_in_different_faces (darts_of E) ->
    edge_2_connected E.
Proof.
  intros E Hwn Hns Hsep e He.
  assert (Hfan : forall v : Point, fan_ok (outgoing v (darts_of E)))
    by (intro v; apply well_noded_fan_ok; exact Hwn).
  assert (HeD : In e (darts_of E)) by (apply in_darts_of_orig; exact He).
  assert (Hne : dbase e <> dtip e).
  { apply dart_endpoints_ne_of_proper. destruct Hwn as (_ & Hap & _). exact (Hap e HeD). }
  apply (diff_face_not_cut E e e Hfan Hns HeD Hne (Hsep e HeD) He).
  left. reflexivity.
Qed.
(* -------------------------------------------------------------------------- *)
(* Axiom audit (capstone).                                                    *)
(* -------------------------------------------------------------------------- *)

Print Assumptions same_face_twin_disconnect.
Print Assumptions same_face_twin_is_cut.
Print Assumptions edge_2_connected_twins_sep.
Print Assumptions H_bridge_well_noded.
Print Assumptions diff_face_bypass_E_minus.
Print Assumptions twins_in_different_faces_edge_2_connected.
