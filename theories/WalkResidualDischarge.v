(* ==========================================================================
   WalkResidualDischarge.v

   [H-bridge attack, C-3f discharge rung E-2c] THE RESIDUAL DISCHARGES:
   `walk_small_offset_connectivity` holds outright under the standing
   combinatorial / generic-position guards -- and with it, through the
   Qed bridge `face_transport_premise_of_walk_connectivity` (#355) and
   `H_bridge_premise_of_transport` (rung D core), the FULL
   `H_bridge_premise` is now a THEOREM of the guard set:

     fan_ok (per vertex) + no_spurs
       + pairwise_no_proper_cross_twin_aware
       + no_horizontal_darts + no_foreign_vertex_twin_aware
     |- H_bridge_premise E.

   THE ASSEMBLY (one proof, all ingredients Qed-banked):
     1. ring facts from the premise's own data: the dpath closes the
        chain (`cycle_closed_chain` -> `ring_edges_of_closed_chain`),
        the vertex-simple window is twin-free
        (`cycle_window_twin_free`), so the cycle ring is simple
        (`ring_simple_of_subset_twin_aware`), foreign-vertex-free
        (guard transfer), and taut
        (`ring_taut_of_simple_and_no_foreign_vertex`);
     2. the walk index `k` from `same_face_twin_first_step_index`
        (fan_ok + no_spurs), membership of every iterate by
        `OrbitCycle.iter_in` over `fstep_in`;
     3. fold the E-1 range corners over the walk
        (`range_family_fold` at `walk_corner_range_at`), fix ONE
        global `rho := Rmin tC (1/3) / 2` (below every corner cap,
        with `rho + rho < 1` for the rides and `rho <= 1/3` for the
        ties), fold the ride caps (`cap_family_fold` at
        `walk_ride_at`) and take the two tie caps (E-2b);
     4. choose `ef'` = HALF the Rmin of: the premise's `ef`, both tie
        caps, and the three delta caps converted through the linear
        `delta = corner_delta_for_ef_*(d, ef') = ef' * span / K`
        (`lt_div_scale` / `le_div_scale` do the conversions);
     5. assemble sym(west tie) o `walk_chain_to_twin` o east tie at
        the shared delta; the chain's start complement is the west
        tie's own left endpoint (`connected_in_complement_cont_left`).

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import Distance Overlay OverlayGraph Vec Azimuth
                               Direction Dart DartAngularOrder DartNext
                               DartNextSpec DartFace NoShortFaces OrbitCycle
                               FaceTwinAware PointInRingTangents
                               JordanCurveSeam JCT JCTHugStep RingClearance
                               JCTTautClearance SectorPath CornerSamples
                               CornerConnector FanGapSector FanCorner
                               WalkCorners WalkCornerRange DartPath
                               BufferAssembly RingExtract CycleRing
                               GeneralTautBridge
                               EdgeConnectivity ArrangementEMinus
                               EdgeFaceBridge HBridgeCoreSlice
                               WalkVertexPack WalkFamilies JCTCorridor
                               JCTMinOpenStep WalkCorridor MirrorCorridor
                               DartSideKit CornerCorridorBridge
                               WalkStepChain WalkChainInduction WalkEndTies
                               WalkRides WalkPremiseBridge WalkResidualKit
                               WalkResidualTies FaceOrbitSep
                               VertexGeneralPosition.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Linear cap conversions through `delta = ef * span / K`.                 *)
(* -------------------------------------------------------------------------- *)

Lemma lt_div_scale :
  forall (x b s K : R),
    0 < s -> 0 < K -> x < b * K / s -> x * s / K < b.
Proof.
  intros x b s K Hs HK Hx.
  apply (Rmult_lt_reg_r (K / s)).
  - unfold Rdiv.
    apply Rmult_lt_0_compat; [ exact HK | apply Rinv_0_lt_compat; exact Hs ].
  - replace (x * s / K * (K / s)) with x by (field; split; lra).
    replace (b * (K / s)) with (b * K / s) by (field; lra).
    exact Hx.
Qed.

Lemma le_div_scale :
  forall (x b s K F : R),
    0 < s -> 0 < K -> 0 < F -> x <= b * K / (F * s) -> F * (x * s / K) <= b.
Proof.
  intros x b s K F Hs HK HF Hx.
  apply (Rmult_le_reg_r (K / (F * s))).
  - unfold Rdiv.
    apply Rmult_lt_0_compat; [ exact HK | apply Rinv_0_lt_compat; nra ].
  - replace (F * (x * s / K) * (K / (F * s))) with x
      by (field; repeat split; lra).
    replace (b * (K / (F * s))) with (b * K / (F * s))
      by (field; repeat split; lra).
    exact Hx.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The headline: the walk residual holds.                                  *)
(* -------------------------------------------------------------------------- *)

Theorem walk_small_offset_connectivity_holds :
  forall E : list Edge,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    pairwise_no_proper_cross_twin_aware (darts_of E) ->
    no_horizontal_darts (darts_of E) ->
    no_foreign_vertex_twin_aware (darts_of E) ->
    walk_small_offset_connectivity E.
Proof.
  intros E Hfan Hns Hpw Hnh Hnfv.
  unfold walk_small_offset_connectivity.
  intros d c my ef HdE Hntwin Hproper Hsf Hp Hnd Hlen Hgen Hint Hef.
  set (D := darts_of E) in *.
  set (r := ring_of_chain (d :: c)) in *.
  (* ---- 1. ring facts from the premise's own data ---- *)
  assert (HdD : In d D) by (apply in_darts_of_orig; exact HdE).
  assert (Hcnil : c <> [])
    by (destruct c; [ cbn [length] in Hlen; lia | discriminate ]).
  assert (Hcc : closed_chain (d :: c))
    by (exact (cycle_closed_chain (darts_of (E_minus E d)) d c Hp Hcnil)).
  assert (Hedges : ring_edges r = d :: c)
    by (apply ring_edges_of_closed_chain; exact Hcc).
  assert (Htf : forall x, In x (d :: c) -> ~ In (twin x) (d :: c))
    by (exact (cycle_window_twin_free (darts_of (E_minus E d)) d c
                 Hp Hnd Hlen Hproper)).
  assert (HWD : forall x, In x (d :: c) -> In x D).
  { intros x [Hxd | Hxc].
    - rewrite <- Hxd. exact HdD.
    - apply (incl_darts_of_E_minus E d).
      exact (dpath_darts_in _ _ _ _ Hp x Hxc). }
  assert (Hsimple : ring_simple r).
  { apply (ring_simple_of_subset_twin_aware D (d :: c));
      [ exact Hpw | exact HWD | exact Htf | ].
    rewrite Hedges. intros e He. exact He. }
  assert (Hnfv_r : ring_no_vertex_on_foreign_edge_interior r).
  { intros e f He Hf Hne.
    rewrite Hedges in He, Hf.
    apply (Hnfv e f (HWD e He) (HWD f Hf) Hne).
    intro Hetf. apply (Htf f Hf). rewrite <- Hetf. exact He. }
  assert (Htaut : ring_taut r)
    by (exact (ring_taut_of_simple_and_no_foreign_vertex r Hsimple Hnfv_r)).
  assert (HsubD : forall f, In f (ring_edges r) -> In f D)
    by (intros f Hf; rewrite Hedges in Hf; exact (HWD f Hf)).
  (* ---- 2. the walk index and iterate membership ---- *)
  destruct (same_face_twin_first_step_index E d Hfan Hns HdD Hsf)
    as [k [Hkrange [Hret _]]].
  assert (Htwclos : forall x, In x D -> In (twin x) D)
    by (apply darts_of_closed_under_twin).
  assert (Hclos : forall x, In x D -> In (fstep D x) D)
    by (intros x Hx; apply fstep_in; [ exact Htwclos | exact Hx ]).
  assert (Hiter : forall i, In (iter (fstep D) i d) D)
    by (intro i; exact (iter_in (fstep D) D Hclos i d HdD)).
  assert (Htwi : forall i, (i < k)%nat -> In (twin (iter (fstep D) i d)) D)
    by (intros i _; apply Htwclos, Hiter).
  (* ---- 3a. fold the E-1 range corners over the walk ---- *)
  destruct (range_family_fold k
              (fun i delta rho =>
                 connected_in_complement_cont r
                   (point_at (dtip (iter (fstep D) i d))
                      (corner_sample_in
                         (ddir (twin (iter (fstep D) i d))) rho delta))
                   (point_at (dtip (iter (fstep D) i d))
                      (corner_sample_out
                         (ddir (fstep D (iter (fstep D) i d))) rho delta))))
    as [tC [FC [HtC [HFC Hcorners]]]].
  { intros i Hi.
    exact (walk_corner_range_at E d c (iter (fstep D) i d)
             Hfan Hns Hnh Hnfv Hnfv_r Hp Hnd Hedges HWD (Hiter i)). }
  (* ---- 3b. one global rho below every corner cap ---- *)
  set (rho := Rmin tC (1 / 3) / 2).
  assert (Hmin13 : 0 < Rmin tC (1 / 3))
    by (apply Rmin_glb_lt; lra).
  pose proof (Rmin_l tC (1 / 3)) as HminL.
  pose proof (Rmin_r tC (1 / 3)) as HminR.
  assert (Hrho : 0 < rho) by (unfold rho; lra).
  assert (Hrho_tC : rho < tC) by (unfold rho; lra).
  assert (Hrho13 : rho <= 1 / 3) by (unfold rho; lra).
  assert (Hrhosum : rho + rho < 1) by lra.
  (* ---- 3c. fold the ride caps over the walk ---- *)
  destruct (cap_family_fold k
              (fun i delta =>
                 connected_in_complement_cont r
                   (point_at (dbase (iter (fstep D) i d))
                      (corner_sample_out
                         (ddir (iter (fstep D) i d)) rho delta))
                   (point_at (dtip (iter (fstep D) i d))
                      (corner_sample_in
                         (point_diff (dbase (iter (fstep D) i d))
                                     (dtip (iter (fstep D) i d)))
                         rho delta))))
    as [capR [HcapR Hrides]].
  { intros i Hi.
    exact (walk_ride_at D r (iter (fstep D) i d) rho rho
             Htaut Hpw Hnfv (Hiter i) HsubD (Hnh _ (Hiter i))
             Hrho Hrho Hrhosum). }
  (* ---- orientation and the straddle height's span position ---- *)
  pose proof (vy_ddir d) as Hvyd.
  assert (Hnhd : py (fst d) <> py (snd d)) by (apply Hnh; exact HdD).
  assert (Hvyne : vy (ddir d) <> 0)
    by (rewrite Hvyd; unfold dtip, dbase; lra).
  set (K := vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d)).
  assert (HKeq : K = vx (ddir d) * vx (ddir d) + vy (ddir d) * vy (ddir d))
    by reflexivity.
  assert (HK : 0 < K) by nra.
  destruct Hint as [t0 [Ht0 [_ Hmyt]]].
  destruct (Rtotal_order (vy (ddir d)) 0) as [Hdesc | [Heq0 | Hasc]];
    [ | exact (False_ind _ (Hvyne Heq0)) | ].
  - (* ================= DESCENDING d ================= *)
    set (span := - vy (ddir d)).
    assert (Hspeq : span = - vy (ddir d)) by reflexivity.
    assert (Hspan : 0 < span) by lra.
    assert (Hmyspan : py (dtip d) < my < py (dbase d)).
    { change (dtip d) with (snd d). change (dbase d) with (fst d).
      unfold dtip, dbase in Hvyd. split; nra. }
    (* the two tie caps *)
    destruct (walk_tie_west_desc D r d rho my
                Htaut Hpw Hnfv HdD HsubD Hdesc Hrho Hrho13 Hmyspan)
      as [capW [HcapW Hwties]].
    destruct (walk_tie_east_desc D r d rho my
                Htaut Hpw Hnfv HdD HsubD Hdesc Hrho Hrho13 Hmyspan)
      as [capE [HcapE Heties]].
    (* the shrink-and-choose *)
    set (m1 := rho * K / (FC * span)).
    assert (Hm1 : 0 < m1)
      by (unfold m1; apply Rdiv_lt_0_compat; nra).
    set (m2 := Rmin (capR * K / span) m1).
    assert (Hm2 : 0 < m2).
    { apply Rmin_glb_lt; [ apply Rdiv_lt_0_compat; nra | exact Hm1 ]. }
    set (m3 := Rmin (tC * K / span) m2).
    assert (Hm3 : 0 < m3).
    { apply Rmin_glb_lt; [ apply Rdiv_lt_0_compat; nra | exact Hm2 ]. }
    set (m4 := Rmin capE m3).
    assert (Hm4 : 0 < m4) by (apply Rmin_glb_lt; assumption).
    set (m5 := Rmin capW m4).
    assert (Hm5 : 0 < m5) by (apply Rmin_glb_lt; assumption).
    set (m6 := Rmin ef m5).
    assert (Hm6 : 0 < m6) by (apply Rmin_glb_lt; assumption).
    set (ef' := m6 / 2).
    assert (Hef' : 0 < ef') by (unfold ef'; lra).
    pose proof (Rmin_l ef m5) as Hb_ef.
    pose proof (Rmin_r ef m5) as Hb_m5.
    pose proof (Rmin_l capW m4) as Hb_capW.
    pose proof (Rmin_r capW m4) as Hb_m4.
    pose proof (Rmin_l capE m3) as Hb_capE.
    pose proof (Rmin_r capE m3) as Hb_m3.
    pose proof (Rmin_l (tC * K / span) m2) as Hb_tC.
    pose proof (Rmin_r (tC * K / span) m2) as Hb_m2.
    pose proof (Rmin_l (capR * K / span) m1) as Hb_capR.
    pose proof (Rmin_r (capR * K / span) m1) as Hb_m1.
    fold m2 in Hb_capR, Hb_m1. fold m3 in Hb_tC, Hb_m2.
    fold m4 in Hb_capE, Hb_m3. fold m5 in Hb_capW, Hb_m4.
    fold m6 in Hb_ef, Hb_m5.
    assert (Hef'_ef : ef' <= ef) by (unfold ef'; lra).
    assert (Hef'_capW : ef' < capW) by (unfold ef'; lra).
    assert (Hef'_capE : ef' < capE) by (unfold ef'; lra).
    assert (Hef'_tC : ef' < tC * K / span) by (unfold ef'; lra).
    assert (Hef'_capR : ef' < capR * K / span) by (unfold ef'; lra).
    assert (Hef'_m1 : ef' <= rho * K / (FC * span))
      by (unfold ef', m1 in *; lra).
    (* the shared corner delta *)
    set (dc := corner_delta_for_ef_west d ef').
    assert (Hdceq : dc = ef' * span / K) by reflexivity.
    assert (Hdcpos : 0 < dc).
    { rewrite Hdceq. unfold Rdiv.
      apply Rmult_lt_0_compat; [ nra | apply Rinv_0_lt_compat; exact HK ]. }
    assert (Hdc_tC : dc < tC).
    { rewrite Hdceq. apply lt_div_scale; [ exact Hspan | exact HK | ].
      exact Hef'_tC. }
    assert (Hdc_capR : dc < capR).
    { rewrite Hdceq. apply lt_div_scale; [ exact Hspan | exact HK | ].
      exact Hef'_capR. }
    assert (Hdc_rho : FC * dc <= rho).
    { rewrite Hdceq. apply le_div_scale;
        [ exact Hspan | exact HK | exact HFC | exact Hef'_m1 ]. }
    (* the two ties at ef' *)
    pose proof (Hwties ef' (conj Hef' Hef'_capW)) as Hwest.
    pose proof (Heties ef' (conj Hef' Hef'_capE)) as Heast.
    (* the chain at the shared delta *)
    assert (Hchain :
      connected_in_complement_cont r
        (point_at (dbase d)
           (corner_sample_out (ddir d) rho dc))
        (point_at (dtip d)
           (corner_sample_out (ddir (twin d)) rho dc))).
    { apply (walk_chain_to_twin r D d k
               (fun _ => rho) (fun _ => rho) dc Hret).
      - exact (connected_in_complement_cont_left r _ _ Hwest).
      - exact Htwi.
      - intros i Hi. exact (Hrides i Hi dc (conj Hdcpos Hdc_capR)).
      - intros i Hi.
        exact (Hcorners i Hi dc rho (conj Hdcpos Hdc_tC) Hdc_rho Hrho_tC). }
    (* assembly *)
    exists ef'.
    split; [ exact Hef' | split; [ exact Hef'_ef | ] ].
    apply connected_in_complement_cont_trans
      with (point_at (dbase d) (corner_sample_out (ddir d) rho dc)).
    { apply connected_in_complement_cont_sym. exact Hwest. }
    apply connected_in_complement_cont_trans
      with (point_at (dtip d) (corner_sample_out (ddir (twin d)) rho dc)).
    { exact Hchain. }
    exact Heast.
  - (* ================= ASCENDING d ================= *)
    set (span := vy (ddir d)).
    assert (Hspeq : span = vy (ddir d)) by reflexivity.
    assert (Hspan : 0 < span) by lra.
    assert (Hmyspan : py (dbase d) < my < py (dtip d)).
    { change (dtip d) with (snd d). change (dbase d) with (fst d).
      unfold dtip, dbase in Hvyd. split; nra. }
    destruct (walk_tie_east_asc D r d rho my
                Htaut Hpw Hnfv HdD HsubD Hasc Hrho Hrho13 Hmyspan)
      as [capE [HcapE Heties]].
    destruct (walk_tie_west_asc D r d rho my
                Htaut Hpw Hnfv HdD HsubD Hasc Hrho Hrho13 Hmyspan)
      as [capW [HcapW Hwties]].
    set (m1 := rho * K / (FC * span)).
    assert (Hm1 : 0 < m1)
      by (unfold m1; apply Rdiv_lt_0_compat; nra).
    set (m2 := Rmin (capR * K / span) m1).
    assert (Hm2 : 0 < m2).
    { apply Rmin_glb_lt; [ apply Rdiv_lt_0_compat; nra | exact Hm1 ]. }
    set (m3 := Rmin (tC * K / span) m2).
    assert (Hm3 : 0 < m3).
    { apply Rmin_glb_lt; [ apply Rdiv_lt_0_compat; nra | exact Hm2 ]. }
    set (m4 := Rmin capE m3).
    assert (Hm4 : 0 < m4) by (apply Rmin_glb_lt; assumption).
    set (m5 := Rmin capW m4).
    assert (Hm5 : 0 < m5) by (apply Rmin_glb_lt; assumption).
    set (m6 := Rmin ef m5).
    assert (Hm6 : 0 < m6) by (apply Rmin_glb_lt; assumption).
    set (ef' := m6 / 2).
    assert (Hef' : 0 < ef') by (unfold ef'; lra).
    pose proof (Rmin_l ef m5) as Hb_ef.
    pose proof (Rmin_r ef m5) as Hb_m5.
    pose proof (Rmin_l capW m4) as Hb_capW.
    pose proof (Rmin_r capW m4) as Hb_m4.
    pose proof (Rmin_l capE m3) as Hb_capE.
    pose proof (Rmin_r capE m3) as Hb_m3.
    pose proof (Rmin_l (tC * K / span) m2) as Hb_tC.
    pose proof (Rmin_r (tC * K / span) m2) as Hb_m2.
    pose proof (Rmin_l (capR * K / span) m1) as Hb_capR.
    pose proof (Rmin_r (capR * K / span) m1) as Hb_m1.
    fold m2 in Hb_capR, Hb_m1. fold m3 in Hb_tC, Hb_m2.
    fold m4 in Hb_capE, Hb_m3. fold m5 in Hb_capW, Hb_m4.
    fold m6 in Hb_ef, Hb_m5.
    assert (Hef'_ef : ef' <= ef) by (unfold ef'; lra).
    assert (Hef'_capW : ef' < capW) by (unfold ef'; lra).
    assert (Hef'_capE : ef' < capE) by (unfold ef'; lra).
    assert (Hef'_tC : ef' < tC * K / span) by (unfold ef'; lra).
    assert (Hef'_capR : ef' < capR * K / span) by (unfold ef'; lra).
    assert (Hef'_m1 : ef' <= rho * K / (FC * span))
      by (unfold ef', m1 in *; lra).
    set (dc := corner_delta_for_ef_east d ef').
    assert (Hdceq : dc = ef' * span / K) by reflexivity.
    assert (Hdcpos : 0 < dc).
    { rewrite Hdceq. unfold Rdiv.
      apply Rmult_lt_0_compat; [ nra | apply Rinv_0_lt_compat; exact HK ]. }
    assert (Hdc_tC : dc < tC).
    { rewrite Hdceq. apply lt_div_scale; [ exact Hspan | exact HK | ].
      exact Hef'_tC. }
    assert (Hdc_capR : dc < capR).
    { rewrite Hdceq. apply lt_div_scale; [ exact Hspan | exact HK | ].
      exact Hef'_capR. }
    assert (Hdc_rho : FC * dc <= rho).
    { rewrite Hdceq. apply le_div_scale;
        [ exact Hspan | exact HK | exact HFC | exact Hef'_m1 ]. }
    pose proof (Heties ef' (conj Hef' Hef'_capE)) as Heast.
    pose proof (Hwties ef' (conj Hef' Hef'_capW)) as Hwest.
    assert (Hchain :
      connected_in_complement_cont r
        (point_at (dbase d)
           (corner_sample_out (ddir d) rho dc))
        (point_at (dtip d)
           (corner_sample_out (ddir (twin d)) rho dc))).
    { apply (walk_chain_to_twin r D d k
               (fun _ => rho) (fun _ => rho) dc Hret).
      - exact (connected_in_complement_cont_left r _ _ Heast).
      - exact Htwi.
      - intros i Hi. exact (Hrides i Hi dc (conj Hdcpos Hdc_capR)).
      - intros i Hi.
        exact (Hcorners i Hi dc rho (conj Hdcpos Hdc_tC) Hdc_rho Hrho_tC). }
    exists ef'.
    split; [ exact Hef' | split; [ exact Hef'_ef | ] ].
    apply connected_in_complement_cont_trans
      with (point_at (dtip d) (corner_sample_out (ddir (twin d)) rho dc)).
    { apply connected_in_complement_cont_sym. exact Hwest. }
    apply connected_in_complement_cont_trans
      with (point_at (dbase d) (corner_sample_out (ddir d) rho dc)).
    { apply connected_in_complement_cont_sym. exact Hchain. }
    exact Heast.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The transport premise and the H-bridge premise are THEOREMS.            *)
(* -------------------------------------------------------------------------- *)

Corollary face_transport_premise_holds :
  forall E : list Edge,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    pairwise_no_proper_cross_twin_aware (darts_of E) ->
    no_horizontal_darts (darts_of E) ->
    no_foreign_vertex_twin_aware (darts_of E) ->
    face_transport_premise E.
Proof.
  intros E Hfan Hns Hpw Hnh Hnfv.
  apply face_transport_premise_of_walk_connectivity; [ exact Hnh | ].
  apply walk_small_offset_connectivity_holds; assumption.
Qed.

Corollary H_bridge_premise_holds :
  forall E : list Edge,
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    no_spurs (darts_of E) ->
    pairwise_no_proper_cross_twin_aware (darts_of E) ->
    no_horizontal_darts (darts_of E) ->
    no_foreign_vertex_twin_aware (darts_of E) ->
    H_bridge_premise E.
Proof.
  intros E Hfan Hns Hpw Hnh Hnfv.
  apply H_bridge_premise_of_transport; try assumption.
  apply face_transport_premise_holds; assumption.
Qed.

(* One-shot packaging of the two-step idiom every `_of_guards` call site was
   re-deriving inline (`well_noded_fan_ok` to get the per-vertex fan, then
   `H_bridge_premise_holds` to get the bridge premise, then
   `EdgeFaceBridge.H_bridge_well_noded` to land on the single hypothesis
   `extract_faces_valid_sep` / `extract_faces_holes_valid_sep` actually want):
   from the six standing guards straight to `twins_in_different_faces`. *)
Corollary twins_in_different_faces_of_guards :
  forall E : list Edge,
    well_noded_darts E ->
    no_spurs (darts_of E) ->
    edge_2_connected E ->
    pairwise_no_proper_cross_twin_aware (darts_of E) ->
    no_horizontal_darts (darts_of E) ->
    no_foreign_vertex_twin_aware (darts_of E) ->
    twins_in_different_faces (darts_of E).
Proof.
  intros E Hwn Hns H2ec Hpw Hnh Hnfv.
  apply (H_bridge_well_noded E
           (H_bridge_premise_holds E (well_noded_fan_ok E Hwn) Hns Hpw Hnh Hnfv)
           Hwn Hns H2ec).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  The residual discharge; allowlist axioms only.                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions walk_small_offset_connectivity_holds.
Print Assumptions face_transport_premise_holds.
Print Assumptions H_bridge_premise_holds.
Print Assumptions twins_in_different_faces_of_guards.
