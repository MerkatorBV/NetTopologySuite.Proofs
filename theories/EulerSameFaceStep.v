(* ==========================================================================
   EulerSameFaceStep.v

   [H-bridge / Euler campaign, rung E-3a] THE CORE INDUCTION STEP OF THE
   UNCONDITIONAL EULER FORMULA: deleting ANY edge of a min-degree->=2
   arrangement transfers `euler_characteristic` -- with the branch chosen
   by the DECIDABLE `same_face` test, and the bridge branch's cut fact
   supplied by the now-Euler-free `H_bridge_premise_holds` (E-2c).

   This is exactly the dispatch `EulerFormula.v`'s header names as "the
   genuinely hard, planar-content" gap: previously the per-edge delta
   had to be supplied externally (via Euler itself -- the circularity);
   with the H-bridge campaign closed, `same_face (darts_of E) d (twin
   d)` alone decides it:

     - SAME FACE  => `d` is a cut edge (`H_bridge_premise_holds`):
       Delta V = 0 (both endpoints survive by min-degree->=2),
       Delta E = -1, Delta F = +1 (`num_faces_E_minus_splice`),
       Delta C = +1 (`bridge_components_split`)   -- `euler_transfer_bridge`;
     - DIFFERENT FACES => the rest of `d`'s face walk is a bypass
       (`diff_face_bypass_E_minus`, Euler-free):
       Delta V = 0, Delta E = -1,
       Delta F = -1 (`num_faces_E_minus_merge`),
       Delta C = 0 (`cycle_components_eq`)        -- `euler_transfer_cycle`.

   Support kit, all from min-degree->=2 + NoDup/no_twin_dup:
     - `outgoing_second`: a degree->=2 fan has a second dart distinct
       from any given one (NoDup of `darts_of` makes the length honest);
     - `no_spurs_of_min_degree_2`: a spur forces a singleton fan at the
       tip (`next_neq_self_of_other` refutes it with the second dart);
     - `base_endpoint_survives` / `tip_endpoint_survives`: the second
       dart's carrier edge is not `d`, so each endpoint stays a vertex
       of `E_minus E d`;
     - `num_vertices_E_minus_eq_of_survivors`: Delta V = 0 outright;
     - `same_face_twin_dec`: membership of `twin d` in the period walk
       decides `same_face` (both directions already banked).

   The remaining E-3 work (E-3b) is the well-founded wrapper: peel to
   the degree core (`euler_core_reduction`), apply this step, recurse.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals List Arith Lia Bool.
From NTS.Proofs Require Import Distance Overlay OverlayGraph EdgeConnectivity
                               Dart DartNext DartNextSpec DartFace
                               NoShortFaces FaceChain ExtractFaces
                               FaceOrbitSep EdgeFaceBridge MinDegreeCore
                               EulerArrangement MapCounts ReachableDec
                               EulerBridge ClassCount ArrangementEMinus
                               EulerCoreInduction NumFacesSplice
                               NumFacesMerge EulerFormula FaceTwinAware
                               HBridgeCoreSlice WalkPremiseBridge
                               WalkResidualDischarge.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  A degree->=2 fan has a second dart.                                     *)
(* -------------------------------------------------------------------------- *)

Lemma outgoing_second :
  forall (v : Point) (D : list Dart) (x : Dart),
    NoDup D -> (2 <= vdeg v D)%nat ->
    exists y, In y (outgoing v D) /\ y <> x.
Proof.
  intros v D x HndD Hdeg.
  assert (Hnd : NoDup (outgoing v D)) by (apply NoDup_filter; exact HndD).
  unfold vdeg in Hdeg.
  destruct (outgoing v D) as [| a [| b l']] eqn:Hout;
    cbn [length] in Hdeg; try lia.
  inversion Hnd as [| ? ? Hna Hnd']; subst.
  destruct (edge_eq_dec a x) as [-> | Hax].
  - exists b. split; [ right; left; reflexivity | ].
    intro Hbx. apply Hna. rewrite Hbx. left. reflexivity.
  - exists a. split; [ left; reflexivity | exact Hax ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Min-degree->=2 kills spurs.                                             *)
(* -------------------------------------------------------------------------- *)

Lemma no_spurs_of_min_degree_2 :
  forall E : list Edge,
    NoDup E -> no_twin_dup E ->
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    min_degree_2 E ->
    no_spurs (darts_of E).
Proof.
  intros E Hnd Hntd Hfan Hmin d Hd Hspur.
  (* the tip is a genuine vertex of E *)
  assert (Hverts : In (dtip d) (verts E)).
  { destruct (dart_carrier_edge E d Hd) as [ec [HecE Hcase]].
    apply in_verts. exists ec. split; [ exact HecE | ].
    destruct Hcase as [-> | ->].
    - right. reflexivity.
    - left. rewrite dbase_twin in *. reflexivity. }
  pose proof (Hmin (dtip d) Hverts) as Hdeg.
  assert (Htw : In (twin d) (outgoing (dtip d) (darts_of E))).
  { apply in_outgoing.
    split; [ apply darts_of_closed_under_twin; exact Hd | apply dbase_twin ]. }
  destruct (outgoing_second (dtip d) (darts_of E) (twin d)
              (darts_of_NoDup E Hnd Hntd) Hdeg) as [y [HyF Hyx]].
  unfold fstep in Hspur.
  exact (next_neq_self_of_other (outgoing (dtip d) (darts_of E)) (twin d) y
           (Hfan (dtip d)) Htw HyF Hyx Hspur).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Both endpoints survive deletion under min-degree->=2.                   *)
(* -------------------------------------------------------------------------- *)

Lemma base_endpoint_survives :
  forall (E : list Edge) (d : Edge),
    NoDup E -> no_twin_dup E -> In d E -> dbase d <> dtip d ->
    min_degree_2 E ->
    In (fst d) (verts (E_minus E d)).
Proof.
  intros E d Hnd Hntd HdE Hproper Hmin.
  assert (HdD : In d (darts_of E)) by (apply in_darts_of_orig; exact HdE).
  assert (HaV : In (fst d) (verts E))
    by (apply in_verts; exists d; split; [ exact HdE | left; reflexivity ]).
  pose proof (Hmin (fst d) HaV) as Hdeg.
  destruct (outgoing_second (fst d) (darts_of E) d
              (darts_of_NoDup E Hnd Hntd) Hdeg) as [y [HyF Hyd]].
  apply in_outgoing in HyF. destruct HyF as [HyD Hybase].
  assert (Hytw : y <> twin d).
  { intro He. subst y. rewrite dbase_twin in Hybase.
    exact (Hproper (eq_sym Hybase)). }
  destruct (dart_carrier_edge E y HyD) as [ec [HecE Hcase]].
  assert (Hecd : ec <> d).
  { intro He. subst ec.
    destruct Hcase as [Hc | Hc].
    - exact (Hyd (eq_sym Hc)).
    - apply Hytw. rewrite Hc, twin_involutive. reflexivity. }
  apply in_verts. exists ec.
  split; [ apply in_E_minus; split; assumption | ].
  destruct Hcase as [-> | ->].
  - left. exact Hybase.
  - right. unfold twin. cbn [snd]. exact Hybase.
Qed.

Lemma tip_endpoint_survives :
  forall (E : list Edge) (d : Edge),
    NoDup E -> no_twin_dup E -> In d E -> dbase d <> dtip d ->
    min_degree_2 E ->
    In (snd d) (verts (E_minus E d)).
Proof.
  intros E d Hnd Hntd HdE Hproper Hmin.
  assert (HdD : In d (darts_of E)) by (apply in_darts_of_orig; exact HdE).
  assert (HbV : In (snd d) (verts E))
    by (apply in_verts; exists d; split; [ exact HdE | right; reflexivity ]).
  pose proof (Hmin (snd d) HbV) as Hdeg.
  destruct (outgoing_second (snd d) (darts_of E) (twin d)
              (darts_of_NoDup E Hnd Hntd) Hdeg) as [y [HyF Hytw]].
  apply in_outgoing in HyF. destruct HyF as [HyD Hybase].
  assert (Hyd : y <> d).
  { intro He. subst y. exact (Hproper Hybase). }
  destruct (dart_carrier_edge E y HyD) as [ec [HecE Hcase]].
  assert (Hecd : ec <> d).
  { intro He. subst ec.
    destruct Hcase as [Hc | Hc].
    - exact (Hyd (eq_sym Hc)).
    - apply Hytw. rewrite Hc, twin_involutive. reflexivity. }
  apply in_verts. exists ec.
  split; [ apply in_E_minus; split; assumption | ].
  destruct Hcase as [-> | ->].
  - left. exact Hybase.
  - right. unfold twin. cbn [snd]. exact Hybase.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Delta V = 0 from the two survivors.                                     *)
(* -------------------------------------------------------------------------- *)

Lemma num_vertices_E_minus_eq_of_survivors :
  forall (E : list Edge) (d : Edge),
    In (fst d) (verts (E_minus E d)) ->
    In (snd d) (verts (E_minus E d)) ->
    num_vertices (E_minus E d) = num_vertices E.
Proof.
  intros E d Ha Hb.
  assert (Hincl1 : incl (verts E) (verts (E_minus E d)))
    by (apply verts_incl_E_of_survivors; assumption).
  assert (Hincl2 : incl (verts (E_minus E d)) (verts E))
    by apply verts_E_minus_incl.
  unfold num_vertices.
  apply Nat.le_antisymm.
  - apply NoDup_incl_length; [ apply NoDup_nodup | ].
    intros p Hp. apply nodup_In in Hp. apply nodup_In.
    apply Hincl2. exact Hp.
  - apply NoDup_incl_length; [ apply NoDup_nodup | ].
    intros p Hp. apply nodup_In in Hp. apply nodup_In.
    apply Hincl1. exact Hp.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  `same_face d (twin d)` is decidable.                                    *)
(* -------------------------------------------------------------------------- *)

Lemma same_face_twin_dec :
  forall (E : list Edge) (d : Dart),
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    In d (darts_of E) ->
    {same_face (darts_of E) d (twin d)} +
    {~ same_face (darts_of E) d (twin d)}.
Proof.
  intros E d Hfan Hd.
  destruct (in_dec edge_eq_dec (twin d)
              (dart_walk (darts_of E) d (face_period (darts_of E) d)))
    as [Hin | Hnin].
  - left. apply dart_walk_iter_iff in Hin.
    destruct Hin as [k [_ Hk]]. exists k. exact Hk.
  - right. intro Hsf. apply Hnin.
    exact (same_face_twin_in_period_walk E d Hfan Hd Hsf).
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Headline: the core induction step.                                      *)
(* -------------------------------------------------------------------------- *)

Theorem euler_characteristic_core_edge_transfer :
  forall (E : list Edge) (d : Edge),
    NoDup E -> no_twin_dup E ->
    (forall v : Point, fan_ok (outgoing v (darts_of E))) ->
    min_degree_2 E ->
    pairwise_no_proper_cross_twin_aware (darts_of E) ->
    no_horizontal_darts (darts_of E) ->
    no_foreign_vertex_twin_aware (darts_of E) ->
    In d E ->
    (euler_characteristic E <-> euler_characteristic (E_minus E d)).
Proof.
  intros E d Hnd Hntd Hfan Hmin Hpw Hnh Hnfv HdE.
  assert (HdD : In d (darts_of E)) by (apply in_darts_of_orig; exact HdE).
  assert (Hproper : dbase d <> dtip d).
  { apply dart_endpoints_ne_of_proper.
    exact (dart_proper_of_fan (darts_of E) d HdD Hfan). }
  assert (Hntwin : ~ In (twin d) E) by (apply Hntd; exact HdE).
  assert (Hns : no_spurs (darts_of E))
    by (apply no_spurs_of_min_degree_2; assumption).
  assert (Ha : In (fst d) (verts (E_minus E d)))
    by (apply base_endpoint_survives; assumption).
  assert (Hb : In (snd d) (verts (E_minus E d)))
    by (apply tip_endpoint_survives; assumption).
  assert (HV : num_vertices (E_minus E d) = num_vertices E)
    by (apply num_vertices_E_minus_eq_of_survivors; assumption).
  assert (HE : (num_edges (E_minus E d) + 1 = num_edges E)%nat)
    by (apply num_edges_E_minus, count_occ_1_of_NoDup; assumption).
  assert (Hfstne : fst d <> snd d) by exact Hproper.
  destruct (same_face_twin_dec E d Hfan HdD) as [Hsf | Hnsf].
  - (* BRIDGE: same face => cut edge (Euler-free, E-2c) *)
    assert (Hcut : ~ reachable (E_minus E d) (fst d) (snd d)).
    { pose proof (H_bridge_premise_holds E Hfan Hns Hpw Hnh Hnfv) as Hbr.
      intro Hreach.
      exact (proj1 (Hbr d HdD Hsf Hproper) HdE Hntwin
               (reach_sym _ _ _ Hreach)). }
    apply euler_transfer_bridge.
    + exact HV.
    + exact HE.
    + exact (num_faces_E_minus_splice E d Hfan Hns HdE Hntwin Hproper Hsf).
    + exact (bridge_components_split E d HdE Hfstne Ha Hb Hcut).
  - (* CYCLE: different faces => the face walk is a bypass (Euler-free) *)
    assert (Hby : reachable (E_minus E d) (fst d) (snd d)).
    { apply reach_sym.
      apply (diff_face_bypass_E_minus E d d Hfan Hns HdD Hnsf HdE).
      left. reflexivity. }
    assert (HFm : num_faces (E_minus E d) = (num_faces E - 1)%nat)
      by (exact (num_faces_E_minus_merge E d Hfan
                   (all_proper_darts_of_fan (darts_of E) Hfan)
                   Hns HdE Hntwin Hproper Hnsf)).
    assert (Hpos : (1 <= num_faces E)%nat).
    { apply num_faces_pos; [ exact Hfan | ].
      intro Hc. rewrite Hc in HdD. destruct HdD. }
    apply euler_transfer_cycle.
    + exact HV.
    + exact HE.
    + lia.
    + exact (cycle_components_eq E d Hfstne Hby).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Same-face dispatch step; allowlist axioms only.               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions no_spurs_of_min_degree_2.
Print Assumptions same_face_twin_dec.
Print Assumptions euler_characteristic_core_edge_transfer.
