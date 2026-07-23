(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgePairNoding
   ----------------------------------------------------------------------------
   Track 2 brick 12: mutual pair noding under dual proper-cross.

   Brick 11 filters a host edge's cuts so each node is interior on *both*
   closed segments.  A real noder still needs the dual-edge payoff: when
   AB dual-proper-crosses CD, the *same* geometric point is an interior
   node on CD as well, and both one-edge pipelines are sound.

   This module:

     - packages a pair of integer edges as mutual `ZCut`s
     - proves `dual_proper_cut` is symmetric under host/cut swap
     - reconstructs the shared geometric point from either edge's `EPos`
     - runs the single-edge noder contract on *both* hosts

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok
   ========================================================================== *)

From Stdlib Require Import ZArith Lia Reals Lra List.
From Stdlib Require Import Sorting.Sorted.
From NTS.Proofs Require Import Distance Orientation Segment
                               RelateIntDetBound RelateEdgePosOrder
                               RelateEdgePosSort RelateEdgeInterParam
                               RelateEdgeInterClip RelateEdgePosMerge
                               RelateEdgeSplit RelateEdgeSplitAdj
                               RelateEdgeNoding RelateEdgeNode
                               RelateEdgeMultiNode RelateBoundary
                               RelateEdgeDualCross.

Local Open Scope Z_scope.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Pair packaging and dual-proper symmetry.                               *)
(* -------------------------------------------------------------------------- *)

Definition zcut (x0 y0 x1 y1 : Z) : ZCut :=
  {| c0x := x0; c0y := y0; c1x := x1; c1y := y1 |}.

(* Mutual dual-proper: both idet-products negative (order-independent form). *)
Definition dual_proper_pair
  (ax ay bx by_ cx cy dx dy : Z) : Prop :=
  dual_proper_cut ax ay bx by_ (zcut cx cy dx dy).

Lemma dual_proper_pair_products :
  forall ax ay bx by_ cx cy dx dy,
    dual_proper_pair ax ay bx by_ cx cy dx dy ->
    idet cx cy dx dy ax ay * idet cx cy dx dy bx by_ < 0 /\
    idet ax ay bx by_ cx cy * idet ax ay bx by_ dx dy < 0.
Proof.
  intros ax ay bx by_ cx cy dx dy [Hcut Hhost].
  unfold proper_cut, cut_product, host_product in Hcut, Hhost.
  simpl in Hcut, Hhost.
  split; [exact Hcut | exact Hhost].
Qed.

(* HEADLINE: dual-proper is symmetric under host ↔ cut swap. *)
Theorem dual_proper_cut_sym :
  forall ax ay bx by_ cx cy dx dy,
    dual_proper_cut ax ay bx by_ (zcut cx cy dx dy) ->
    dual_proper_cut cx cy dx dy (zcut ax ay bx by_).
Proof.
  intros ax ay bx by_ cx cy dx dy [Hcut Hhost].
  unfold dual_proper_cut, proper_cut, cut_product, host_product in *.
  simpl in *.
  split; [exact Hhost | exact Hcut].
Qed.

Theorem dual_proper_pair_sym :
  forall ax ay bx by_ cx cy dx dy,
    dual_proper_pair ax ay bx by_ cx cy dx dy ->
    dual_proper_pair cx cy dx dy ax ay bx by_.
Proof.
  intros ax ay bx by_ cx cy dx dy H.
  unfold dual_proper_pair in *.
  exact (dual_proper_cut_sym ax ay bx by_ cx cy dx dy H).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Shared geometric node from either host's EPos.                         *)
(* -------------------------------------------------------------------------- *)

Lemma between_strict_implies_between :
  forall P0 P1 Q, between_strict P0 P1 Q -> between P0 P1 Q.
Proof.
  intros P0 P1 Q [t [[Ht0 Ht1] [Hx Hy]]].
  exists t. repeat split; try lra; assumption.
Qed.

(* Node on host A–B from dual-proper cut C–D. *)
Definition epos_ab_of_dual
  (ax ay bx by_ cx cy dx dy : Z)
  (H : dual_proper_pair ax ay bx by_ cx cy dx dy) : EPos :=
  let Hcut := proj1 (dual_proper_pair_products ax ay bx by_ cx cy dx dy H) in
  epos_of_proper_cross ax ay bx by_ cx cy dx dy Hcut.

(* Node on host C–D from dual-proper cut A–B. *)
Definition epos_cd_of_dual
  (ax ay bx by_ cx cy dx dy : Z)
  (H : dual_proper_pair ax ay bx by_ cx cy dx dy) : EPos :=
  let Hhost := proj2 (dual_proper_pair_products ax ay bx by_ cx cy dx dy H) in
  epos_of_proper_cross cx cy dx dy ax ay bx by_ Hhost.

Lemma epos_ab_of_dual_interior :
  forall ax ay bx by_ cx cy dx dy
    (H : dual_proper_pair ax ay bx by_ cx cy dx dy),
    epos_interior (epos_ab_of_dual ax ay bx by_ cx cy dx dy H).
Proof.
  intros ax ay bx by_ cx cy dx dy H.
  unfold epos_ab_of_dual.
  apply epos_of_proper_cross_interior.
Qed.

Lemma epos_cd_of_dual_interior :
  forall ax ay bx by_ cx cy dx dy
    (H : dual_proper_pair ax ay bx by_ cx cy dx dy),
    epos_interior (epos_cd_of_dual ax ay bx by_ cx cy dx dy H).
Proof.
  intros ax ay bx by_ cx cy dx dy H.
  unfold epos_cd_of_dual.
  apply epos_of_proper_cross_interior.
Qed.

Lemma epos_ab_of_dual_epval :
  forall ax ay bx by_ cx cy dx dy
    (H : dual_proper_pair ax ay bx by_ cx cy dx dy),
    (epval (epos_ab_of_dual ax ay bx by_ cx cy dx dy H)
     = inter_param (ptZ ax ay) (ptZ bx by_)
         (ptZ cx cy) (ptZ dx dy))%R.
Proof.
  intros. unfold epos_ab_of_dual. apply epos_of_proper_cross_epval.
Qed.

Lemma epos_cd_of_dual_epval :
  forall ax ay bx by_ cx cy dx dy
    (H : dual_proper_pair ax ay bx by_ cx cy dx dy),
    (epval (epos_cd_of_dual ax ay bx by_ cx cy dx dy H)
     = inter_param (ptZ cx cy) (ptZ dx dy)
         (ptZ ax ay) (ptZ bx by_))%R.
Proof.
  intros. unfold epos_cd_of_dual. apply epos_of_proper_cross_epval.
Qed.

(* HEADLINE: both hosts reconstruct the same real intersection point. *)
Theorem dual_proper_shared_point :
  forall ax ay bx by_ cx cy dx dy
    (H : dual_proper_pair ax ay bx by_ cx cy dx dy),
    lerp (ptZ ax ay) (ptZ bx by_)
      (epval (epos_ab_of_dual ax ay bx by_ cx cy dx dy H))
    = lerp (ptZ cx cy) (ptZ dx dy)
        (epval (epos_cd_of_dual ax ay bx by_ cx cy dx dy H)).
Proof.
  intros ax ay bx by_ cx cy dx dy H.
  rewrite epos_ab_of_dual_epval, epos_cd_of_dual_epval.
  destruct (dual_proper_pair_products ax ay bx by_ cx cy dx dy H)
    as [Hcut Hhost].
  (* P := lerp on A–B is interior on both segments. *)
  pose proof (inter_param_proper_node_of_idet ax ay bx by_ cx cy dx dy
                Hhost Hcut) as [Hab Hcd].
  set (P := lerp (ptZ ax ay) (ptZ bx by_)
              (inter_param (ptZ ax ay) (ptZ bx by_)
                 (ptZ cx cy) (ptZ dx dy))).
  change (P = lerp (ptZ cx cy) (ptZ dx dy)
                 (inter_param (ptZ cx cy) (ptZ dx dy)
                    (ptZ ax ay) (ptZ bx by_))).
  (* Convert open membership to closed for uniqueness. *)
  assert (HbetAB : between (ptZ ax ay) (ptZ bx by_) P).
  { apply between_strict_implies_between. exact Hab. }
  assert (HbetCD : between (ptZ cx cy) (ptZ dx dy) P).
  { apply between_strict_implies_between. exact Hcd. }
  (* Uniqueness on host C–D cut by A–B: any shared point is the CD-param node. *)
  pose proof (inter_param_unique_node
                (ptZ cx cy) (ptZ dx dy) (ptZ ax ay) (ptZ bx by_) P) as Hu.
  (* Need R-cross products from idet products. *)
  assert (Hprod_host :
            (cross (ptZ cx cy) (ptZ dx dy) (ptZ ax ay)
             * cross (ptZ cx cy) (ptZ dx dy) (ptZ bx by_) < 0)%R).
  { rewrite cross_ptZ_product_is_idet_product.
    assert (Hr : (IZR (idet cx cy dx dy ax ay * idet cx cy dx dy bx by_)
                    < IZR 0)%R) by (apply IZR_lt; exact Hcut).
    change (IZR 0) with 0%R in Hr. exact Hr. }
  assert (Hprod_cut :
            (cross (ptZ ax ay) (ptZ bx by_) (ptZ cx cy)
             * cross (ptZ ax ay) (ptZ bx by_) (ptZ dx dy) < 0)%R).
  { rewrite (cross_ptZ_is_idet ax ay bx by_ cx cy).
    rewrite (cross_ptZ_is_idet ax ay bx by_ dx dy).
    rewrite <- mult_IZR.
    assert (Hr : (IZR (idet ax ay bx by_ cx cy * idet ax ay bx by_ dx dy)
                    < IZR 0)%R) by (apply IZR_lt; exact Hhost).
    change (IZR 0) with 0%R in Hr. exact Hr. }
  specialize (Hu Hprod_host Hprod_cut HbetCD HbetAB).
  exact Hu.
Qed.

(* Both EPos nodes are open-interior on their own hosts and the dual segment. *)
Theorem dual_proper_pair_nodes_on_both :
  forall ax ay bx by_ cx cy dx dy
    (H : dual_proper_pair ax ay bx by_ cx cy dx dy),
    let P := lerp (ptZ ax ay) (ptZ bx by_)
               (epval (epos_ab_of_dual ax ay bx by_ cx cy dx dy H)) in
    between_strict (ptZ ax ay) (ptZ bx by_) P /\
    between_strict (ptZ cx cy) (ptZ dx dy) P /\
    epos_interior (epos_ab_of_dual ax ay bx by_ cx cy dx dy H) /\
    epos_interior (epos_cd_of_dual ax ay bx by_ cx cy dx dy H).
Proof.
  intros ax ay bx by_ cx cy dx dy H.
  set (P := lerp (ptZ ax ay) (ptZ bx by_)
              (epval (epos_ab_of_dual ax ay bx by_ cx cy dx dy H))).
  (* Align P with inter_param form used by the geometry lemma. *)
  assert (Hep : P =
    lerp (ptZ ax ay) (ptZ bx by_)
      (inter_param (ptZ ax ay) (ptZ bx by_)
         (ptZ cx cy) (ptZ dx dy))).
  { unfold P. rewrite epos_ab_of_dual_epval. reflexivity. }
  destruct (dual_proper_pair_products ax ay bx by_ cx cy dx dy H)
    as [Hcut Hhost].
  pose proof (inter_param_proper_node_of_idet ax ay bx by_ cx cy dx dy
                Hhost Hcut) as [Hab Hcd].
  rewrite <- Hep in Hab, Hcd.
  split; [exact Hab |].
  split; [exact Hcd |].
  split.
  - apply epos_ab_of_dual_interior.
  - apply epos_cd_of_dual_interior.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Both hosts feed the single-edge noding pipeline.                       *)
(* -------------------------------------------------------------------------- *)

(* HEADLINE: dual-proper pair → sound one-node noding on *both* edges. *)
Theorem edge_pair_noding_of_dual :
  forall ax ay bx by_ cx cy dx dy
    (H : dual_proper_pair ax ay bx by_ cx cy dx dy),
    let pab := epos_ab_of_dual ax ay bx by_ cx cy dx dy H in
    let pcd := epos_cd_of_dual ax ay bx by_ cx cy dx dy H in
    (* Host A–B *)
    all_epos_interior [pab] /\
    Sorted eple [pab] /\
    (forall X,
       between (ptZ ax ay) (ptZ bx by_) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs
              (edge_params (noded_edge_params [pab]))) /\
         between (lerp (ptZ ax ay) (ptZ bx by_) t0)
                 (lerp (ptZ ax ay) (ptZ bx by_) t1) X) /\
    (forall t0 t1 t2 X,
       In (t0, t1)
         (consecutive_pairs (edge_params (noded_edge_params [pab]))) ->
       In (t1, t2)
         (consecutive_pairs (edge_params (noded_edge_params [pab]))) ->
       between (lerp (ptZ ax ay) (ptZ bx by_) t0)
               (lerp (ptZ ax ay) (ptZ bx by_) t1) X ->
       between (lerp (ptZ ax ay) (ptZ bx by_) t1)
               (lerp (ptZ ax ay) (ptZ bx by_) t2) X ->
       X = lerp (ptZ ax ay) (ptZ bx by_) t1) /\
    (* Host C–D *)
    all_epos_interior [pcd] /\
    Sorted eple [pcd] /\
    (forall X,
       between (ptZ cx cy) (ptZ dx dy) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs
              (edge_params (noded_edge_params [pcd]))) /\
         between (lerp (ptZ cx cy) (ptZ dx dy) t0)
                 (lerp (ptZ cx cy) (ptZ dx dy) t1) X) /\
    (forall t0 t1 t2 X,
       In (t0, t1)
         (consecutive_pairs (edge_params (noded_edge_params [pcd]))) ->
       In (t1, t2)
         (consecutive_pairs (edge_params (noded_edge_params [pcd]))) ->
       between (lerp (ptZ cx cy) (ptZ dx dy) t0)
               (lerp (ptZ cx cy) (ptZ dx dy) t1) X ->
       between (lerp (ptZ cx cy) (ptZ dx dy) t1)
               (lerp (ptZ cx cy) (ptZ dx dy) t2) X ->
       X = lerp (ptZ cx cy) (ptZ dx dy) t1).
Proof.
  intros ax ay bx by_ cx cy dx dy H.
  set (pab := epos_ab_of_dual ax ay bx by_ cx cy dx dy H).
  set (pcd := epos_cd_of_dual ax ay bx by_ cx cy dx dy H).
  (* Feed both singleton nodes into the brick-8 pipeline directly. *)
  assert (HintAB : epos_interior pab) by (apply epos_ab_of_dual_interior).
  assert (HintCD : epos_interior pcd) by (apply epos_cd_of_dual_interior).
  assert (HallAB : all_epos_interior [pab])
    by (apply all_epos_interior_singleton; exact HintAB).
  assert (HallCD : all_epos_interior [pcd])
    by (apply all_epos_interior_singleton; exact HintCD).
  assert (HsAB : Sorted eple [pab]) by apply Sorted_eple_singleton.
  assert (HsCD : Sorted eple [pcd]) by apply Sorted_eple_singleton.
  split; [exact HallAB |].
  split; [exact HsAB |].
  pose proof (edge_noding_sound (ptZ ax ay) (ptZ bx by_) [pab] HallAB HsAB)
    as [HabCov HabMeet].
  split; [exact HabCov |].
  split; [exact HabMeet |].
  split; [exact HallCD |].
  split; [exact HsCD |].
  pose proof (edge_noding_sound (ptZ cx cy) (ptZ dx dy) [pcd] HallCD HsCD)
    as [HcdCov HcdMeet].
  split; [exact HcdCov | exact HcdMeet].
Qed.

(* Compact packaging: cover on both hosts after dual pair noding. *)
Theorem edge_pair_noding_cover_both :
  forall ax ay bx by_ cx cy dx dy
    (H : dual_proper_pair ax ay bx by_ cx cy dx dy),
    let pab := epos_ab_of_dual ax ay bx by_ cx cy dx dy H in
    let pcd := epos_cd_of_dual ax ay bx by_ cx cy dx dy H in
    (forall X,
       between (ptZ ax ay) (ptZ bx by_) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs
              (edge_params (noded_edge_params [pab]))) /\
         between (lerp (ptZ ax ay) (ptZ bx by_) t0)
                 (lerp (ptZ ax ay) (ptZ bx by_) t1) X) /\
    (forall X,
       between (ptZ cx cy) (ptZ dx dy) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs
              (edge_params (noded_edge_params [pcd]))) /\
         between (lerp (ptZ cx cy) (ptZ dx dy) t0)
                 (lerp (ptZ cx cy) (ptZ dx dy) t1) X).
Proof.
  intros ax ay bx by_ cx cy dx dy H.
  pose proof (edge_pair_noding_of_dual ax ay bx by_ cx cy dx dy H) as Hall.
  destruct Hall as [_ [_ [Hab [_ [_ [_ [Hcd _]]]]]]].
  split; [exact Hab | exact Hcd].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dual_proper_cut_sym.
Print Assumptions dual_proper_shared_point.
Print Assumptions dual_proper_pair_nodes_on_both.
Print Assumptions edge_pair_noding_of_dual.
Print Assumptions edge_pair_noding_cover_both.
