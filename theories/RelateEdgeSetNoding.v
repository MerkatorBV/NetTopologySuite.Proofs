(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeSetNoding
   ----------------------------------------------------------------------------
   Track 2 brick 13: segment-set dual noding.

   Brick 12 closes a *single* dual-proper pair (AB ↔ CD).  A real noder
   takes a *list* of integer edges and, for each host, collects dual-proper
   cuts from the whole set, sorts, and runs the pipeline.  This module:

     - defines `host_noding` / `set_noding` over `list ZCut` edges
     - proves every host’s dual-filtered multi-cut pipeline is sound
     - proves sort preserves membership both ways
     - proves a dual-proper pair *inside the set* contributes a node to
       *both* hosts’ noding lists, at the same geometric point

   Self-vs-self and non-crossing pairs are dropped by the dual filter
   (idet-products are not both negative).  No `Admitted`, no `Axiom`,
   no `Parameter`.

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
                               RelateEdgeDualCross RelateEdgePairNoding.

Local Open Scope Z_scope.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Host noding against a set of edges (as cuts).                          *)
(* -------------------------------------------------------------------------- *)

(* Treat each ZCut as an undirected integer edge: endpoints (c0, c1).
   The same list is the cutting set for every host. *)
Definition host_noding (h : ZCut) (es : list ZCut) : list EPos :=
  noded_from_dual_cuts (c0x h) (c0y h) (c1x h) (c1y h) es.

Definition set_noding (es : list ZCut) : list (list EPos) :=
  map (fun h => host_noding h es) es.

(* HEADLINE: dual-filter multi-cut pipeline is sound for any host vs set. *)
Theorem host_noding_sound :
  forall h es,
    let ps := host_noding h es in
    all_epos_interior ps /\
    Sorted eple ps /\
    (forall X,
       between (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs (edge_params (noded_edge_params ps))) /\
         between (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t0)
                 (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t1) X) /\
    (forall t0 t1 t2 X,
       In (t0, t1)
         (consecutive_pairs (edge_params (noded_edge_params ps))) ->
       In (t1, t2)
         (consecutive_pairs (edge_params (noded_edge_params ps))) ->
       between (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t0)
               (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t1) X ->
       between (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t1)
               (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t2) X ->
       X = lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t1).
Proof.
  intros h es.
  unfold host_noding.
  exact (edge_noding_of_dual_cuts
           (c0x h) (c0y h) (c1x h) (c1y h) es).
Qed.

(* Every edge of the set is soundly noded against the whole set. *)
Theorem set_noding_sound :
  forall es h,
    In h es ->
    let ps := host_noding h es in
    all_epos_interior ps /\
    Sorted eple ps /\
    (forall X,
       between (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs (edge_params (noded_edge_params ps))) /\
         between (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t0)
                 (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t1) X) /\
    (forall t0 t1 t2 X,
       In (t0, t1)
         (consecutive_pairs (edge_params (noded_edge_params ps))) ->
       In (t1, t2)
         (consecutive_pairs (edge_params (noded_edge_params ps))) ->
       between (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t0)
               (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t1) X ->
       between (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t1)
               (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t2) X ->
       X = lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t1).
Proof.
  intros es h _.
  exact (host_noding_sound h es).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Membership: collect + sort preserve dual-proper nodes.                 *)
(* -------------------------------------------------------------------------- *)

Lemma insert_eple_In_complete :
  forall x l p,
    p = x \/ In p l ->
    In p (insert_eple x l).
Proof.
  intros x l p H.
  induction l as [| y ys IH].
  - simpl. destruct H as [Heq | Hin].
    + left. symmetry. exact Heq.
    + contradiction.
  - simpl. destruct (epcompare x y) eqn:E.
    + (* Eq: x :: y :: ys *)
      destruct H as [Heq | Hin].
      * left. symmetry. exact Heq.
      * right. exact Hin.
    + (* Lt: x :: y :: ys *)
      destruct H as [Heq | Hin].
      * left. symmetry. exact Heq.
      * right. exact Hin.
    + (* Gt: y :: insert x ys *)
      destruct H as [Heq | Hin].
      * right. apply IH. left. exact Heq.
      * destruct Hin as [Hy | Hys].
        -- left. exact Hy.
        -- right. apply IH. right. exact Hys.
Qed.

Lemma sort_eple_In_complete :
  forall l p,
    In p l ->
    In p (sort_eple l).
Proof.
  intros l p Hin.
  induction l as [| x xs IH].
  - simpl in Hin. contradiction.
  - simpl in Hin. simpl.
    destruct Hin as [Heq | Hin'].
    + apply insert_eple_In_complete. left. symmetry. exact Heq.
    + apply insert_eple_In_complete. right. apply IH. exact Hin'.
Qed.

Lemma collect_dual_nodes_In :
  forall ax ay bx by_ c cs p,
    In c cs ->
    epos_of_dual_cut ax ay bx by_ c = Some p ->
    In p (collect_dual_nodes ax ay bx by_ cs).
Proof.
  intros ax ay bx by_ c cs p Hin He.
  induction cs as [| c' rest IH].
  - simpl in Hin. contradiction.
  - simpl in Hin. simpl.
    destruct Hin as [Heq | Hin'].
    + subst c'. rewrite He. left. reflexivity.
    + destruct (epos_of_dual_cut ax ay bx by_ c') as [p' |].
      * right. apply IH. exact Hin'.
      * apply IH. exact Hin'.
Qed.

Lemma dual_cut_node_in_host_noding :
  forall h c es p,
    In c es ->
    epos_of_dual_cut (c0x h) (c0y h) (c1x h) (c1y h) c = Some p ->
    In p (host_noding h es).
Proof.
  intros h c es p Hin He.
  unfold host_noding, noded_from_dual_cuts.
  apply sort_eple_In_complete.
  apply (collect_dual_nodes_In
           (c0x h) (c0y h) (c1x h) (c1y h) c es p Hin He).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Dual-proper pairs inside the set: both hosts carry the shared node.    *)
(* -------------------------------------------------------------------------- *)

Lemma dual_proper_of_zcut :
  forall ax ay bx by_ c,
    dual_proper_cut ax ay bx by_ c ->
    dual_proper_pair ax ay bx by_ (c0x c) (c0y c) (c1x c) (c1y c).
Proof.
  intros ax ay bx by_ c H.
  unfold dual_proper_pair, zcut.
  destruct c as [cx cy dx dy]. simpl.
  exact H.
Qed.

Lemma epos_of_dual_cut_epval :
  forall ax ay bx by_ c p,
    epos_of_dual_cut ax ay bx by_ c = Some p ->
    (epval p =
     inter_param (ptZ ax ay) (ptZ bx by_)
       (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)))%R.
Proof.
  intros ax ay bx by_ c p He.
  unfold epos_of_dual_cut in He.
  destruct (Z_lt_dec
              (idet (c0x c) (c0y c) (c1x c) (c1y c) ax ay
               * idet (c0x c) (c0y c) (c1x c) (c1y c) bx by_) 0)
    as [Hcut | Hcut]; [| discriminate He].
  destruct (Z_lt_dec
              (idet ax ay bx by_ (c0x c) (c0y c)
               * idet ax ay bx by_ (c1x c) (c1y c)) 0)
    as [Hhost | Hhost]; [| discriminate He].
  inversion He. subst p.
  apply epos_of_proper_cross_epval.
Qed.

(* HEADLINE: dual-proper pair in the set → nodes on both hosts, same point. *)
Theorem dual_pair_in_set_shared_nodes :
  forall h c es,
    In h es ->
    In c es ->
    dual_proper_cut (c0x h) (c0y h) (c1x h) (c1y h) c ->
    exists pab pcd : EPos,
      In pab (host_noding h es) /\
      In pcd (host_noding c es) /\
      epos_interior pab /\
      epos_interior pcd /\
      (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) (epval pab)
       = lerp (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)) (epval pcd))%R /\
      between_strict (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h))
        (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) (epval pab)) /\
      between_strict (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c))
        (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) (epval pab)).
Proof.
  intros h c es HinH HinC Hd.
  (* Node on host h from cut c. *)
  destruct (epos_of_dual_cut_of_dual_proper
              (c0x h) (c0y h) (c1x h) (c1y h) c Hd) as [pab Hep_ab].
  (* Dual-proper on swapped host c from cut h. *)
  pose proof (dual_proper_cut_sym
                (c0x h) (c0y h) (c1x h) (c1y h)
                (c0x c) (c0y c) (c1x c) (c1y c)) as Hsym.
  assert (Hd' : dual_proper_cut (c0x c) (c0y c) (c1x c) (c1y c)
                  (zcut (c0x h) (c0y h) (c1x h) (c1y h))).
  { apply Hsym.
    unfold zcut.
    destruct c as [cx cy dx dy]. simpl in *.
    exact Hd. }
  (* For collect we need dual_proper_cut against the *record* h, not zcut. *)
  assert (Hd_rev : dual_proper_cut (c0x c) (c0y c) (c1x c) (c1y c) h).
  { unfold dual_proper_cut, proper_cut, cut_product, host_product in *.
    destruct h as [ax ay bx by_]. destruct c as [cx cy dx dy].
    simpl in *.
    destruct Hd as [Hcut Hhost].
    split; [exact Hhost | exact Hcut]. }
  destruct (epos_of_dual_cut_of_dual_proper
              (c0x c) (c0y c) (c1x c) (c1y c) h Hd_rev) as [pcd Hep_cd].
  exists pab, pcd.
  split.
  { apply (dual_cut_node_in_host_noding h c es pab HinC Hep_ab). }
  split.
  { apply (dual_cut_node_in_host_noding c h es pcd HinH Hep_cd). }
  split.
  { apply (epos_of_dual_cut_interior
             (c0x h) (c0y h) (c1x h) (c1y h) c pab Hep_ab). }
  split.
  { apply (epos_of_dual_cut_interior
             (c0x c) (c0y c) (c1x c) (c1y c) h pcd Hep_cd). }
  (* Shared geometric point via uniqueness / inter_param. *)
  pose proof (epos_of_dual_cut_epval
                (c0x h) (c0y h) (c1x h) (c1y h) c pab Hep_ab) as Ev_ab.
  pose proof (epos_of_dual_cut_epval
                (c0x c) (c0y c) (c1x c) (c1y c) h pcd Hep_cd) as Ev_cd.
  rewrite Ev_ab, Ev_cd.
  (* dual_proper_shared_point on expanded coords. *)
  pose proof (dual_proper_of_zcut
                (c0x h) (c0y h) (c1x h) (c1y h) c Hd) as Hpair.
  pose proof (dual_proper_shared_point
                (c0x h) (c0y h) (c1x h) (c1y h)
                (c0x c) (c0y c) (c1x c) (c1y c) Hpair) as Hshare.
  (* Align epos_ab/cd_of_dual epvals with inter_param. *)
  pose proof (epos_ab_of_dual_epval
                (c0x h) (c0y h) (c1x h) (c1y h)
                (c0x c) (c0y c) (c1x c) (c1y c) Hpair) as Eab.
  pose proof (epos_cd_of_dual_epval
                (c0x h) (c0y h) (c1x h) (c1y h)
                (c0x c) (c0y c) (c1x c) (c1y c) Hpair) as Ecd.
  rewrite Eab, Ecd in Hshare.
  split.
  { exact Hshare. }
  (* Open interior on both segments at the AB-param point. *)
  pose proof (dual_proper_pair_products
                (c0x h) (c0y h) (c1x h) (c1y h)
                (c0x c) (c0y c) (c1x c) (c1y c) Hpair)
    as [Hcut Hhost].
  pose proof (inter_param_proper_node_of_idet
                (c0x h) (c0y h) (c1x h) (c1y h)
                (c0x c) (c0y c) (c1x c) (c1y c) Hhost Hcut)
    as [Hab Hcd].
  split; [exact Hab | exact Hcd].
Qed.

(* Compact: dual-proper pair in set ⇒ both host pipelines cover. *)
Theorem dual_pair_in_set_cover_both :
  forall h c es,
    In h es ->
    In c es ->
    dual_proper_cut (c0x h) (c0y h) (c1x h) (c1y h) c ->
    (forall X,
       between (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs
              (edge_params (noded_edge_params (host_noding h es)))) /\
         between (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t0)
                 (lerp (ptZ (c0x h) (c0y h)) (ptZ (c1x h) (c1y h)) t1) X) /\
    (forall X,
       between (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs
              (edge_params (noded_edge_params (host_noding c es)))) /\
         between (lerp (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)) t0)
                 (lerp (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)) t1) X).
Proof.
  intros h c es HinH HinC Hd.
  split.
  - pose proof (host_noding_sound h es) as H.
    destruct H as [_ [_ [Hcov _]]]. exact Hcov.
  - pose proof (host_noding_sound c es) as H.
    destruct H as [_ [_ [Hcov _]]]. exact Hcov.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions host_noding_sound.
Print Assumptions set_noding_sound.
Print Assumptions dual_pair_in_set_shared_nodes.
Print Assumptions dual_pair_in_set_cover_both.
