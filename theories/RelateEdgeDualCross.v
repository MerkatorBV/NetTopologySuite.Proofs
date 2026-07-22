(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeDualCross
   ----------------------------------------------------------------------------
   Track 2 brick 11: dual proper-cross filter — node on BOTH closed segments.

   Brick 10's `proper_cut` only requires opposite signs of the *cutting* line
   against the host endpoints (idet CDA · idet CDB < 0).  That forces the
   det/det parameter into (0,1) on the host line (clip), but the intersection
   may still miss the cutting *segment* (extended-line hit).

   Full segment/segment proper-cross needs the dual product as well:

       idet ABC · idet ABD < 0   (host line separates C and D)

   (brick 4's `inter_param_proper_node_of_idet`).  This module:

     - defines `host_product` / `dual_proper_cut` / `all_dual_proper`
     - collects only dual-proper cuts into nodes
     - proves each dual-proper node lies in the open interior of both closed
       integer segments
     - runs the multi-node noding pipeline under the dual filter

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
                               RelateEdgeMultiNode RelateBoundary.

Local Open Scope Z_scope.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Dual proper-cross predicate.                                           *)
(* -------------------------------------------------------------------------- *)

(* Host line separates the cut endpoints. *)
Definition host_product (ax ay bx by_ : Z) (c : ZCut) : Z :=
  idet ax ay bx by_ (c0x c) (c0y c)
  * idet ax ay bx by_ (c1x c) (c1y c).

(* Mutual opposite-side signs: proper segment/segment cross (integer). *)
Definition dual_proper_cut (ax ay bx by_ : Z) (c : ZCut) : Prop :=
  proper_cut ax ay bx by_ c /\ host_product ax ay bx by_ c < 0.

Fixpoint all_dual_proper (ax ay bx by_ : Z) (cs : list ZCut) : Prop :=
  match cs with
  | [] => True
  | c :: rest =>
      dual_proper_cut ax ay bx by_ c /\ all_dual_proper ax ay bx by_ rest
  end.

Lemma dual_proper_implies_proper :
  forall ax ay bx by_ c,
    dual_proper_cut ax ay bx by_ c ->
    proper_cut ax ay bx by_ c.
Proof. intros ax ay bx by_ c [Hp _]. exact Hp. Qed.

Lemma all_dual_proper_implies_all_proper :
  forall ax ay bx by_ cs,
    all_dual_proper ax ay bx by_ cs ->
    all_proper ax ay bx by_ cs.
Proof.
  intros ax ay bx by_ cs Hall.
  induction cs as [| c rest IH].
  - simpl. exact I.
  - simpl in Hall. destruct Hall as [[Hp _] Hrest].
    simpl. split; [exact Hp | apply IH; exact Hrest].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Dual-proper node is interior on both closed segments.                  *)
(* -------------------------------------------------------------------------- *)

(* Reconstruct the real intersection point of the two integer segments. *)
Definition inter_ptZ (ax ay bx by_ cx cy dx dy : Z) : Point :=
  lerp (ptZ ax ay) (ptZ bx by_)
       (inter_param (ptZ ax ay) (ptZ bx by_) (ptZ cx cy) (ptZ dx dy)).

Theorem dual_proper_node_on_both_segments :
  forall ax ay bx by_ c,
    dual_proper_cut ax ay bx by_ c ->
    let cx := c0x c in let cy := c0y c in
    let dx := c1x c in let dy := c1y c in
    between_strict (ptZ ax ay) (ptZ bx by_)
      (inter_ptZ ax ay bx by_ cx cy dx dy) /\
    between_strict (ptZ cx cy) (ptZ dx dy)
      (inter_ptZ ax ay bx by_ cx cy dx dy).
Proof.
  intros ax ay bx by_ c [Hcut Hhost].
  unfold proper_cut, cut_product, host_product in *.
  unfold inter_ptZ.
  apply inter_param_proper_node_of_idet.
  - exact Hhost.
  - exact Hcut.
Qed.

(* The dual-proper EPos (via brick 9 constructor) has epval = inter_param and
   the lerp at that param is on both open segments. *)
Theorem dual_proper_epos_on_both :
  forall ax ay bx by_ c,
    dual_proper_cut ax ay bx by_ c ->
    exists (Hcut : proper_cut ax ay bx by_ c),
      epos_interior
        (epos_of_proper_cross ax ay bx by_
           (c0x c) (c0y c) (c1x c) (c1y c) Hcut) /\
      (epval (epos_of_proper_cross ax ay bx by_
                (c0x c) (c0y c) (c1x c) (c1y c) Hcut) =
       inter_param (ptZ ax ay) (ptZ bx by_)
         (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)))%R /\
      between_strict (ptZ ax ay) (ptZ bx by_)
        (lerp (ptZ ax ay) (ptZ bx by_)
              (inter_param (ptZ ax ay) (ptZ bx by_)
                 (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)))) /\
      between_strict (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c))
        (lerp (ptZ ax ay) (ptZ bx by_)
              (inter_param (ptZ ax ay) (ptZ bx by_)
                 (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)))).
Proof.
  intros ax ay bx by_ c [Hcut Hhost].
  exists Hcut.
  split; [apply epos_of_proper_cross_interior |].
  split; [apply epos_of_proper_cross_epval |].
  exact (inter_param_proper_node_of_idet ax ay bx by_
           (c0x c) (c0y c) (c1x c) (c1y c) Hhost Hcut).
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Collect dual-proper cuts only.                                         *)
(* -------------------------------------------------------------------------- *)

Definition epos_of_dual_cut (ax ay bx by_ : Z) (c : ZCut) : option EPos :=
  let na := idet (c0x c) (c0y c) (c1x c) (c1y c) ax ay in
  let nb := idet (c0x c) (c0y c) (c1x c) (c1y c) bx by_ in
  let ha := idet ax ay bx by_ (c0x c) (c0y c) in
  let hb := idet ax ay bx by_ (c1x c) (c1y c) in
  match Z_lt_dec (na * nb) 0 with
  | left Hcut =>
      match Z_lt_dec (ha * hb) 0 with
      | left _ => Some (epos_of_proper_cross ax ay bx by_
                          (c0x c) (c0y c) (c1x c) (c1y c) Hcut)
      | right _ => None
      end
  | right _ => None
  end.

Fixpoint collect_dual_nodes (ax ay bx by_ : Z) (cs : list ZCut) : list EPos :=
  match cs with
  | [] => []
  | c :: rest =>
      match epos_of_dual_cut ax ay bx by_ c with
      | Some p => p :: collect_dual_nodes ax ay bx by_ rest
      | None => collect_dual_nodes ax ay bx by_ rest
      end
  end.

Lemma epos_of_dual_cut_interior :
  forall ax ay bx by_ c p,
    epos_of_dual_cut ax ay bx by_ c = Some p ->
    epos_interior p.
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
  apply epos_of_proper_cross_interior.
Qed.

Lemma epos_of_dual_cut_of_dual_proper :
  forall ax ay bx by_ c,
    dual_proper_cut ax ay bx by_ c ->
    exists p, epos_of_dual_cut ax ay bx by_ c = Some p.
Proof.
  intros ax ay bx by_ c [Hcut Hhost].
  unfold dual_proper_cut, proper_cut, cut_product, host_product,
         epos_of_dual_cut in *.
  destruct (Z_lt_dec
              (idet (c0x c) (c0y c) (c1x c) (c1y c) ax ay
               * idet (c0x c) (c0y c) (c1x c) (c1y c) bx by_) 0)
    as [Hc | Hc].
  - destruct (Z_lt_dec
                (idet ax ay bx by_ (c0x c) (c0y c)
                 * idet ax ay bx by_ (c1x c) (c1y c)) 0)
      as [Hh | Hh].
    + eexists. reflexivity.
    + exfalso. apply Hh. exact Hhost.
  - exfalso. apply Hc. exact Hcut.
Qed.

Lemma collect_dual_nodes_all_interior :
  forall ax ay bx by_ cs,
    all_epos_interior (collect_dual_nodes ax ay bx by_ cs).
Proof.
  intros ax ay bx by_ cs.
  induction cs as [| c rest IH].
  - simpl. exact I.
  - simpl. destruct (epos_of_dual_cut ax ay bx by_ c) as [p |] eqn:He.
    + simpl. split.
      * apply (epos_of_dual_cut_interior ax ay bx by_ c p He).
      * exact IH.
    + exact IH.
Qed.

Lemma collect_dual_nodes_length_all_dual :
  forall ax ay bx by_ cs,
    all_dual_proper ax ay bx by_ cs ->
    length (collect_dual_nodes ax ay bx by_ cs) = length cs.
Proof.
  intros ax ay bx by_ cs Hall.
  induction cs as [| c rest IH].
  - reflexivity.
  - simpl in Hall. destruct Hall as [Hd Hrest].
    simpl. destruct (epos_of_dual_cut_of_dual_proper ax ay bx by_ c Hd) as [p He].
    rewrite He. simpl. f_equal. apply IH. exact Hrest.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Noding pipeline under the dual filter.                                 *)
(* -------------------------------------------------------------------------- *)

Definition noded_from_dual_cuts (ax ay bx by_ : Z) (cs : list ZCut) : list EPos :=
  sort_eple (collect_dual_nodes ax ay bx by_ cs).

Lemma noded_from_dual_cuts_Sorted :
  forall ax ay bx by_ cs,
    Sorted eple (noded_from_dual_cuts ax ay bx by_ cs).
Proof.
  intros. unfold noded_from_dual_cuts. apply sort_eple_Sorted.
Qed.

Lemma noded_from_dual_cuts_interior :
  forall ax ay bx by_ cs,
    all_epos_interior (noded_from_dual_cuts ax ay bx by_ cs).
Proof.
  intros. unfold noded_from_dual_cuts.
  apply all_epos_interior_sort.
  apply collect_dual_nodes_all_interior.
Qed.

(* HEADLINE: dual-proper cuts → sound single-edge noding (segment/segment). *)
Theorem edge_noding_of_dual_cuts :
  forall ax ay bx by_ cs,
    let ps := noded_from_dual_cuts ax ay bx by_ cs in
    all_epos_interior ps /\
    Sorted eple ps /\
    (forall X,
       between (ptZ ax ay) (ptZ bx by_) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs (edge_params (noded_edge_params ps))) /\
         between (lerp (ptZ ax ay) (ptZ bx by_) t0)
                 (lerp (ptZ ax ay) (ptZ bx by_) t1) X) /\
    (forall t0 t1 t2 X,
       In (t0, t1)
         (consecutive_pairs (edge_params (noded_edge_params ps))) ->
       In (t1, t2)
         (consecutive_pairs (edge_params (noded_edge_params ps))) ->
       between (lerp (ptZ ax ay) (ptZ bx by_) t0)
               (lerp (ptZ ax ay) (ptZ bx by_) t1) X ->
       between (lerp (ptZ ax ay) (ptZ bx by_) t1)
               (lerp (ptZ ax ay) (ptZ bx by_) t2) X ->
       X = lerp (ptZ ax ay) (ptZ bx by_) t1).
Proof.
  intros ax ay bx by_ cs.
  set (ps := noded_from_dual_cuts ax ay bx by_ cs).
  pose proof (noded_from_dual_cuts_interior ax ay bx by_ cs) as Hall.
  pose proof (noded_from_dual_cuts_Sorted ax ay bx by_ cs) as Hs.
  change (noded_from_dual_cuts ax ay bx by_ cs) with ps in Hall, Hs.
  split; [exact Hall |].
  split; [exact Hs |].
  exact (edge_noding_sound (ptZ ax ay) (ptZ bx by_) ps Hall Hs).
Qed.

Theorem edge_noding_of_all_dual_proper_cuts :
  forall ax ay bx by_ cs,
    all_dual_proper ax ay bx by_ cs ->
    let ps := noded_from_dual_cuts ax ay bx by_ cs in
    length (collect_dual_nodes ax ay bx by_ cs) = length cs /\
    all_epos_interior ps /\
    Sorted eple ps /\
    (forall X,
       between (ptZ ax ay) (ptZ bx by_) X ->
       exists t0 t1 : R,
         In (t0, t1)
           (consecutive_pairs (edge_params (noded_edge_params ps))) /\
         between (lerp (ptZ ax ay) (ptZ bx by_) t0)
                 (lerp (ptZ ax ay) (ptZ bx by_) t1) X).
Proof.
  intros ax ay bx by_ cs Halld.
  set (ps := noded_from_dual_cuts ax ay bx by_ cs).
  split.
  - apply collect_dual_nodes_length_all_dual. exact Halld.
  - pose proof (edge_noding_of_dual_cuts ax ay bx by_ cs) as H.
    change (noded_from_dual_cuts ax ay bx by_ cs) with ps in H.
    destruct H as [H1 [H2 [H3 _]]].
    split; [exact H1 |].
    split; [exact H2 | exact H3].
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dual_proper_node_on_both_segments.
Print Assumptions dual_proper_epos_on_both.
Print Assumptions edge_noding_of_dual_cuts.
Print Assumptions edge_noding_of_all_dual_proper_cuts.
