(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeMultiNode
   ----------------------------------------------------------------------------
   Track 2 brick 10: many proper-crosses on one host edge → sorted nodes →
   the exact noding pipeline.

   Brick 9 produces one interior `EPos` from a single proper-crossing cut.
   A noder collects *all* cuts against a host edge, sorts them by the exact
   comparator, merges ties, and splits.  This module supplies:

     - `insert_eple` / `sort_eple` — insertion sort by `epcompare` (`eple`)
     - `sort_eple` is `Sorted eple` and preserves `all_epos_interior`
     - `ZCut` — integer cutting segment against a fixed host
     - `collect_nodes` — map proper cuts to `EPos` (skip non-proper)
     - `edge_noding_of_cuts` — full noder contract on the sorted collection

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
                               RelateEdgeNoding RelateEdgeNode.

Local Open Scope Z_scope.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Insertion sort by the exact edge-position comparator.                  *)
(* -------------------------------------------------------------------------- *)

(* Insert x into an eple-sorted list (nondecreasing). *)
Fixpoint insert_eple (x : EPos) (l : list EPos) : list EPos :=
  match l with
  | [] => [x]
  | y :: ys =>
      match epcompare x y with
      | Gt => y :: insert_eple x ys
      | _ => x :: y :: ys
      end
  end.

Fixpoint sort_eple (l : list EPos) : list EPos :=
  match l with
  | [] => []
  | x :: xs => insert_eple x (sort_eple xs)
  end.

Lemma insert_eple_In :
  forall x l p,
    In p (insert_eple x l) -> p = x \/ In p l.
Proof.
  intros x l. induction l as [| y ys IH]; intros p Hin.
  - simpl in Hin. destruct Hin as [Heq | []]. left. symmetry. exact Heq.
  - simpl in Hin. destruct (epcompare x y) eqn:E.
    + destruct Hin as [Heq | Hin']; [left; symmetry; exact Heq |].
      destruct Hin' as [Heq | Hin'']; [right; left; exact Heq | right; right; exact Hin''].
    + destruct Hin as [Heq | Hin']; [left; symmetry; exact Heq |].
      destruct Hin' as [Heq | Hin'']; [right; left; exact Heq | right; right; exact Hin''].
    + destruct Hin as [Heq | Hin']; [right; left; exact Heq |].
      destruct (IH p Hin') as [H | H]; [left; exact H | right; right; exact H].
Qed.

Lemma sort_eple_In :
  forall l p, In p (sort_eple l) -> In p l.
Proof.
  intros l. induction l as [| x xs IH]; intros p Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct (insert_eple_In x (sort_eple xs) p Hin) as [Heq | Hin'].
    + left. symmetry. exact Heq.
    + right. apply IH. exact Hin'.
Qed.

Lemma all_epos_interior_insert :
  forall x l,
    epos_interior x ->
    all_epos_interior l ->
    all_epos_interior (insert_eple x l).
Proof.
  intros x l Hx Hall.
  apply all_epos_interior_of_In.
  intros p Hin.
  destruct (insert_eple_In x l p Hin) as [Heq | Hin'].
  - rewrite Heq. exact Hx.
  - exact (all_epos_interior_In l p Hall Hin').
Qed.

Lemma all_epos_interior_sort :
  forall l,
    all_epos_interior l ->
    all_epos_interior (sort_eple l).
Proof.
  intros l Hall.
  induction l as [| x xs IH].
  - simpl. exact I.
  - simpl in Hall. destruct Hall as [Hx Hxs].
    simpl. apply all_epos_interior_insert.
    + exact Hx.
    + apply IH. exact Hxs.
Qed.

Lemma eplt_of_epcompare_Gt :
  forall a b, epcompare a b = Gt -> eplt b a.
Proof.
  intros a b E.
  pose proof (epcompare_eple a b) as H. rewrite E in H. exact H.
Qed.

Lemma insert_eple_Sorted :
  forall x l,
    Sorted eple l ->
    Sorted eple (insert_eple x l).
Proof.
  intros x l Hs.
  induction Hs as [| y ys Hs_tl IH Hhd].
  - simpl. constructor; [constructor | constructor].
  - simpl. destruct (epcompare x y) eqn:E.
    + (* Eq: x :: y :: ys  (comparison order Eq, Lt, Gt) *)
      constructor.
      * constructor; [exact Hs_tl | exact Hhd].
      * constructor. right. apply epeq_of_epcompare_Eq. exact E.
    + (* Lt: x :: y :: ys *)
      constructor.
      * constructor; [exact Hs_tl | exact Hhd].
      * constructor. left. apply eplt_of_epcompare_Lt. exact E.
    + (* Gt: y :: insert x ys *)
      constructor.
      * apply IH.
      * destruct ys as [| z zs] eqn:Hzs.
        -- simpl. constructor. left. apply eplt_of_epcompare_Gt. exact E.
        -- simpl.
           destruct (epcompare x z) eqn:Ez.
           ++ constructor. left. apply eplt_of_epcompare_Gt. exact E.
           ++ constructor. left. apply eplt_of_epcompare_Gt. exact E.
           ++ (* Gt → z :: insert x zs; need eple y z *)
              inversion Hhd as [| ? ? Hrel]; subst.
              constructor. exact Hrel.
Qed.

Theorem sort_eple_Sorted :
  forall l, Sorted eple (sort_eple l).
Proof.
  intros l. induction l as [| x xs IH].
  - simpl. constructor.
  - simpl. apply insert_eple_Sorted. exact IH.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Integer cutting segments and node collection.                          *)
(* -------------------------------------------------------------------------- *)

Record ZCut : Type := mkZCut {
  c0x : Z; c0y : Z; c1x : Z; c1y : Z
}.

Definition cut_product (ax ay bx by_ : Z) (c : ZCut) : Z :=
  idet (c0x c) (c0y c) (c1x c) (c1y c) ax ay
  * idet (c0x c) (c0y c) (c1x c) (c1y c) bx by_.

Definition proper_cut (ax ay bx by_ : Z) (c : ZCut) : Prop :=
  cut_product ax ay bx by_ c < 0.

Fixpoint all_proper (ax ay bx by_ : Z) (cs : list ZCut) : Prop :=
  match cs with
  | [] => True
  | c :: rest => proper_cut ax ay bx by_ c /\ all_proper ax ay bx by_ rest
  end.

(* Optional node: only when the cut properly crosses the host. *)
Definition epos_of_cut (ax ay bx by_ : Z) (c : ZCut) : option EPos :=
  let na := idet (c0x c) (c0y c) (c1x c) (c1y c) ax ay in
  let nb := idet (c0x c) (c0y c) (c1x c) (c1y c) bx by_ in
  match Z_lt_dec (na * nb) 0 with
  | left H =>
      Some (epos_of_proper_cross ax ay bx by_
              (c0x c) (c0y c) (c1x c) (c1y c) H)
  | right _ => None
  end.

Fixpoint collect_nodes (ax ay bx by_ : Z) (cs : list ZCut) : list EPos :=
  match cs with
  | [] => []
  | c :: rest =>
      match epos_of_cut ax ay bx by_ c with
      | Some p => p :: collect_nodes ax ay bx by_ rest
      | None => collect_nodes ax ay bx by_ rest
      end
  end.

Lemma epos_of_cut_interior :
  forall ax ay bx by_ c p,
    epos_of_cut ax ay bx by_ c = Some p ->
    epos_interior p.
Proof.
  intros ax ay bx by_ c p He.
  unfold epos_of_cut in He.
  destruct (Z_lt_dec
              (idet (c0x c) (c0y c) (c1x c) (c1y c) ax ay
               * idet (c0x c) (c0y c) (c1x c) (c1y c) bx by_) 0)
    as [H | H]; [| discriminate He].
  inversion He. subst p.
  apply epos_of_proper_cross_interior.
Qed.

Lemma epos_of_cut_proper :
  forall ax ay bx by_ c,
    proper_cut ax ay bx by_ c ->
    exists p, epos_of_cut ax ay bx by_ c = Some p.
Proof.
  intros ax ay bx by_ c Hp.
  unfold proper_cut, cut_product, epos_of_cut in *.
  destruct (Z_lt_dec
              (idet (c0x c) (c0y c) (c1x c) (c1y c) ax ay
               * idet (c0x c) (c0y c) (c1x c) (c1y c) bx by_) 0)
    as [H | H].
  - eexists. reflexivity.
  - exfalso. apply H. exact Hp.
Qed.

Lemma collect_nodes_all_interior :
  forall ax ay bx by_ cs,
    all_epos_interior (collect_nodes ax ay bx by_ cs).
Proof.
  intros ax ay bx by_ cs.
  induction cs as [| c rest IH].
  - simpl. exact I.
  - simpl. destruct (epos_of_cut ax ay bx by_ c) as [p |] eqn:He.
    + simpl. split.
      * apply (epos_of_cut_interior ax ay bx by_ c p He).
      * exact IH.
    + exact IH.
Qed.

Lemma collect_nodes_of_all_proper :
  forall ax ay bx by_ cs,
    all_proper ax ay bx by_ cs ->
    all_epos_interior (collect_nodes ax ay bx by_ cs).
Proof.
  intros. apply collect_nodes_all_interior.
Qed.

(* Under all_proper, every cut contributes a node (no None). *)
Lemma collect_nodes_length_all_proper :
  forall ax ay bx by_ cs,
    all_proper ax ay bx by_ cs ->
    length (collect_nodes ax ay bx by_ cs) = length cs.
Proof.
  intros ax ay bx by_ cs Hall.
  induction cs as [| c rest IH].
  - reflexivity.
  - simpl in Hall. destruct Hall as [Hp Hrest].
    simpl. destruct (epos_of_cut_proper ax ay bx by_ c Hp) as [p He].
    rewrite He. simpl. f_equal. apply IH. exact Hrest.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Pipeline: sort collected nodes and apply edge_noding_sound.            *)
(* -------------------------------------------------------------------------- *)

Definition noded_from_cuts (ax ay bx by_ : Z) (cs : list ZCut) : list EPos :=
  sort_eple (collect_nodes ax ay bx by_ cs).

Lemma noded_from_cuts_Sorted :
  forall ax ay bx by_ cs,
    Sorted eple (noded_from_cuts ax ay bx by_ cs).
Proof.
  intros. unfold noded_from_cuts. apply sort_eple_Sorted.
Qed.

Lemma noded_from_cuts_interior :
  forall ax ay bx by_ cs,
    all_epos_interior (noded_from_cuts ax ay bx by_ cs).
Proof.
  intros. unfold noded_from_cuts.
  apply all_epos_interior_sort.
  apply collect_nodes_all_interior.
Qed.

(* HEADLINE: any list of integer cuts yields a sound single-edge noding
   of the proper ones (non-proper cuts are dropped). *)
Theorem edge_noding_of_cuts :
  forall ax ay bx by_ cs,
    let ps := noded_from_cuts ax ay bx by_ cs in
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
  set (ps := noded_from_cuts ax ay bx by_ cs).
  pose proof (noded_from_cuts_interior ax ay bx by_ cs) as Hall.
  pose proof (noded_from_cuts_Sorted ax ay bx by_ cs) as Hs.
  change (noded_from_cuts ax ay bx by_ cs) with ps in Hall, Hs.
  split; [exact Hall |].
  split; [exact Hs |].
  pose proof (edge_noding_sound (ptZ ax ay) (ptZ bx by_) ps Hall Hs) as Hsnd.
  exact Hsnd.
Qed.

(* Specialise: when every cut is proper, nothing is dropped. *)
Theorem edge_noding_of_all_proper_cuts :
  forall ax ay bx by_ cs,
    all_proper ax ay bx by_ cs ->
    let ps := noded_from_cuts ax ay bx by_ cs in
    length (collect_nodes ax ay bx by_ cs) = length cs /\
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
  intros ax ay bx by_ cs Hallp.
  set (ps := noded_from_cuts ax ay bx by_ cs).
  split.
  - apply collect_nodes_length_all_proper. exact Hallp.
  - pose proof (edge_noding_of_cuts ax ay bx by_ cs) as H.
    change (noded_from_cuts ax ay bx by_ cs) with ps in H.
    destruct H as [H1 [H2 [H3 _]]].
    split; [exact H1 |].
    split; [exact H2 | exact H3].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions sort_eple_Sorted.
Print Assumptions collect_nodes_all_interior.
Print Assumptions edge_noding_of_cuts.
Print Assumptions edge_noding_of_all_proper_cuts.
