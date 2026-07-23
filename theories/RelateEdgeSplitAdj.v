(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeSplitAdj
   ----------------------------------------------------------------------------
   Track 2 brick 7: adjacent pieces of a multi-node split meet only at the
   shared node, and exact edge-positions (`EPos`) specialise the real split.

   Brick 6 (`RelateEdgeSplit`) proved covering: sorted interior parameters
   cut A–B into consecutive pieces that cover the host.  Covering alone does
   not prevent two adjacent pieces from overlapping in their relative
   interiors.  This module closes that gap and wires the integer-exact
   position type of bricks 1–5 into the real parameter chain.

     (1) Two consecutive host intervals [t0, t1] and [t1, t2] (t0 < t1 < t2)
         meet only at lerp A B t1.
     (2) Any two consecutive pairs drawn from a strictly increasing parameter
         chain (in particular `edge_params ts`) inherit that exclusive meet.
     (3) `map epval` of a `Sorted eplt` list is `sorted_lt`; interior
         `EPos` values in (0,1) yield `all_interior`, so bricks 1–5 feed
         brick 6–7 without leaving the exact lane.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Sorting.Sorted.
From NTS.Proofs Require Import Distance Orientation Segment
                               RelateEdgeInterParam RelateEdgePosOrder
                               RelateEdgePosSort RelateEdgeSplit.

Local Open Scope R_scope.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Adjacent host intervals meet only at the shared parameter.             *)
(* -------------------------------------------------------------------------- *)

(* HEADLINE: two consecutive subsegments meet only at their shared node. *)
Theorem edge_split_adj_meet :
  forall A B t0 t1 t2 X,
    t0 < t1 ->
    t1 < t2 ->
    between (lerp A B t0) (lerp A B t1) X ->
    between (lerp A B t1) (lerp A B t2) X ->
    X = lerp A B t1.
Proof.
  intros A B t0 t1 t2 X Ht01 Ht12 H01 H12.
  destruct (param_of_between_lerp A B t0 t1 X ltac:(lra) H01)
    as [s1 [[Hs10 Hs11] Hx1]].
  destruct (param_of_between_lerp A B t1 t2 X ltac:(lra) H12)
    as [s2 [[Hs20 Hs21] Hx2]].
  assert (Heq : lerp A B s1 = lerp A B s2).
  { rewrite <- Hx1, <- Hx2. reflexivity. }
  destruct (lerp_eq_cases A B s1 s2 Heq) as [Hs | HAB].
  - assert (Hs1t : s1 = t1) by lra.
    rewrite Hx1, Hs1t. reflexivity.
  - subst B. rewrite Hx1. unfold lerp. destruct A. f_equal; ring.
Qed.

(* Specialise: left endpoint at 0 (first piece of a chain). *)
Corollary edge_split_adj_meet_from_start :
  forall A B t1 t2 X,
    0 < t1 < t2 ->
    between A (lerp A B t1) X ->
    between (lerp A B t1) (lerp A B t2) X ->
    X = lerp A B t1.
Proof.
  intros A B t1 t2 X Ht H01 H12.
  assert (H01' : between (lerp A B 0) (lerp A B t1) X).
  { rewrite lerp_0. exact H01. }
  apply (edge_split_adj_meet A B 0 t1 t2 X); try lra; assumption.
Qed.

(* Specialise: right endpoint at 1 (last piece of a chain). *)
Corollary edge_split_adj_meet_to_end :
  forall A B t0 t1 X,
    t0 < t1 < 1 ->
    between (lerp A B t0) (lerp A B t1) X ->
    between (lerp A B t1) B X ->
    X = lerp A B t1.
Proof.
  intros A B t0 t1 X Ht H01 H12.
  assert (H12' : between (lerp A B t1) (lerp A B 1) X).
  { rewrite lerp_1. exact H12. }
  apply (edge_split_adj_meet A B t0 t1 1 X); try lra; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Consecutive pairs in a strictly increasing parameter list.             *)
(* -------------------------------------------------------------------------- *)

(* Strict increase of every consecutive pair in a Sorted Rlt list. *)
Lemma consecutive_pairs_lt :
  forall ts t0 t1,
    sorted_lt ts ->
    In (t0, t1) (consecutive_pairs ts) ->
    t0 < t1.
Proof.
  intros ts t0 t1 Hs Hin.
  induction ts as [| a ts' IH].
  - simpl in Hin. contradiction.
  - destruct ts' as [| b rest].
    + simpl in Hin. contradiction.
    + simpl in Hin. destruct Hin as [Heq | Hin'].
      * injection Heq as <- <-. apply sorted_lt_hd in Hs. exact Hs.
      * apply IH.
        -- apply sorted_lt_cons_inv in Hs. exact Hs.
        -- exact Hin'.
Qed.

(* If (t0,t1) and (t1,t2) both appear as consecutive pairs of a strictly
   increasing list, then t0 < t1 < t2 (so adj-meet applies).  We only need
   the chained inequalities from each pair being consecutive. *)
Lemma consecutive_pairs_chain_lt :
  forall ts t0 t1 t2,
    sorted_lt ts ->
    In (t0, t1) (consecutive_pairs ts) ->
    In (t1, t2) (consecutive_pairs ts) ->
    t0 < t1 /\ t1 < t2.
Proof.
  intros ts t0 t1 t2 Hs H01 H12.
  split.
  - exact (consecutive_pairs_lt ts t0 t1 Hs H01).
  - exact (consecutive_pairs_lt ts t1 t2 Hs H12).
Qed.

(* HEADLINE: adjacent pieces drawn from a sorted param chain meet only at the node. *)
Theorem edge_split_chain_adj_meet :
  forall A B ts t0 t1 t2 X,
    sorted_lt ts ->
    In (t0, t1) (consecutive_pairs ts) ->
    In (t1, t2) (consecutive_pairs ts) ->
    between (lerp A B t0) (lerp A B t1) X ->
    between (lerp A B t1) (lerp A B t2) X ->
    X = lerp A B t1.
Proof.
  intros A B ts t0 t1 t2 X Hs H01 H12 Hb01 Hb12.
  destruct (consecutive_pairs_chain_lt ts t0 t1 t2 Hs H01 H12) as [Ht01 Ht12].
  exact (edge_split_adj_meet A B t0 t1 t2 X Ht01 Ht12 Hb01 Hb12).
Qed.

(* Specialise to the noding param chain 0 :: ts ++ [1]. *)
Lemma sorted_lt_snoc_one :
  forall ts z,
    sorted_lt ts ->
    (forall t, In t ts -> t < z) ->
    sorted_lt (ts ++ [z]).
Proof.
  intros ts z Hs Hlt.
  induction ts as [| t rest IH].
  - simpl. constructor; [constructor | constructor].
  - simpl. constructor.
    + apply IH.
      * apply sorted_lt_cons_inv in Hs. exact Hs.
      * intros u Hin. apply Hlt. right. exact Hin.
    + destruct rest as [| t' rest'].
      * simpl. constructor. apply Hlt. left. reflexivity.
      * simpl. constructor. apply sorted_lt_hd in Hs. exact Hs.
Qed.

Lemma all_interior_lt_one :
  forall ts t, all_interior ts -> In t ts -> t < 1.
Proof.
  intros ts t Hall Hin.
  induction ts as [| u us IH]; [contradiction |].
  simpl in Hall. destruct Hall as [Hu Hall'].
  destruct Hin as [Heq | Hin'].
  - rewrite <- Heq. apply Hu.
  - apply IH; assumption.
Qed.

Lemma all_interior_gt_zero :
  forall ts t, all_interior ts -> In t ts -> 0 < t.
Proof.
  intros ts t Hall Hin.
  induction ts as [| u us IH]; [contradiction |].
  simpl in Hall. destruct Hall as [Hu Hall'].
  destruct Hin as [Heq | Hin'].
  - rewrite <- Heq. apply Hu.
  - apply IH; assumption.
Qed.

Lemma sorted_lt_edge_params :
  forall ts,
    all_interior ts ->
    sorted_lt ts ->
    sorted_lt (edge_params ts).
Proof.
  intros ts Hall Hs.
  unfold edge_params.
  constructor.
  - apply sorted_lt_snoc_one.
    + exact Hs.
    + intros t Hin. exact (all_interior_lt_one ts t Hall Hin).
  - destruct ts as [| t rest].
    + simpl. constructor. lra.
    + simpl. constructor.
      apply (all_interior_gt_zero (t :: rest) t Hall).
      left. reflexivity.
Qed.

(* HEADLINE: adjacent edge_params pieces meet only at the shared node. *)
Theorem edge_params_adj_meet :
  forall A B ts t0 t1 t2 X,
    all_interior ts ->
    sorted_lt ts ->
    In (t0, t1) (consecutive_pairs (edge_params ts)) ->
    In (t1, t2) (consecutive_pairs (edge_params ts)) ->
    between (lerp A B t0) (lerp A B t1) X ->
    between (lerp A B t1) (lerp A B t2) X ->
    X = lerp A B t1.
Proof.
  intros A B ts t0 t1 t2 X Hall Hs H01 H12 Hb01 Hb12.
  apply (edge_split_chain_adj_meet A B (edge_params ts) t0 t1 t2 X).
  - apply sorted_lt_edge_params; assumption.
  - exact H01.
  - exact H12.
  - exact Hb01.
  - exact Hb12.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Bridge from exact EPos positions (bricks 1–5) to real split params.    *)
(* -------------------------------------------------------------------------- *)

Definition epos_vals (ps : list EPos) : list R := map epval ps.

(* Sorted eplt ⇒ sorted real values. *)
Theorem sorted_eplt_sorted_lt_epval :
  forall ps, Sorted eplt ps -> sorted_lt (epos_vals ps).
Proof.
  intros ps Hs.
  unfold epos_vals, sorted_lt.
  induction Hs as [| a l Hstail IH Hhd].
  - simpl. constructor.
  - simpl. constructor.
    + apply IH.
    + destruct l as [| b t].
      * constructor.
      * simpl. constructor.
        inversion Hhd as [| ? ? Hrel]; subst.
        apply eplt_iff_R. exact Hrel.
Qed.

(* Interior EPos: 0 < epval < 1 (the clip regime of brick 4). *)
Definition epos_interior (p : EPos) : Prop :=
  (0 < epval p < 1)%R.

Fixpoint all_epos_interior (ps : list EPos) : Prop :=
  match ps with
  | [] => True
  | p :: rest => epos_interior p /\ all_epos_interior rest
  end.

Lemma all_epos_interior_all_interior :
  forall ps,
    all_epos_interior ps ->
    all_interior (epos_vals ps).
Proof.
  intros ps Hall. induction ps as [| p rest IH].
  - simpl. exact I.
  - simpl in Hall. destruct Hall as [Hp Hrest]. simpl. split.
    + exact Hp.
    + apply IH. exact Hrest.
Qed.

(* HEADLINE: a sorted exact-position list after clip feeds the real split cover. *)
Theorem edge_split_cover_of_epos :
  forall A B ps X,
    all_epos_interior ps ->
    Sorted eplt ps ->
    between A B X ->
    exists t0 t1,
      In (t0, t1) (consecutive_pairs (edge_params (epos_vals ps))) /\
      between (lerp A B t0) (lerp A B t1) X.
Proof.
  intros A B ps X Hall Hs HX.
  apply edge_split_cover.
  - apply all_epos_interior_all_interior. exact Hall.
  - apply sorted_eplt_sorted_lt_epval. exact Hs.
  - exact HX.
Qed.

(* Same packaging through edge_pieces. *)
Theorem edge_split_cover_pieces_of_epos :
  forall A B ps X,
    all_epos_interior ps ->
    Sorted eplt ps ->
    between A B X ->
    exists P Q,
      In (P, Q) (edge_pieces A B (epos_vals ps)) /\
      between P Q X.
Proof.
  intros A B ps X Hall Hs HX.
  apply edge_split_cover_pieces.
  - apply all_epos_interior_all_interior. exact Hall.
  - apply sorted_eplt_sorted_lt_epval. exact Hs.
  - exact HX.
Qed.

(* Adjacent meet after epdedup: exact lane → exclusive shared node. *)
Theorem edge_params_adj_meet_of_epos :
  forall A B ps t0 t1 t2 X,
    all_epos_interior ps ->
    Sorted eplt ps ->
    In (t0, t1) (consecutive_pairs (edge_params (epos_vals ps))) ->
    In (t1, t2) (consecutive_pairs (edge_params (epos_vals ps))) ->
    between (lerp A B t0) (lerp A B t1) X ->
    between (lerp A B t1) (lerp A B t2) X ->
    X = lerp A B t1.
Proof.
  intros A B ps t0 t1 t2 X Hall Hs H01 H12 Hb01 Hb12.
  apply (edge_params_adj_meet A B (epos_vals ps) t0 t1 t2 X).
  - apply all_epos_interior_all_interior. exact Hall.
  - apply sorted_eplt_sorted_lt_epval. exact Hs.
  - exact H01.
  - exact H12.
  - exact Hb01.
  - exact Hb12.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions edge_split_adj_meet.
Print Assumptions edge_split_chain_adj_meet.
Print Assumptions edge_params_adj_meet.
Print Assumptions sorted_eplt_sorted_lt_epval.
Print Assumptions edge_split_cover_of_epos.
Print Assumptions edge_params_adj_meet_of_epos.
