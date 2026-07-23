(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeSplit
   ----------------------------------------------------------------------------
   Track 2 brick 6: split an edge at sorted interior nodes into covering pieces.

   Bricks 1–5 deliver exact compare → geometry → sort → clip → equal-ratio
   merge.  Noding's payoff is to *cut* the host edge A–B at those interior
   positions into a chain of subsegments that:

     (1) cover the original closed segment,
     (2) meet only at the shared node (adjacent pieces),
     (3) are themselves closed segments on the supporting line.

   This module lands the affine split calculus (`lerp` reparametrisation),
   the one-node cover/meet theorems, and the multi-node covering theorem for
   a strictly sorted list of interior parameters.  Parameters are reals in
   (0, 1); the integer-exact positions of bricks 1–5 specialise via `epval`.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Sorting.Sorted.
From NTS.Proofs Require Import Distance Orientation Segment
                               RelateEdgeInterParam.

Local Open Scope R_scope.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Affine parameter calculus for lerp.                                    *)
(* -------------------------------------------------------------------------- *)

Lemma lerp_0 : forall A B, lerp A B 0 = A.
Proof.
  intros [ax ay] B. unfold lerp. simpl. f_equal; ring.
Qed.

Lemma lerp_1 : forall A B, lerp A B 1 = B.
Proof.
  intros A [bx by_]. unfold lerp. simpl. f_equal; ring.
Qed.

Lemma between_of_lerp :
  forall A B t, 0 <= t <= 1 -> between A B (lerp A B t).
Proof.
  intros A B t [Ht0 Ht1].
  exists t. unfold lerp; simpl.
  repeat split; try assumption; ring.
Qed.

Lemma between_as_lerp :
  forall A B X,
    between A B X ->
    exists s, 0 <= s <= 1 /\ X = lerp A B s.
Proof.
  intros A B X [s [Hs0 [Hs1 [Hx Hy]]]].
  exists s. split.
  - split; assumption.
  - unfold lerp. destruct X. simpl in *. f_equal; [exact Hx | exact Hy].
Qed.

Lemma lerp_lerp :
  forall A B t0 t1 u,
    lerp (lerp A B t0) (lerp A B t1) u =
    lerp A B ((1 - u) * t0 + u * t1).
Proof.
  intros A B t0 t1 u.
  unfold lerp; simpl. f_equal; ring.
Qed.

Lemma lerp_eq_cases :
  forall A B s1 s2,
    lerp A B s1 = lerp A B s2 ->
    s1 = s2 \/ A = B.
Proof.
  intros A B s1 s2 Heq.
  destruct (Req_dec s1 s2) as [He | Hne].
  - left; exact He.
  - right.
    unfold lerp in Heq. injection Heq as Hx Hy.
    destruct A as [ax ay], B as [bx by_]. simpl in *.
    f_equal; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Subsegment between two host parameters.                                *)
(* -------------------------------------------------------------------------- *)

Lemma between_lerp_of_param_interval :
  forall A B t0 t1 s,
    t0 <= t1 ->
    t0 <= s <= t1 ->
    between (lerp A B t0) (lerp A B t1) (lerp A B s).
Proof.
  intros A B t0 t1 s Ht01 [Hs0 Hs1].
  destruct (Req_dec t0 t1) as [Heq | Hne].
  - rewrite Heq in *. assert (Hs : s = t1) by lra.
    rewrite Hs. apply between_P0.
  - set (u := (s - t0) / (t1 - t0)).
    assert (Hden : t1 - t0 <> 0) by lra.
    assert (Hu0 : 0 <= u).
    { unfold u.
      apply Rmult_le_pos.
      - lra.
      - apply Rlt_le. apply Rinv_0_lt_compat. lra. }
    assert (Hu1 : u <= 1).
    { unfold u.
      apply (Rmult_le_reg_r (t1 - t0)); [lra |].
      replace (1 * (t1 - t0)) with (t1 - t0) by ring.
      replace (((s - t0) / (t1 - t0)) * (t1 - t0)) with (s - t0)
        by (field; exact Hden).
      lra. }
    assert (Hs_u : s = (1 - u) * t0 + u * t1).
    { unfold u. field; exact Hden. }
    rewrite Hs_u, <- lerp_lerp.
    apply between_of_lerp. split; assumption.
Qed.

Lemma param_of_between_lerp :
  forall A B t0 t1 X,
    t0 <= t1 ->
    between (lerp A B t0) (lerp A B t1) X ->
    exists s, t0 <= s <= t1 /\ X = lerp A B s.
Proof.
  intros A B t0 t1 X Ht01 Hbet.
  destruct (between_as_lerp _ _ _ Hbet) as [u [Hu Hx]].
  rewrite Hx, lerp_lerp.
  set (s := (1 - u) * t0 + u * t1).
  exists s. split.
  - destruct Hu as [Hu0 Hu1]. unfold s. split; nra.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  One-node split: cover and meet-only-at-node.                           *)
(* -------------------------------------------------------------------------- *)

Theorem edge_split_one_cover :
  forall A B t X,
    0 < t < 1 ->
    between A B X ->
    between A (lerp A B t) X \/ between (lerp A B t) B X.
Proof.
  intros A B t X Ht HX.
  destruct (between_as_lerp A B X HX) as [s [[Hs0 Hs1] Hx]].
  rewrite Hx.
  destruct (Rle_dec s t) as [Hst | Hts].
  - left.
    assert (H : between (lerp A B 0) (lerp A B t) (lerp A B s)).
    { apply between_lerp_of_param_interval; lra. }
    rewrite (lerp_0 A B) in H. exact H.
  - right.
    assert (H : between (lerp A B t) (lerp A B 1) (lerp A B s)).
    { apply between_lerp_of_param_interval; lra. }
    rewrite (lerp_1 A B) in H. exact H.
Qed.

Theorem edge_split_one_meet :
  forall A B t X,
    0 < t < 1 ->
    between A (lerp A B t) X ->
    between (lerp A B t) B X ->
    X = lerp A B t.
Proof.
  intros A B t X Ht HAB HCB.
  assert (HAB' : between (lerp A B 0) (lerp A B t) X).
  { rewrite lerp_0. exact HAB. }
  assert (HCB' : between (lerp A B t) (lerp A B 1) X).
  { rewrite lerp_1. exact HCB. }
  destruct (param_of_between_lerp A B 0 t X ltac:(lra) HAB')
    as [s1 [[Hs10 Hs11] Hx1]].
  destruct (param_of_between_lerp A B t 1 X ltac:(lra) HCB')
    as [s2 [[Hs20 Hs21] Hx2]].
  assert (Heq : lerp A B s1 = lerp A B s2).
  { rewrite <- Hx1, <- Hx2. reflexivity. }
  destruct (lerp_eq_cases A B s1 s2 Heq) as [Hs | HAB_eq].
  - assert (Hs1t : s1 = t) by lra.
    rewrite Hx1, Hs1t. reflexivity.
  - subst B. rewrite Hx1. unfold lerp. destruct A. f_equal; ring.
Qed.

Lemma edge_split_one_node_on_host :
  forall A B t, 0 < t < 1 -> between A B (lerp A B t).
Proof. intros. apply between_of_lerp; lra. Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Multi-node chain machinery.                                            *)
(* -------------------------------------------------------------------------- *)

Definition edge_nodes (A B : Point) (ts : list R) : list Point :=
  A :: map (lerp A B) ts ++ [B].

Fixpoint consecutive_pairs {A : Type} (l : list A) : list (A * A) :=
  match l with
  | [] => []
  | a :: t =>
      match t with
      | [] => []
      | b :: _ => (a, b) :: consecutive_pairs t
      end
  end.

Definition edge_pieces (A B : Point) (ts : list R) : list (Point * Point) :=
  consecutive_pairs (edge_nodes A B ts).

Definition edge_params (ts : list R) : list R := 0 :: ts ++ [1].

Fixpoint all_interior (ts : list R) : Prop :=
  match ts with
  | [] => True
  | t :: rest => 0 < t < 1 /\ all_interior rest
  end.

Definition sorted_lt (ts : list R) : Prop := Sorted Rlt ts.

Lemma sorted_lt_cons_inv :
  forall t ts, sorted_lt (t :: ts) -> sorted_lt ts.
Proof. intros t ts Hs. inversion Hs; subst. exact H1. Qed.

Lemma sorted_lt_hd :
  forall t t' ts, sorted_lt (t :: t' :: ts) -> t < t'.
Proof.
  intros t t' ts Hs.
  inversion Hs as [| ? ? Hs_tl Hhd]; subst.
  inversion Hhd as [| ? ? Hrel]; subst. exact Hrel.
Qed.

(* Under Sorted Rlt (t :: rest), every element of rest is > t. *)
Lemma sorted_lt_all_gt :
  forall t rest u, sorted_lt (t :: rest) -> In u rest -> t < u.
Proof.
  intros t rest. revert t.
  induction rest as [| w ws IH]; intros t u Hs Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin'].
    + rewrite <- Heq. apply sorted_lt_hd in Hs. exact Hs.
    + assert (Htw : t < w) by (apply sorted_lt_hd in Hs; exact Hs).
      assert (Hws : sorted_lt (w :: ws)) by (apply sorted_lt_cons_inv in Hs; exact Hs).
      assert (Hwu : w < u) by (apply (IH w u Hws Hin')).
      exact (Rlt_trans _ _ _ Htw Hwu).
Qed.

Lemma edge_pieces_nil :
  forall A B, edge_pieces A B [] = [(A, B)].
Proof. reflexivity. Qed.

Lemma edge_pieces_one :
  forall A B t,
    edge_pieces A B [t] = [(A, lerp A B t); (lerp A B t, B)].
Proof. reflexivity. Qed.

Lemma consecutive_pairs_app_snoc_one :
  forall {A : Type} (x : A) (ys : list A) (z : A),
    consecutive_pairs (x :: ys ++ [z]) =
    match ys with
    | [] => [(x, z)]
    | y :: ys' => (x, y) :: consecutive_pairs (y :: ys' ++ [z])
    end.
Proof.
  intros A x ys z.
  destruct ys as [| y ys']; reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Multi-node cover (parameter form, then geometric form).                *)
(* -------------------------------------------------------------------------- *)

(* Find consecutive parameters p <= s <= q in the chain tL :: ts ++ [1]. *)
Lemma edge_split_interval_from :
  forall tL ts s,
    tL < 1 ->
    all_interior ts ->
    sorted_lt ts ->
    (forall t, In t ts -> tL < t) ->
    tL <= s <= 1 ->
    exists t0 t1,
      In (t0, t1) (consecutive_pairs (tL :: ts ++ [1])) /\
      t0 <= s <= t1.
Proof.
  intros tL ts s HtL Hall Hs Hgt Hs_rng.
  revert tL s HtL Hall Hs Hgt Hs_rng.
  induction ts as [| t rest IH]; intros tL s HtL Hall Hs Hgt Hs_rng.
  - exists tL, 1. split.
    + simpl. left. reflexivity.
    + exact Hs_rng.
  - simpl in Hall. destruct Hall as [Ht Hall'].
    assert (HtL_t : tL < t) by (apply Hgt; left; reflexivity).
    destruct (Rle_dec s t) as [Hst | Hts].
    + exists tL, t. split.
      * simpl. left. reflexivity.
      * lra.
    + specialize (IH t s ltac:(lra) Hall' (sorted_lt_cons_inv _ _ Hs)).
      assert (Hgt' : forall u, In u rest -> t < u).
      { intros u Hin. exact (sorted_lt_all_gt t rest u Hs Hin). }
      specialize (IH Hgt' ltac:(lra)).
      destruct IH as [t0 [t1 [Hin Hs01]]].
      exists t0, t1. split; [| exact Hs01].
      (* In consecutive_pairs (t :: rest ++ [1]) ⇒ In in (tL :: t :: rest ++ [1]) *)
      simpl. right. exact Hin.
Qed.

Theorem edge_split_param_cover :
  forall ts s,
    all_interior ts ->
    sorted_lt ts ->
    0 <= s <= 1 ->
    exists t0 t1,
      In (t0, t1) (consecutive_pairs (edge_params ts)) /\
      t0 <= s <= t1.
Proof.
  intros ts s Hall Hs Hs01.
  unfold edge_params.
  apply (edge_split_interval_from 0 ts s); try assumption; try lra.
  intros t Hin.
  clear Hs. induction ts as [| u us IH]; [contradiction |].
  simpl in Hall. destruct Hall as [Hu Hall'].
  destruct Hin as [Heq | Hin'].
  - rewrite <- Heq. lra.
  - apply IH; assumption.
Qed.

(* HEADLINE: sorted interior nodes cover the host segment with pieces. *)
Theorem edge_split_cover :
  forall A B ts X,
    all_interior ts ->
    sorted_lt ts ->
    between A B X ->
    exists t0 t1,
      In (t0, t1) (consecutive_pairs (edge_params ts)) /\
      between (lerp A B t0) (lerp A B t1) X.
Proof.
  intros A B ts X Hall Hs HX.
  destruct (between_as_lerp A B X HX) as [s [Hs01 Hx]].
  destruct (edge_split_param_cover ts s Hall Hs Hs01) as [t0 [t1 [Hin Hs_int]]].
  exists t0, t1. split; [exact Hin |].
  rewrite Hx. apply between_lerp_of_param_interval.
  - lra.
  - exact Hs_int.
Qed.

(* Geometric packaging: pieces are consecutive edge_nodes. *)
Lemma edge_nodes_params :
  forall A B ts,
    edge_nodes A B ts = map (lerp A B) (edge_params ts).
Proof.
  intros A B ts.
  unfold edge_nodes, edge_params.
  simpl. rewrite map_app. simpl.
  rewrite lerp_0, lerp_1. reflexivity.
Qed.

Theorem edge_split_cover_pieces :
  forall A B ts X,
    all_interior ts ->
    sorted_lt ts ->
    between A B X ->
    exists P Q,
      In (P, Q) (edge_pieces A B ts) /\
      between P Q X.
Proof.
  intros A B ts X Hall Hs HX.
  destruct (edge_split_cover A B ts X Hall Hs HX) as [t0 [t1 [Hin Hbet]]].
  exists (lerp A B t0), (lerp A B t1). split; [| exact Hbet].
  unfold edge_pieces.
  rewrite edge_nodes_params.
  (* Need: In (t0,t1) consecutive_pairs params ⇒
            In (lerp t0, lerp t1) consecutive_pairs (map lerp params). *)
  assert (Hmap :
    forall ps,
      In (t0, t1) (consecutive_pairs ps) ->
      In (lerp A B t0, lerp A B t1) (consecutive_pairs (map (lerp A B) ps))).
  { intros ps. induction ps as [| p ps' IH].
    - simpl. intros [].
    - destruct ps' as [| p' ps''].
      + simpl. intros [].
      + simpl. intros [Heq | Hin'].
        * left. injection Heq as <- <-. reflexivity.
        * right. apply IH. exact Hin'. }
  apply Hmap. exact Hin.
Qed.

(* Adjacent pieces from a one-node split meet only at the node (reuse §3). *)
Theorem edge_split_one_pieces_cover_meet :
  forall A B t X,
    0 < t < 1 ->
    between A B X ->
    (between A (lerp A B t) X \/ between (lerp A B t) B X) /\
    (between A (lerp A B t) X -> between (lerp A B t) B X -> X = lerp A B t).
Proof.
  intros A B t X Ht HX.
  split.
  - apply edge_split_one_cover; assumption.
  - intros. apply edge_split_one_meet; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions edge_split_one_cover.
Print Assumptions edge_split_one_meet.
Print Assumptions edge_split_cover.
Print Assumptions edge_split_cover_pieces.
