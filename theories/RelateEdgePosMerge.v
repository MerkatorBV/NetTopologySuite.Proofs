(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgePosMerge
   ----------------------------------------------------------------------------
   Track 2 brick 5: non-strict edge-position order and equal-ratio merge.

   Brick 3 (`RelateEdgePosSort`) made `eplt` a strict total order and showed
   that a strictly sorted edge is real-monotone.  Real noding, however, admits
   *ties*: several crossing edges may hit the *same* rational position on a
   host edge (T-junctions, multi-geometry endpoints, co-located splits).  The
   decidable comparator already classifies those as `epcompare = Eq`; this
   module turns that hook into the merge step.

   - `epeq` — equal cross-products (same rational value); an `Equivalence`.
   - `eple` — non-strict order `eplt \/ epeq`; a total preorder.
   - Both agree with the true real order of `epval` (≤ / =).
   - `Sorted eple` is real-nondecreasing (monotone in ≤).
   - Computational `epdedup` collapses consecutive `Eq` runs, keeping the first
     representative of each equal-ratio block.
   - Payoff: if a list is `Sorted eple`, then `epdedup` is `Sorted eplt` —
     the strict noding chain after merging co-located nodes — and has no
     adjacent `epeq` pair.

   Order / merge algebra is pure `Z` (0 axioms); real agreement carries the
   classical-reals trio only.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok
   ========================================================================== *)

From Stdlib Require Import ZArith Lia Reals Lra List RelationClasses.
From Stdlib Require Import Sorting.Sorted.
From NTS.Proofs Require Import RelateEdgePosOrder RelateEdgePosSort.

Local Open Scope Z_scope.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Equal-ratio relation and the non-strict order.                         *)
(* -------------------------------------------------------------------------- *)

Definition epeq (a b : EPos) : Prop := pnum a * pden b = pnum b * pden a.
Definition eple (a b : EPos) : Prop := eplt a b \/ epeq a b.

Lemma epeq_refl : forall a, epeq a a.
Proof. intros a. unfold epeq. lia. Qed.

Lemma epeq_sym : forall a b, epeq a b -> epeq b a.
Proof. intros a b. unfold epeq. lia. Qed.

Lemma epeq_trans : forall a b c, epeq a b -> epeq b c -> epeq a c.
Proof.
  intros [na da Hda] [nb db Hdb] [nc dc Hdc].
  unfold epeq; simpl. intros H1 H2.
  assert (K1 : na * db * dc = nb * da * dc) by nia.
  assert (K2 : nb * dc * da = nc * db * da) by nia.
  nia.
Qed.

Instance epeq_Equivalence : Equivalence epeq.
Proof. constructor; [exact epeq_refl | exact epeq_sym | exact epeq_trans]. Qed.

Lemma eple_refl : forall a, eple a a.
Proof. intros a. right. apply epeq_refl. Qed.

Lemma eple_trans : forall a b c, eple a b -> eple b c -> eple a c.
Proof.
  intros a b c [Hab | Hab] [Hbc | Hbc].
  - left. exact (eplt_trans a b c Hab Hbc).
  - left. unfold eplt, epeq in *.
    destruct a as [na da Hda], b as [nb db Hdb], c as [nc dc Hdc]; simpl in *.
    nia.
  - left. unfold eplt, epeq in *.
    destruct a as [na da Hda], b as [nb db Hdb], c as [nc dc Hdc]; simpl in *.
    nia.
  - right. exact (epeq_trans a b c Hab Hbc).
Qed.

Instance eple_PreOrder : PreOrder eple.
Proof. constructor; [exact eple_refl | exact eple_trans]. Qed.

Lemma eple_total : forall a b, eple a b \/ eple b a.
Proof.
  intros a b.
  destruct (eplt_trichotomy a b) as [H | [H | H]].
  - left; left; exact H.
  - left; right; exact H.
  - right; left; exact H.
Qed.

Lemma epcompare_eple :
  forall a b,
    match epcompare a b with
    | Lt => eplt a b
    | Eq => epeq a b
    | Gt => eplt b a
    end.
Proof.
  intros a b. pose proof (epcompare_spec a b) as H.
  destruct (epcompare a b); exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Agreement with real ratio order.                                       *)
(* -------------------------------------------------------------------------- *)

Lemma epeq_iff_R : forall a b, epeq a b <-> (epval a = epval b)%R.
Proof.
  intros a b. unfold epeq, epval.
  symmetry. apply pos_eq_iff_cross; [apply pden_pos | apply pden_pos].
Qed.

Lemma eple_iff_R : forall a b, eple a b <-> (epval a <= epval b)%R.
Proof.
  intros a b. split.
  - intros [Hlt | Heq].
    + apply Rlt_le. apply eplt_iff_R. exact Hlt.
    + rewrite (proj1 (epeq_iff_R a b) Heq). apply Rle_refl.
  - intros Hle.
    destruct (Rle_lt_or_eq_dec (epval a) (epval b) Hle) as [Hlt | Heq].
    + left. apply eplt_iff_R. exact Hlt.
    + right. apply epeq_iff_R. exact Heq.
Qed.

Theorem sorted_eple_monotone :
  forall l, Sorted eple l -> Sorted (fun a b => (epval a <= epval b)%R) l.
Proof.
  apply Sorted_impl. intros x y H. apply eple_iff_R. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Adjacent equal-ratio free ⇒ strict Sorted.                             *)
(* -------------------------------------------------------------------------- *)

Fixpoint NoAdjEpeq (l : list EPos) : Prop :=
  match l with
  | [] => True
  | a :: t =>
      match t with
      | [] => True
      | b :: _ => ~ epeq a b /\ NoAdjEpeq t
      end
  end.

Lemma Sorted_eple_NoAdj_eplt :
  forall l, Sorted eple l -> NoAdjEpeq l -> Sorted eplt l.
Proof.
  intros l Hs.
  induction Hs as [| a l Hstail IH Hhd].
  - intros _. constructor.
  - intros Hna. constructor.
    + destruct l as [| b t]; [constructor | apply IH; apply Hna].
    + destruct l as [| b t]; [constructor |].
      simpl in Hna. destruct Hna as [Hne _].
      inversion Hhd as [| b' t' Hrel]; subst. constructor.
      destruct Hrel as [Hlt | Heq]; [exact Hlt | exfalso; apply Hne; exact Heq].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Computational merge (structural: keep last of each Eq run).            *)
(* -------------------------------------------------------------------------- *)

(* Structurally recursive merge: keep the *last* of each consecutive equal-ratio
   block (compare head against head of already-deduped tail).  On a nondecreasing
   list this is the unique-value chain; Sorted-eplt payoff is identical to
   keeping the first. *)
Fixpoint epdedup (l : list EPos) : list EPos :=
  match l with
  | [] => []
  | a :: t =>
      match epdedup t with
      | [] => [a]
      | b :: m =>
          match epcompare a b with
          | Eq => b :: m
          | Lt => a :: b :: m
          | Gt => a :: b :: m
          end
      end
  end.

Lemma Sorted_eple_cons_inv :
  forall a l, Sorted eple (a :: l) -> Sorted eple l.
Proof.
  intros a l Hs.
  inversion Hs as [| xa xl Hs_tl Hhd]; subst. exact Hs_tl.
Qed.

Lemma HdRel_eple_cons :
  forall a b l, Sorted eple (a :: b :: l) -> eple a b.
Proof.
  intros a b l Hs.
  inversion Hs as [| xa xl Hs_tl Hhd]; subst.
  inversion Hhd as [| xb xt Hrel]; subst. exact Hrel.
Qed.

Lemma Sorted_eple_all_ge :
  forall a l x, Sorted eple (a :: l) -> In x l -> eple a x.
Proof.
  intros a l. revert a.
  induction l as [| b t IH]; intros a x Hs Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + rewrite <- Heq. exact (HdRel_eple_cons a b t Hs).
    + apply (eple_trans a b x).
      * exact (HdRel_eple_cons a b t Hs).
      * apply (IH b x).
        -- exact (Sorted_eple_cons_inv a (b :: t) Hs).
        -- exact Hin.
Qed.

Lemma eplt_of_epcompare_Lt :
  forall a b, epcompare a b = Lt -> eplt a b.
Proof.
  intros a b E. pose proof (epcompare_eple a b) as H. rewrite E in H. exact H.
Qed.

Lemma epeq_of_epcompare_Eq :
  forall a b, epcompare a b = Eq -> epeq a b.
Proof.
  intros a b E. pose proof (epcompare_eple a b) as H. rewrite E in H. exact H.
Qed.

Lemma not_epeq_of_epcompare_Lt :
  forall a b, epcompare a b = Lt -> ~ epeq a b.
Proof.
  intros a b E Heq.
  pose proof (eplt_of_epcompare_Lt a b E) as Hlt.
  unfold eplt, epeq in *. lia.
Qed.

Lemma not_epeq_of_epcompare_Gt :
  forall a b, epcompare a b = Gt -> ~ epeq a b.
Proof.
  intros a b E Heq.
  pose proof (epcompare_eple a b) as H. rewrite E in H.
  unfold eplt, epeq in *. lia.
Qed.

(* Every element of epdedup l is an element of l. *)
Lemma epdedup_In : forall l x, In x (epdedup l) -> In x l.
Proof.
  induction l as [| a t IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct (epdedup t) as [| b m] eqn:Hd.
    + destruct Hin as [Heq | Hfalse]; [left; exact Heq | contradiction].
    + destruct (epcompare a b).
      * (* Eq: result b::m *)
        right. apply (IH x). exact Hin.
      * (* Lt: result a::b::m *)
        destruct Hin as [Heq | Hin'].
        -- left. exact Heq.
        -- right. apply (IH x). exact Hin'.
      * (* Gt: result a::b::m *)
        destruct Hin as [Heq | Hin'].
        -- left. exact Heq.
        -- right. apply (IH x). exact Hin'.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Payoff: dedup of a nondecreasing list is strictly increasing.          *)
(* -------------------------------------------------------------------------- *)

Lemma epdedup_Sorted_eple :
  forall l, Sorted eple l -> Sorted eple (epdedup l).
Proof.
  intros l Hs.
  induction Hs as [| a l Hs_tl IH Hhd].
  - simpl. constructor.
  - simpl.
    destruct (epdedup l) as [| b m] eqn:Hd.
    + constructor; [constructor | constructor].
    + destruct (epcompare a b) eqn:E.
      * (* Eq: result b::m *)
        exact IH.
      * (* Lt: a :: b :: m *)
        constructor.
        -- exact IH.
        -- constructor. left. exact (eplt_of_epcompare_Lt a b E).
      * (* Gt: impossible under Sorted eple *)
        exfalso.
        assert (Hin : In b l).
        { apply epdedup_In. rewrite Hd. left. reflexivity. }
        assert (Hs_full : Sorted eple (a :: l)).
        { constructor; [exact Hs_tl | exact Hhd]. }
        pose proof (Sorted_eple_all_ge a l b Hs_full Hin) as Hle.
        pose proof (epcompare_eple a b) as Hc. rewrite E in Hc.
        destruct Hle as [Hlt | Heq]; unfold eplt, epeq in *; lia.
Qed.

Lemma epdedup_NoAdjEpeq :
  forall l, NoAdjEpeq (epdedup l).
Proof.
  intros l.
  induction l as [| a t IH].
  - simpl. exact I.
  - simpl.
    destruct (epdedup t) as [| b m] eqn:Hd.
    + exact I.
    + destruct (epcompare a b) eqn:E.
      * (* Eq: NoAdj on b::m *)
        exact IH.
      * (* Lt: ~epeq a b /\ NoAdj (b::m) *)
        split.
        -- apply (not_epeq_of_epcompare_Lt a b E).
        -- exact IH.
      * (* Gt *)
        split.
        -- apply (not_epeq_of_epcompare_Gt a b E).
        -- exact IH.
Qed.

Theorem epdedup_sorted_eplt :
  forall l, Sorted eple l -> Sorted eplt (epdedup l).
Proof.
  intros l Hs.
  apply Sorted_eple_NoAdj_eplt.
  - apply epdedup_Sorted_eple. exact Hs.
  - apply epdedup_NoAdjEpeq.
Qed.

Theorem epdedup_monotone :
  forall l,
    Sorted eple l ->
    Sorted (fun a b => (epval a < epval b)%R) (epdedup l).
Proof.
  intros l Hs.
  apply sorted_eplt_monotone.
  apply epdedup_sorted_eplt.
  exact Hs.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions epeq_trans.
Print Assumptions eple_trans.
Print Assumptions eple_total.
Print Assumptions sorted_eple_monotone.
Print Assumptions epdedup_sorted_eplt.
Print Assumptions epdedup_monotone.
