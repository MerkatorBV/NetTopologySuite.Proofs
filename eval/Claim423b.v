(* ============================================================================
   nts-eval micro unit — claimId 423-b (GREEN)
   Red planted 2026-08-02 (47ef69d) · Green closed 2026-08-02
   ----------------------------------------------------------------------------
   DISCRETE FRECHET DISTANCE on finite point lists (Eiter & Mannila 1994;
   Meinert arXiv:2404.05708 Theorem 1 is the fold/scan reformulation of
   the same recurrence): the "two frogs" leash value

       dF(A,B) defined by the head recurrence
         dF([a],[b])       = d(a,b)
         dF(a::A',[b])     = max(d(a,b), dF(A',[b]))
         dF([a],b::B')     = max(d(a,b), dF([a],B'))
         dF(a::A',b::B')   = max(d(a,b),
                                 min(dF(A',b::B'), dF(a::A',B'), dF(A',B')))

   equals the MIN over MONOTONE COUPLINGS of the max pairwise leash:
   both frogs start on the two heads, each step advances frog 1, frog 2,
   or both, and both must end on the two last stones.  Squared-distance
   convention (corpus rational-witness discipline; max/min commute with
   monotone squaring on nonnegatives, so dF_sq = (metric dF)^2).

   The corpus already carries the KERNEL algebra and shape-fixed
   unrollings (theories/FrechetMaxmin.v: maxmin invariants, 2x2 closed
   form, padding invariance) -- but the general list DP and its coupling
   spec were explicitly parked as this RED claim
   (docs/hausdorff-penetration.md, honest scope).  That is the gap.

   GREEN.  The headline spec is stated (`discrete_frechet_claim`) and
   CLOSED in this unit (`discrete_frechet_min_coupling`, Qed).  The spec
   pins the computed value from both sides on nonempty lists:
     (lower bound) EVERY monotone coupling's max leash is >= dF(A,B);
     (attain)      SOME monotone coupling realises exactly dF(A,B).
   Together: dF is exactly the min-over-couplings max leash -- the
   Eiter-Mannila / Meinert Theorem-1-grade correctness of the
   recurrence.  Proof shape: the lower bound is induction on the
   coupling DERIVATION (each constructor lands on one of the
   recurrence's min branches); the attain half is a nested list
   induction (outer on A quantified over B, inner on B) that BUILDS the
   optimal coupling, selecting the min branch by Rle_dec and prefixing
   the corresponding constructor.  Production home:
   `theories/FrechetDiscrete.v` over the corpus Point/dist_sq
   vocabulary, same WITNESS tag.  Red history: claim planted 2026-08-02
   (47ef69d) with only the witness pins Qed; Green closed it the same
   day.

   What IS Qed here: rational witness pins fixing the intended
   semantics --
     - identical 2-stone curves have leash 0, and the diagonal coupling
       witnessing it is exhibited THROUGH the inductive (non-vacuity of
       the coupling relation and of the attain direction);
     - the REVERSED 2-stone curve has leash_sq 9 although the vertex
       SETS coincide (every set distance, e.g. 423-a's directed
       Hausdorff, is 0): the coupling order is load-bearing;
     - the crossing pairing that would give 0 on the reversed pair is
       PROVED NOT to be a coupling (monotonicity kills it);
     - the 423-a asymmetric witness [(0,0)] vs [(0,2);(3,0)] has
       dF_sq = 9 > 4 = directed-Hausdorff_sq: the lone frog must visit
       BOTH stones, so Frechet dominates Hausdorff on the same data.

   WITNESS claimId: 423-b
   topic: metric
   Lemma (Green target): discrete_frechet_min_coupling
   ========================================================================== *)

(* WITNESS {"claimId":"423-b","topic":"metric","lemma":"discrete_frechet_min_coupling","title":"Discrete Frechet = min over monotone couplings of the max leash"} *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
Local Open Scope R_scope.

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

(* -------------------------------------------------------------------------- *)
(* The Eiter-Mannila recurrence, head form (nested structural recursion:      *)
(* outer on A, inner on B).  The [] sentinels are outside the claim's         *)
(* domain (nonempty lists required).                                          *)
(* -------------------------------------------------------------------------- *)

Fixpoint dF_sq (A : list Point) {struct A} : list Point -> R :=
  match A with
  | [] => fun _ => 0
  | a :: A' =>
      fix dFB (B : list Point) {struct B} : R :=
        match B with
        | [] => 0
        | b :: B' =>
            match A', B' with
            | [], [] => dist_sq a b
            | [], _ :: _ => Rmax (dist_sq a b) (dFB B')
            | _ :: _, [] => Rmax (dist_sq a b) (dF_sq A' [b])
            | _ :: _, _ :: _ =>
                Rmax (dist_sq a b)
                     (Rmin (Rmin (dF_sq A' B) (dFB B')) (dF_sq A' B'))
            end
        end
  end.

(* -------------------------------------------------------------------------- *)
(* Monotone couplings: both frogs start on the heads; each emitted pair is    *)
(* followed by advancing frog 1, frog 2, or both; both end on the last        *)
(* stones.  (Eiter-Mannila's order-preserving surjective pairing.)            *)
(* -------------------------------------------------------------------------- *)

Inductive coupling : list Point -> list Point -> list (Point * Point) -> Prop :=
| cpl_last : forall a b,
    coupling [a] [b] [(a, b)]
| cpl_advA : forall a x A' b B c,
    coupling (x :: A') (b :: B) c ->
    coupling (a :: x :: A') (b :: B) ((a, b) :: c)
| cpl_advB : forall a A b y B' c,
    coupling (a :: A) (y :: B') c ->
    coupling (a :: A) (b :: y :: B') ((a, b) :: c)
| cpl_advAB : forall a x A' b y B' c,
    coupling (x :: A') (y :: B') c ->
    coupling (a :: x :: A') (b :: y :: B') ((a, b) :: c).

(* The leash a coupling needs: the max pairwise squared distance. *)
Fixpoint max_pair_dist_sq (c : list (Point * Point)) : R :=
  match c with
  | [] => 0
  | [(a, b)] => dist_sq a b
  | (a, b) :: c' => Rmax (dist_sq a b) (max_pair_dist_sq c')
  end.

(* -------------------------------------------------------------------------- *)
(* The 423-b claim (RED: stated, not closed).                                 *)
(* dF_sq A B is exactly the attained min-over-couplings max leash:            *)
(*   (lower bound) no monotone coupling beats it;                             *)
(*   (attain)      some monotone coupling realises it.                        *)
(* -------------------------------------------------------------------------- *)

Definition discrete_frechet_claim : Prop :=
  forall (A B : list Point),
    A <> nil ->
    B <> nil ->
    (forall c, coupling A B c -> dF_sq A B <= max_pair_dist_sq c) /\
    (exists c, coupling A B c /\ max_pair_dist_sq c = dF_sq A B).

(* GREEN: the claim is closed here (self-contained) and mirrored in
   production over the corpus Point/dist_sq vocabulary
   (theories/FrechetDiscrete.v, same WITNESS tag). *)

(* -------------------------------------------------------------------------- *)
(* Green infrastructure.                                                      *)
(* -------------------------------------------------------------------------- *)

(* One-step unfolding equations (by conversion) for the four nonempty
   shapes of the recurrence. *)
Lemma dF_step_11 : forall a b, dF_sq [a] [b] = dist_sq a b.
Proof. reflexivity. Qed.

Lemma dF_step_1n : forall a b y B',
    dF_sq [a] (b :: y :: B') = Rmax (dist_sq a b) (dF_sq [a] (y :: B')).
Proof. reflexivity. Qed.

Lemma dF_step_n1 : forall a x A' b,
    dF_sq (a :: x :: A') [b] = Rmax (dist_sq a b) (dF_sq (x :: A') [b]).
Proof. reflexivity. Qed.

Lemma dF_step_nn : forall a x A' b y B',
    dF_sq (a :: x :: A') (b :: y :: B')
    = Rmax (dist_sq a b)
           (Rmin (Rmin (dF_sq (x :: A') (b :: y :: B'))
                       (dF_sq (a :: x :: A') (y :: B')))
                 (dF_sq (x :: A') (y :: B'))).
Proof. reflexivity. Qed.

(* Couplings are never empty (every constructor emits a head pair). *)
Lemma coupling_c_nonempty : forall A B c, coupling A B c -> c <> [].
Proof. intros A B c H; destruct H; discriminate. Qed.

(* Opening the leash aggregate on a nonempty tail. *)
Lemma maxleash_cons : forall a b c,
    c <> [] ->
    max_pair_dist_sq ((a, b) :: c)
    = Rmax (dist_sq a b) (max_pair_dist_sq c).
Proof. intros a b c Hne. destruct c; [ congruence | reflexivity ]. Qed.

(* -------------------------------------------------------------------------- *)
(* Lower bound: no monotone coupling beats the recurrence.  Induction on      *)
(* the coupling derivation; each constructor lands on one of the             *)
(* recurrence's min branches.                                                *)
(* -------------------------------------------------------------------------- *)

Lemma dF_le_coupling : forall A B c,
    coupling A B c -> dF_sq A B <= max_pair_dist_sq c.
Proof.
  intros A B c H. induction H.
  - (* cpl_last: both sides are dist_sq a b *)
    apply Rle_refl.
  - (* cpl_advA: frog 1 advances; branch u of the min *)
    rewrite (maxleash_cons a b c) by (eapply coupling_c_nonempty; eauto).
    destruct B as [ | y B0 ].
    + rewrite dF_step_n1. apply Rle_max_compat_l. exact IHcoupling.
    + rewrite dF_step_nn. apply Rle_max_compat_l.
      eapply Rle_trans; [ apply Rmin_l | ].
      eapply Rle_trans; [ apply Rmin_l | ]. exact IHcoupling.
  - (* cpl_advB: frog 2 advances; branch v of the min *)
    rewrite (maxleash_cons a b c) by (eapply coupling_c_nonempty; eauto).
    destruct A as [ | x A1 ].
    + rewrite dF_step_1n. apply Rle_max_compat_l. exact IHcoupling.
    + rewrite dF_step_nn. apply Rle_max_compat_l.
      eapply Rle_trans; [ | exact IHcoupling ].
      eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ].
  - (* cpl_advAB: both advance; branch w of the min *)
    rewrite (maxleash_cons a b c) by (eapply coupling_c_nonempty; eauto).
    rewrite dF_step_nn. apply Rle_max_compat_l.
    eapply Rle_trans; [ apply Rmin_r | ]. exact IHcoupling.
Qed.

(* -------------------------------------------------------------------------- *)
(* Attainment: build the optimal coupling.  Outer induction on A quantified   *)
(* over B, inner induction on B; at each doubly-long shape the min branch is  *)
(* selected by Rle_dec and the matching constructor prefixed.                 *)
(* -------------------------------------------------------------------------- *)

Lemma dF_attained : forall A B,
    A <> [] -> B <> [] ->
    exists c, coupling A B c /\ max_pair_dist_sq c = dF_sq A B.
Proof.
  induction A as [ | a A' IHA ]; intros B HA HB; [ congruence | ].
  revert HB. induction B as [ | b B' IHB ]; intros HB; [ congruence | ].
  destruct A' as [ | x A'' ]; destruct B' as [ | y B'' ].
  - (* [a] vs [b]: the single-pair coupling *)
    exists [(a, b)]. split; [ apply cpl_last | reflexivity ].
  - (* [a] vs b::y::B'': frog 2 advances *)
    destruct IHB as [c' [Hc' Heq']]; [ discriminate | ].
    exists ((a, b) :: c'). split.
    + apply cpl_advB. exact Hc'.
    + rewrite (maxleash_cons a b c') by (eapply coupling_c_nonempty; eauto).
      rewrite Heq'. rewrite dF_step_1n. reflexivity.
  - (* a::x::A'' vs [b]: frog 1 advances *)
    destruct (IHA [b]) as [c' [Hc' Heq']]; [ discriminate | discriminate | ].
    exists ((a, b) :: c'). split.
    + apply cpl_advA. exact Hc'.
    + rewrite (maxleash_cons a b c') by (eapply coupling_c_nonempty; eauto).
      rewrite Heq'. rewrite dF_step_n1. reflexivity.
  - (* both long: select the min branch *)
    destruct (IHA (b :: y :: B'')) as [cu [Hcu Hequ]];
      [ discriminate | discriminate | ].
    destruct IHB as [cv [Hcv Heqv]]; [ discriminate | ].
    destruct (IHA (y :: B'')) as [cw [Hcw Heqw]];
      [ discriminate | discriminate | ].
    set (u := dF_sq (x :: A'') (b :: y :: B'')) in *.
    set (v := dF_sq (a :: x :: A'') (y :: B'')) in *.
    set (w := dF_sq (x :: A'') (y :: B'')) in *.
    destruct (Rle_dec (Rmin u v) w) as [Hw | Hw].
    + destruct (Rle_dec u v) as [Huv | Huv].
      * (* min = u: frog 1 advances *)
        exists ((a, b) :: cu). split; [ apply cpl_advA; exact Hcu | ].
        rewrite (maxleash_cons a b cu)
          by (eapply coupling_c_nonempty; eauto).
        rewrite Hequ. rewrite dF_step_nn.
        fold u v w. rewrite (Rmin_left _ _ Hw), (Rmin_left _ _ Huv).
        reflexivity.
      * (* min = v: frog 2 advances *)
        apply Rnot_le_lt in Huv.
        exists ((a, b) :: cv). split; [ apply cpl_advB; exact Hcv | ].
        rewrite (maxleash_cons a b cv)
          by (eapply coupling_c_nonempty; eauto).
        rewrite Heqv. rewrite dF_step_nn.
        fold u v w. rewrite (Rmin_left _ _ Hw).
        rewrite (Rmin_right u v) by lra.
        reflexivity.
    + (* min = w: both advance *)
      apply Rnot_le_lt in Hw.
      exists ((a, b) :: cw). split; [ apply cpl_advAB; exact Hcw | ].
      rewrite (maxleash_cons a b cw)
        by (eapply coupling_c_nonempty; eauto).
      rewrite Heqw. rewrite dF_step_nn.
      fold u v w. rewrite (Rmin_right (Rmin u v) w); [ reflexivity | lra ].
Qed.

(* The 423-b headline. *)
Lemma discrete_frechet_min_coupling : discrete_frechet_claim.
Proof.
  unfold discrete_frechet_claim. intros A B HA HB. split.
  - intros c Hc. apply dF_le_coupling. exact Hc.
  - apply dF_attained; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Rational witness pins (Qed at Red).                                        *)
(* -------------------------------------------------------------------------- *)

(* Concrete evaluations reduce to Rmax/Rmin on rational literals; opening
   the underlying Rle_dec closes every branch by lra. *)
Ltac pin_crunch :=
  unfold Rmax, Rmin;
  repeat match goal with
         | |- context [Rle_dec ?x ?y] => destruct (Rle_dec x y)
         end;
  lra.

Definition pA : Point := mkPoint 0 0.
Definition pB : Point := mkPoint 3 0.

(* Identical 2-stone curves: leash 0, via the diagonal coupling. *)
Lemma wf_identical_zero : dF_sq [pA; pB] [pA; pB] = 0.
Proof.
  cbn. unfold dist_sq, pA, pB. cbn.
  pin_crunch.
Qed.

(* The diagonal coupling EXISTS as a derivation of the inductive, and its
   leash is 0 -- the attain direction is non-vacuous at this instance. *)
Lemma wf_diagonal_coupling :
  coupling [pA; pB] [pA; pB] [(pA, pA); (pB, pB)] /\
  max_pair_dist_sq [(pA, pA); (pB, pB)] = 0.
Proof.
  split.
  - apply cpl_advAB. apply cpl_last.
  - cbn. unfold dist_sq, pA, pB. cbn.
    pin_crunch.
Qed.

(* REVERSAL: same vertex set, leash_sq 9 -- the coupling ORDER is
   load-bearing (any set distance on these lists is 0). *)
Lemma wf_reversed_nine : dF_sq [pA; pB] [pB; pA] = 9.
Proof.
  cbn. unfold dist_sq, pA, pB. cbn.
  pin_crunch.
Qed.

(* MISMATCH PROBE: the crossing pairing that WOULD give leash 0 on the
   reversed pair is not a coupling -- monotonicity kills it (its head
   pair is not the pair of heads). *)
Lemma wf_crossing_not_coupling :
  ~ coupling [pA; pB] [pB; pA] [(pA, pA); (pB, pB)].
Proof.
  unfold pA, pB. intros H.
  (* every constructor forces the emitted head pair to be the pair of
     heads ((0,0),(3,0)); the crossing pairing's head is ((0,0),(0,0)),
     so each branch carries a coordinate clash 3 = 0. *)
  inversion H; subst;
    repeat match goal with
           | Heq : mkPoint _ _ = mkPoint _ _ |- _ =>
               injection Heq; clear Heq; intros
           end;
    lra.
Qed.

(* FRECHET DOMINATES HAUSDORFF on the 423-a asymmetric witness: the lone
   frog must visit BOTH stones, so dF_sq = 9 while the directed
   Hausdorff_sq of the same lists is 4 (eval/Claim423a.v pins). *)
Lemma wf_lone_frog_visits_all :
  dF_sq [mkPoint 0 0] [mkPoint 0 2; mkPoint 3 0] = 9 /\ (4 < 9)%R.
Proof.
  split; [ | lra ].
  cbn. unfold dist_sq. cbn.
  pin_crunch.
Qed.
