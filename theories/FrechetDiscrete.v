(* ============================================================================
   NetTopologySuite.Proofs.FrechetDiscrete
   ----------------------------------------------------------------------------
   GREEN for micro-claim 423-b: the DISCRETE FRECHET DISTANCE computed by
   the Eiter-Mannila recurrence is EXACTLY the min over monotone
   couplings of the max pairwise leash.

   Eiter & Mannila (1994) define the discrete Frechet distance of two
   polygonal curves by the dynamic program Meinert (arXiv:2404.05708)
   reformulates recursion-free (its eq (1)); JTS-adjacent trajectory
   analytics (vessel-route clustering, map matching) consume exactly
   this value on GNSS vertex chains.  The corpus already carries the
   kernel algebra and shape-fixed unrollings (FrechetMaxmin.v); what was
   missing -- and parked as the 423-b RED claim -- is the general list
   DP together with its TWO-FROGS SEMANTICS: both frogs start on the
   heads, each step advances frog 1, frog 2, or both, both end on the
   last stones, and the value is the cheapest max leash over all such
   walks.

   Proved here (squared-distance convention; max/min commute with
   monotone squaring on nonnegatives, so dF_sq = (metric dF)^2):

     (lower bound / dF_le_coupling)  every monotone coupling's max
       leash is >= dF_sq A B -- induction on the coupling DERIVATION;
       each constructor lands on one of the recurrence's min branches;

     (attain / dF_attained)  some monotone coupling realises dF_sq A B
       -- nested list induction (outer on A quantified over B, inner on
       B) that BUILDS the optimal walk, selecting the min branch by
       Rle_dec and prefixing the matching constructor;

     (headline / discrete_frechet_min_coupling)  the conjunction, on
       nonempty lists: the recurrence computes the two-frogs semantics.

     (nonnegativity)  dF_sq is a leash value: 0 <= dF_sq A B.

   Mirrors eval/Claim423b.v (same WITNESS tag), which carries the
   self-contained version plus the rational pins: identical curves 0
   with the diagonal coupling exhibited; reversal 9 though the vertex
   sets coincide; the crossing pairing proved NOT a coupling; and
   Frechet dominating the directed Hausdorff (9 > 4) on 423-a's own
   witness.

   WITNESS claimId: 423-b
   topic: metric
   Lemma: discrete_frechet_min_coupling

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance.
Import ListNotations.
Open Scope R_scope.

(* WITNESS {"claimId":"423-b","topic":"metric","lemma":"discrete_frechet_min_coupling","title":"Discrete Frechet = min over monotone couplings of the max leash"} *)

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
(* Proof infrastructure.  dF_sq A B is exactly the attained                   *)
(* min-over-couplings max leash: (lower bound) no monotone coupling beats     *)
(* it; (attain) some monotone coupling realises it.                           *)
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

(* -------------------------------------------------------------------------- *)
(* The 423-b headline: the recurrence computes the two-frogs semantics.       *)
(* -------------------------------------------------------------------------- *)

Theorem discrete_frechet_min_coupling :
  forall (A B : list Point),
    A <> nil ->
    B <> nil ->
    (forall c, coupling A B c -> dF_sq A B <= max_pair_dist_sq c) /\
    (exists c, coupling A B c /\ max_pair_dist_sq c = dF_sq A B).
Proof.
  intros A B HA HB. split.
  - intros c Hc. apply dF_le_coupling. exact Hc.
  - apply dF_attained; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Nonnegativity: a leash value.                                              *)
(* -------------------------------------------------------------------------- *)

Lemma discrete_frechet_sq_nonneg : forall A B, 0 <= dF_sq A B.
Proof.
  intros [ | a A' ] [ | b B' ]; try apply Rle_refl.
  destruct A' as [ | x A'' ]; destruct B' as [ | y B'' ].
  - rewrite dF_step_11. apply dist_sq_nonneg.
  - rewrite dF_step_1n.
    eapply Rle_trans; [ apply (dist_sq_nonneg a b) | apply Rmax_l ].
  - rewrite dF_step_n1.
    eapply Rle_trans; [ apply (dist_sq_nonneg a b) | apply Rmax_l ].
  - rewrite dF_step_nn.
    eapply Rle_trans; [ apply (dist_sq_nonneg a b) | apply Rmax_l ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions discrete_frechet_min_coupling.
Print Assumptions discrete_frechet_sq_nonneg.
