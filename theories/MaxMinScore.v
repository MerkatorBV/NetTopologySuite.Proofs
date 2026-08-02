(* ============================================================================
   NetTopologySuite.Proofs.MaxMinScore
   ----------------------------------------------------------------------------
   The score-agnostic MAX-MIN aggregation layer shared by the discrete
   metric rungs of epic #423: for an abstract score on point pairs,
       min_score_to a B   = min over b in B of score a b
       max_min_score A B  = max over a in A of min_score_to a B
   with the four aggregation facts (inner min is an attained lower
   bound, outer max is an attained upper bound), the one-step
   conversion equations that open the cons cases without disturbing
   folded inner calls, and nonnegativity under a nonnegative score.

   None of these facts uses any property of the score function beyond
   (for the last two) nonnegativity -- the observation that let the
   423-a Green's inductions be proved once and instantiated at BOTH the
   squared and the unsquared metric:
     - HausdorffDiscrete.v      (score := dist_sq, the 423-a surface)
     - HausdorffMetricInstance.v (score := dist, where the triangle
       inequality lives and the HKR metric closes).

   Extracted verbatim from HausdorffMetricInstance.v once #431/#432
   both landed on main (the flagged post-merge refactor): one source of
   truth for the layer, statements of all downstream lemmas unchanged.

   topic: metric

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

Section GenericMaxMin.

  Variable score : Point -> Point -> R.

  Fixpoint min_score_to (a : Point) (B : list Point) : R :=
    match B with
    | [] => 0
    | [b] => score a b
    | b :: B' => Rmin (score a b) (min_score_to a B')
    end.

  Fixpoint max_min_score (A B : list Point) : R :=
    match A with
    | [] => 0
    | [a] => min_score_to a B
    | a :: A' => Rmax (min_score_to a B) (max_min_score A' B)
    end.

  Lemma min_score_to_step : forall a b0 b1 B'',
      min_score_to a (b0 :: b1 :: B'')
      = Rmin (score a b0) (min_score_to a (b1 :: B'')).
  Proof. reflexivity. Qed.

  Lemma max_min_score_step : forall a0 a1 A'' B,
      max_min_score (a0 :: a1 :: A'') B
      = Rmax (min_score_to a0 B) (max_min_score (a1 :: A'') B).
  Proof. reflexivity. Qed.

  Lemma min_score_to_le : forall a B b,
      In b B -> min_score_to a B <= score a b.
  Proof.
    intros a B. induction B as [ | b0 B' IH ]; intros b Hin.
    - destruct Hin.
    - destruct Hin as [-> | Hin].
      + destruct B' as [ | b1 B'' ]; [ apply Rle_refl | ].
        rewrite min_score_to_step. apply Rmin_l.
      + destruct B' as [ | b1 B'' ]; [ destruct Hin | ].
        rewrite min_score_to_step.
        eapply Rle_trans; [ apply Rmin_r | ]. apply IH. exact Hin.
  Qed.

  Lemma min_score_to_attained : forall a B,
      B <> nil -> exists b, In b B /\ min_score_to a B = score a b.
  Proof.
    intros a B. induction B as [ | b0 B' IH ]; intros Hne.
    - congruence.
    - destruct B' as [ | b1 B'' ].
      + exists b0. split; [ left; reflexivity | reflexivity ].
      + destruct IH as [b [Hb Heq]]; [ discriminate | ].
        rewrite min_score_to_step.
        destruct (Rle_dec (score a b0) (min_score_to a (b1 :: B'')))
          as [Hle | Hgt].
        * exists b0. split; [ left; reflexivity | ].
          rewrite Rmin_left; [ reflexivity | exact Hle ].
        * apply Rnot_le_lt in Hgt.
          exists b. split; [ right; exact Hb | ].
          rewrite Rmin_right; [ exact Heq | lra ].
  Qed.

  Lemma max_min_score_ge_component : forall A B a,
      In a A -> min_score_to a B <= max_min_score A B.
  Proof.
    intros A B. induction A as [ | a0 A' IH ]; intros a Hin.
    - destruct Hin.
    - destruct Hin as [-> | Hin].
      + destruct A' as [ | a1 A'' ]; [ apply Rle_refl | ].
        rewrite max_min_score_step. apply Rmax_l.
      + destruct A' as [ | a1 A'' ]; [ destruct Hin | ].
        rewrite max_min_score_step.
        eapply Rle_trans; [ apply IH; exact Hin | apply Rmax_r ].
  Qed.

  Lemma max_min_score_attained : forall A B,
      A <> nil ->
      exists a, In a A /\ max_min_score A B = min_score_to a B.
  Proof.
    intros A B. induction A as [ | a0 A' IH ]; intros Hne.
    - congruence.
    - destruct A' as [ | a1 A'' ].
      + exists a0. split; [ left; reflexivity | reflexivity ].
      + destruct IH as [a [Ha Heq]]; [ discriminate | ].
        rewrite max_min_score_step.
        destruct (Rle_dec (max_min_score (a1 :: A'') B)
                          (min_score_to a0 B)) as [Hle | Hgt].
        * exists a0. split; [ left; reflexivity | ].
          rewrite Rmax_left; [ reflexivity | exact Hle ].
        * apply Rnot_le_lt in Hgt.
          exists a. split; [ right; exact Ha | ].
          rewrite Rmax_right; [ exact Heq | lra ].
  Qed.

  Hypothesis score_nonneg : forall p q, 0 <= score p q.

  Lemma min_score_to_nonneg : forall a B, 0 <= min_score_to a B.
  Proof.
    intros a B. induction B as [ | b0 B' IH ].
    - apply Rle_refl.
    - destruct B' as [ | b1 B'' ]; [ apply score_nonneg | ].
      rewrite min_score_to_step.
      apply Rmin_glb; [ apply score_nonneg | exact IH ].
  Qed.

  Lemma max_min_score_nonneg : forall A B, 0 <= max_min_score A B.
  Proof.
    intros A B. induction A as [ | a0 A' IH ].
    - apply Rle_refl.
    - destruct A' as [ | a1 A'' ]; [ apply min_score_to_nonneg | ].
      rewrite max_min_score_step.
      eapply Rle_trans; [ apply (min_score_to_nonneg a0 B) | apply Rmax_l ].
  Qed.

End GenericMaxMin.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions max_min_score_attained.
Print Assumptions max_min_score_nonneg.
