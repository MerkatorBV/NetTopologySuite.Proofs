(* ============================================================================
   NetTopologySuite.Proofs.HausdorffDiscrete
   ----------------------------------------------------------------------------
   GREEN for micro-claim 423-a: the DIRECTED DISCRETE HAUSDORFF value on
   finite point lists is the ATTAINED MAX-MIN.

   Huttenlocher-Klanderman-Rucklidge (IEEE PAMI 1993) eq (2), the h(A,B)
   JTS/NTS DiscreteHausdorffDistance computes:
       h(A,B) = max_{a in A} min_{b in B} d(a,b).
   Squared-distance convention (corpus rational-witness discipline; sqrt
   is monotone, so the max-min structure is identical in either
   reading).  The characterising spec proved here pins the computed
   value h = directed_hausdorff_sq A B from BOTH sides on nonempty
   lists:
     (cover)  every a in A has some b in B with dist_sq a b <= h  --
              h is big enough: no point of A is farther than h from B;
     (attain) some a in A has dist_sq a b >= h against EVERY b in B --
              h is tight: the most-mismatched point realises it.
   Together: h is exactly the attained max-min -- the value a ranked
   shape-matching pipeline (or a geometry similarity test) can trust.

   Proof: four list inductions over Rmin/Rmax (min lower bound, min
   attained, max dominates components, max attained), each opened by a
   one-step conversion equation so the folded inner calls stay intact
   for micromega.  No sqrt anywhere.

   Mirrors eval/Claim423a.v (same WITNESS tag), which carries the
   self-contained version plus the rational pins: pair example h_sq = 1
   both ways; asymmetric example [(0,0)] vs [(0,2);(3,0)] with forward
   4 / backward 9 (min-inside / max-outside / directedness killers).

   The symmetrization layer H = max(h(A,B), h(B,A)) is already proved
   abstractly in HausdorffMetricSym.v (the Hsym lemmas); instantiating it at
   this h needs the zero law and the directed triangle inequality --
   natural next rungs of epic #423, not claimed here.

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

(* WITNESS {"claimId":"423-a","topic":"metric","lemma":"directed_discrete_hausdorff_max_min","title":"Directed discrete Hausdorff = attained max-min over finite point lists"} *)

(* -------------------------------------------------------------------------- *)
(* §1  The value: innermost min, then outer max (HKR eq (2), squared).        *)
(*     The [] sentinels are outside the spec's domain (nonempty lists).       *)
(* -------------------------------------------------------------------------- *)

Fixpoint min_dist_sq_to (a : Point) (B : list Point) : R :=
  match B with
  | [] => 0
  | [b] => dist_sq a b
  | b :: B' => Rmin (dist_sq a b) (min_dist_sq_to a B')
  end.

Fixpoint directed_hausdorff_sq (A B : list Point) : R :=
  match A with
  | [] => 0
  | [a] => min_dist_sq_to a B
  | a :: A' => Rmax (min_dist_sq_to a B) (directed_hausdorff_sq A' B)
  end.

(* One-step unfolding equations (by conversion). *)
Lemma min_dist_sq_to_step : forall a b0 b1 B'',
    min_dist_sq_to a (b0 :: b1 :: B'')
    = Rmin (dist_sq a b0) (min_dist_sq_to a (b1 :: B'')).
Proof. reflexivity. Qed.

Lemma ddh_step : forall a0 a1 A'' B,
    directed_hausdorff_sq (a0 :: a1 :: A'') B
    = Rmax (min_dist_sq_to a0 B) (directed_hausdorff_sq (a1 :: A'') B).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The four aggregate facts.                                              *)
(* -------------------------------------------------------------------------- *)

(* The inner min is a lower bound on every candidate distance. *)
Lemma min_dist_sq_to_le : forall a B b,
    In b B -> min_dist_sq_to a B <= dist_sq a b.
Proof.
  intros a B. induction B as [ | b0 B' IH ]; intros b Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + destruct B' as [ | b1 B'' ]; [ simpl; lra | ].
      rewrite min_dist_sq_to_step. apply Rmin_l.
    + destruct B' as [ | b1 B'' ]; [ destruct Hin | ].
      rewrite min_dist_sq_to_step.
      eapply Rle_trans; [ apply Rmin_r | ]. apply IH. exact Hin.
Qed.

(* ... and it is attained on a nonempty list. *)
Lemma min_dist_sq_to_attained : forall a B,
    B <> nil -> exists b, In b B /\ min_dist_sq_to a B = dist_sq a b.
Proof.
  intros a B. induction B as [ | b0 B' IH ]; intros Hne.
  - congruence.
  - destruct B' as [ | b1 B'' ].
    + exists b0. split; [ left; reflexivity | reflexivity ].
    + destruct IH as [b [Hb Heq]]; [ discriminate | ].
      rewrite min_dist_sq_to_step.
      destruct (Rle_dec (dist_sq a b0) (min_dist_sq_to a (b1 :: B'')))
        as [Hle | Hgt].
      * exists b0. split; [ left; reflexivity | ].
        rewrite Rmin_left; [ reflexivity | exact Hle ].
      * apply Rnot_le_lt in Hgt.
        exists b. split; [ right; exact Hb | ].
        rewrite Rmin_right; [ exact Heq | lra ].
Qed.

(* The outer max dominates every per-point min. *)
Lemma ddh_ge_component : forall A B a,
    In a A -> min_dist_sq_to a B <= directed_hausdorff_sq A B.
Proof.
  intros A B. induction A as [ | a0 A' IH ]; intros a Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + destruct A' as [ | a1 A'' ]; [ simpl; lra | ].
      rewrite ddh_step. apply Rmax_l.
    + destruct A' as [ | a1 A'' ]; [ destruct Hin | ].
      rewrite ddh_step.
      eapply Rle_trans; [ apply IH; exact Hin | apply Rmax_r ].
Qed.

(* ... and it is attained on a nonempty list. *)
Lemma ddh_attained : forall A B,
    A <> nil ->
    exists a, In a A /\ directed_hausdorff_sq A B = min_dist_sq_to a B.
Proof.
  intros A B. induction A as [ | a0 A' IH ]; intros Hne.
  - congruence.
  - destruct A' as [ | a1 A'' ].
    + exists a0. split; [ left; reflexivity | reflexivity ].
    + destruct IH as [a [Ha Heq]]; [ discriminate | ].
      rewrite ddh_step.
      destruct (Rle_dec (directed_hausdorff_sq (a1 :: A'') B)
                        (min_dist_sq_to a0 B)) as [Hle | Hgt].
      * exists a0. split; [ left; reflexivity | ].
        rewrite Rmax_left; [ reflexivity | exact Hle ].
      * apply Rnot_le_lt in Hgt.
        exists a. split; [ right; exact Ha | ].
        rewrite Rmax_right; [ exact Heq | lra ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The 423-a headline: h is exactly the attained max-min.                 *)
(* -------------------------------------------------------------------------- *)

Theorem directed_discrete_hausdorff_max_min :
  forall (A B : list Point),
    A <> nil ->
    B <> nil ->
    (forall a, In a A ->
       exists b, In b B /\ dist_sq a b <= directed_hausdorff_sq A B) /\
    (exists a, In a A /\
       forall b, In b B -> directed_hausdorff_sq A B <= dist_sq a b).
Proof.
  intros A B HA HB. split.
  - intros a Hin.
    destruct (min_dist_sq_to_attained a B HB) as [b [Hb Heq]].
    exists b. split; [ exact Hb | ].
    rewrite <- Heq. apply ddh_ge_component. exact Hin.
  - destruct (ddh_attained A B HA) as [a [Ha Heq]].
    exists a. split; [ exact Ha | ].
    intros b Hb. rewrite Heq. apply min_dist_sq_to_le. exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Nonnegativity (a distance value; zero means A sits on B).              *)
(* -------------------------------------------------------------------------- *)

Lemma min_dist_sq_to_nonneg : forall a B, 0 <= min_dist_sq_to a B.
Proof.
  intros a B. induction B as [ | b0 B' IH ].
  - simpl. lra.
  - destruct B' as [ | b1 B'' ]; [ apply dist_sq_nonneg | ].
    rewrite min_dist_sq_to_step.
    pose proof (dist_sq_nonneg a b0).
    unfold Rmin. destruct (Rle_dec _ _); lra.
Qed.

Lemma directed_hausdorff_sq_nonneg : forall A B,
    0 <= directed_hausdorff_sq A B.
Proof.
  intros A B. induction A as [ | a0 A' IH ].
  - simpl. lra.
  - destruct A' as [ | a1 A'' ]; [ apply min_dist_sq_to_nonneg | ].
    rewrite ddh_step.
    pose proof (min_dist_sq_to_nonneg a0 B).
    unfold Rmax. destruct (Rle_dec _ _); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions directed_discrete_hausdorff_max_min.
Print Assumptions directed_hausdorff_sq_nonneg.
