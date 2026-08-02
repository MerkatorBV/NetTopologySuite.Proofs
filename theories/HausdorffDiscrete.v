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

   Proof: the four aggregation facts (min lower bound, min attained,
   max dominates components, max attained) are instantiations of the
   score-agnostic layer in MaxMinScore.v at score := dist_sq -- the
   post-#431/#432 refactor consolidating the machinery shared with the
   unsquared instance in HausdorffMetricInstance.v.  No sqrt anywhere.

   Mirrors eval/Claim423a.v (same WITNESS tag), which carries the
   self-contained version plus the rational pins: pair example h_sq = 1
   both ways; asymmetric example [(0,0)] vs [(0,2);(3,0)] with forward
   4 / backward 9 (min-inside / max-outside / directedness killers).

   The symmetrization layer H = max(h(A,B), h(B,A)) is proved
   abstractly in HausdorffMetricSym.v and CLOSED at the unsquared
   metric in HausdorffMetricInstance.v (zero law = List.incl, directed
   triangle, full HKR metric) -- this file remains the squared 423-a
   claim surface only.

   WITNESS claimId: 423-a
   topic: metric
   Lemma: directed_discrete_hausdorff_max_min

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance MaxMinScore.
Import ListNotations.
Open Scope R_scope.

(* WITNESS {"claimId":"423-a","topic":"metric","lemma":"directed_discrete_hausdorff_max_min","title":"Directed discrete Hausdorff = attained max-min over finite point lists"} *)

(* -------------------------------------------------------------------------- *)
(* §1  The value: innermost min, then outer max (HKR eq (2), squared).        *)
(*     The [] sentinels are outside the spec's domain (nonempty lists).       *)
(* -------------------------------------------------------------------------- *)

Definition min_dist_sq_to (a : Point) (B : list Point) : R :=
  min_score_to dist_sq a B.

Definition directed_hausdorff_sq (A B : list Point) : R :=
  max_min_score dist_sq A B.

(* One-step unfolding equations (by conversion, via the shared layer). *)
Lemma min_dist_sq_to_step : forall a b0 b1 B'',
    min_dist_sq_to a (b0 :: b1 :: B'')
    = Rmin (dist_sq a b0) (min_dist_sq_to a (b1 :: B'')).
Proof. intros. exact (min_score_to_step dist_sq a b0 b1 B''). Qed.

Lemma ddh_step : forall a0 a1 A'' B,
    directed_hausdorff_sq (a0 :: a1 :: A'') B
    = Rmax (min_dist_sq_to a0 B) (directed_hausdorff_sq (a1 :: A'') B).
Proof. intros. exact (max_min_score_step dist_sq a0 a1 A'' B). Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The four aggregate facts.                                              *)
(* -------------------------------------------------------------------------- *)

(* The inner min is a lower bound on every candidate distance. *)
Lemma min_dist_sq_to_le : forall a B b,
    In b B -> min_dist_sq_to a B <= dist_sq a b.
Proof. exact (min_score_to_le dist_sq). Qed.

(* ... and it is attained on a nonempty list. *)
Lemma min_dist_sq_to_attained : forall a B,
    B <> nil -> exists b, In b B /\ min_dist_sq_to a B = dist_sq a b.
Proof. exact (min_score_to_attained dist_sq). Qed.

(* The outer max dominates every per-point min. *)
Lemma ddh_ge_component : forall A B a,
    In a A -> min_dist_sq_to a B <= directed_hausdorff_sq A B.
Proof. exact (max_min_score_ge_component dist_sq). Qed.

(* ... and it is attained on a nonempty list. *)
Lemma ddh_attained : forall A B,
    A <> nil ->
    exists a, In a A /\ directed_hausdorff_sq A B = min_dist_sq_to a B.
Proof. exact (max_min_score_attained dist_sq). Qed.

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
Proof. exact (min_score_to_nonneg dist_sq dist_sq_nonneg). Qed.

Lemma directed_hausdorff_sq_nonneg : forall A B,
    0 <= directed_hausdorff_sq A B.
Proof. exact (max_min_score_nonneg dist_sq dist_sq_nonneg). Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions directed_discrete_hausdorff_max_min.
Print Assumptions directed_hausdorff_sq_nonneg.
