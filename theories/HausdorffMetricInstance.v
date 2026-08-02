(* ============================================================================
   NetTopologySuite.Proofs.HausdorffMetricInstance
   ----------------------------------------------------------------------------
   THE HKR HAUSDORFF METRIC, DISCRETELY INSTANTIATED.

   Huttenlocher-Klanderman-Rucklidge (IEEE PAMI 1993) Section I-A rests
   on H(A,B) = max(h(A,B), h(B,A)) being a METRIC on point sets --
   identity, symmetry, triangle -- so that a ranked model database is
   transitive ("two highly dissimilar shapes cannot both be similar to
   a third").  HausdorffMetricSym.v proved that symmetrization theorem
   ABSTRACTLY, over any directed dissimilarity with three axioms
   (nonnegativity, a zero-iff-subshape law, the directed triangle
   inequality).  This file supplies the three axioms for the concrete
   DISCRETE directed Hausdorff on finite point lists and closes the
   instantiation:

   (a) GENERIC MAX-MIN LAYER.  The aggregation facts of the 423-a Green
       (inner min is an attained lower bound, outer max is an attained
       upper bound) use no property of the score function at all; they
       live once in MaxMinScore.v (shared with HausdorffDiscrete.v) and
       are instantiated here at the UNSQUARED metric dist (the triangle
       inequality lives there; the squared convention of 423-a's claim
       surface cannot carry it, since (a+b)^2 <> a^2 + b^2).

   (b) ZERO LAW = LIST INCLUSION.  h(A,B) = 0  <->  incl A B  on
       nonempty lists: h vanishes exactly when every vertex of A
       coincides with a vertex of B (dist_eq_zero_iff + point
       extensionality).  HKR's "identity up to carrier equality",
       verbatim in List.incl vocabulary.

   (c) DIRECTED TRIANGLE.  h(A,C) <= h(A,B) + h(B,C) on nonempty lists:
       route the arg-max vertex a* of A through its nearest b* in B and
       b*'s nearest c* in C, then chain min_score_to_le, the metric
       dist_triangle, and the attained bounds.

   (d) THE INSTANCE.  On the carrier of nonempty lists (a sig type --
       the empty-list sentinels genuinely falsify both laws, so the
       carrier restriction is semantic, not cosmetic), Hsym instantiates
       to the discrete H with symmetry, the mutual-inclusion zero law,
       and the triangle inequality: the HKR metric, end to end, with
       Print Assumptions showing the classical-reals axioms only.

   Rational pins in HKR's own metric units: the 423-a asymmetric
   witness A' = [(0,0)], B' = [(0,2);(3,0)] gives h(A',B') = 2 and
   h(B',A') = 3 UNSQUARED (the paper flags h's asymmetry explicitly;
   these are the plan's original expectation values).

   Relation to the board: 423-a (PR #431) closed the attained-max-min
   spec at the squared convention; this file is the metric-axioms lane
   on top -- no claim surface is redefined.  Post-merge refactor: the
   generic layer moved to MaxMinScore.v and HausdorffDiscrete.v now
   derives its dist_sq machinery from the same source.

   WITNESS claimId: none (lane enrichment; adoptable as a 423 rung)
   topic: metric

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance HausdorffMetricSym MaxMinScore.
Import ListNotations.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Generic max-min layer: imported from MaxMinScore.v.                    *)
(* -------------------------------------------------------------------------- *)

(* The score-agnostic max-min layer lives in MaxMinScore.v (shared with
   HausdorffDiscrete.v); this file instantiates it at the unsquared dist. *)

(* -------------------------------------------------------------------------- *)
(* §2  The unsquared directed Hausdorff and its three metric axioms.          *)
(* -------------------------------------------------------------------------- *)

(* HKR eq (2) in true metric units: h(A,B) = max_{a in A} min_{b in B}
   dist a b.  (423-a's claim surface is the squared twin; the triangle
   inequality only exists at this level.) *)
Definition directed_hausdorff (A B : list Point) : R :=
  max_min_score dist A B.

Lemma directed_hausdorff_nonneg : forall A B, 0 <= directed_hausdorff A B.
Proof. intros. apply max_min_score_nonneg. exact dist_nonneg. Qed.

(* Record extensionality: coordinate equality is point equality. *)
Lemma point_eq_of_coords : forall p q, px p = px q -> py p = py q -> p = q.
Proof. intros [xp yp] [xq yq]; simpl; intros -> ->; reflexivity. Qed.

(* AXIOM 2 for Hsym -- the zero law IS list inclusion: h vanishes exactly
   when every vertex of A coincides with a vertex of B. *)
Theorem directed_hausdorff_zero_iff : forall A B,
    A <> nil -> B <> nil ->
    (directed_hausdorff A B = 0 <-> incl A B).
Proof.
  intros A B HA HB. unfold directed_hausdorff. split.
  - (* h = 0 => inclusion: each a's attained nearest b is a itself *)
    intros H0 a Ha.
    assert (Hmin0 : min_score_to dist a B = 0).
    { pose proof (max_min_score_ge_component dist A B a Ha) as Hup.
      pose proof (min_score_to_nonneg dist dist_nonneg a B) as Hlo.
      lra. }
    destruct (min_score_to_attained dist a B HB) as [b [Hb Heq]].
    rewrite Hmin0 in Heq.
    symmetry in Heq. apply dist_eq_zero_iff in Heq.
    destruct Heq as [Hx Hy].
    rewrite (point_eq_of_coords a b Hx Hy). exact Hb.
  - (* inclusion => h = 0: the attained max vertex sits on B *)
    intros Hincl.
    destruct (max_min_score_attained dist A B HA) as [a [Ha Heq]].
    rewrite Heq.
    assert (Hup : min_score_to dist a B <= dist a a).
    { apply min_score_to_le. apply Hincl. exact Ha. }
    rewrite dist_refl in Hup.
    pose proof (min_score_to_nonneg dist dist_nonneg a B). lra.
Qed.

(* AXIOM 3 for Hsym -- the DIRECTED triangle inequality: route the
   arg-max vertex a* through its nearest b* in B, then b*'s nearest c*
   in C, and chain the metric triangle inequality. *)
Theorem directed_hausdorff_triangle : forall A B C,
    A <> nil -> B <> nil -> C <> nil ->
    directed_hausdorff A C
    <= directed_hausdorff A B + directed_hausdorff B C.
Proof.
  intros A B C HA HB HC. unfold directed_hausdorff.
  destruct (max_min_score_attained dist A C HA) as [a [Ha HeqA]].
  destruct (min_score_to_attained dist a B HB) as [b [Hb HeqB]].
  destruct (min_score_to_attained dist b C HC) as [c [Hc HeqC]].
  rewrite HeqA.
  (* min over C from a is at most the routed distance a -> b -> c *)
  assert (Hroute : min_score_to dist a C <= dist a c)
    by (apply min_score_to_le; exact Hc).
  pose proof (dist_triangle a b c) as Htri.
  (* dist a b is a's attained min over B, dominated by h(A,B) *)
  assert (HaB : dist a b <= max_min_score dist A B).
  { rewrite <- HeqB. apply max_min_score_ge_component. exact Ha. }
  (* dist b c is b's attained min over C, dominated by h(B,C) *)
  assert (HbC : dist b c <= max_min_score dist B C).
  { rewrite <- HeqC. apply max_min_score_ge_component. exact Hb. }
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The Hsym instantiation on nonempty lists.                              *)
(*                                                                            *)
(* The carrier restriction is semantic: with the empty-list sentinel,        *)
(* h(A, []) = 0 while incl A [] is false, and the triangle inequality        *)
(* fails through B = [] -- so the sig type is exactly HKR's finite           *)
(* nonempty point sets, not ceremony.                                        *)
(* -------------------------------------------------------------------------- *)

Definition NEPointList : Type := { l : list Point | l <> nil }.

Definition ne_carrier (A : NEPointList) : list Point := proj1_sig A.

Definition ne_hausdorff (A B : NEPointList) : R :=
  directed_hausdorff (ne_carrier A) (ne_carrier B).

Definition ne_incl (A B : NEPointList) : Prop :=
  incl (ne_carrier A) (ne_carrier B).

(* The full HKR distance, eq (1): H = max of the two directed values. *)
Definition hausdorff_distance (A B : NEPointList) : R :=
  Hsym NEPointList ne_hausdorff A B.

Theorem hausdorff_distance_nonneg : forall A B,
    0 <= hausdorff_distance A B.
Proof.
  intros A B. apply Hsym_nonneg.
  intros X Y. apply directed_hausdorff_nonneg.
Qed.

Theorem hausdorff_distance_symmetric : forall A B,
    hausdorff_distance A B = hausdorff_distance B A.
Proof. intros A B. apply Hsym_symmetric. Qed.

(* HKR identity: H = 0 exactly on mutual vertex inclusion. *)
Theorem hausdorff_distance_zero_iff : forall A B,
    hausdorff_distance A B = 0 <-> ne_incl A B /\ ne_incl B A.
Proof.
  intros A B. apply Hsym_zero_iff.
  - intros X Y. apply directed_hausdorff_nonneg.
  - intros [X HX] [Y HY].
    unfold ne_hausdorff, ne_incl, ne_carrier; simpl.
    apply directed_hausdorff_zero_iff; assumption.
Qed.

(* HKR triangle: ranked model databases are transitive. *)
Theorem hausdorff_distance_triangle : forall A B C,
    hausdorff_distance A C
    <= hausdorff_distance A B + hausdorff_distance B C.
Proof.
  intros A B C. apply Hsym_triangle.
  intros [X HX] [Y HY] [Z HZ].
  unfold ne_hausdorff, ne_carrier; simpl.
  apply directed_hausdorff_triangle; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Rational pins in HKR's own metric units.                               *)
(*     The 423-a asymmetric witness, unsquared: h forward 2, backward 3.      *)
(* -------------------------------------------------------------------------- *)

Definition mp (x y : R) : Point := mkPoint x y.

Lemma dist_00_02 : dist (mp 0 0) (mp 0 2) = 2.
Proof.
  unfold dist.
  replace (dist_sq (mp 0 0) (mp 0 2)) with (2 * 2)
    by (unfold dist_sq, mp; simpl; ring).
  rewrite sqrt_square; lra.
Qed.

Lemma dist_00_30 : dist (mp 0 0) (mp 3 0) = 3.
Proof.
  unfold dist.
  replace (dist_sq (mp 0 0) (mp 3 0)) with (3 * 3)
    by (unfold dist_sq, mp; simpl; ring).
  rewrite sqrt_square; lra.
Qed.

(* Forward: the single A'-vertex takes its NEAREST B'-vertex: min(2,3)=2. *)
Lemma w_asym_forward_metric :
  directed_hausdorff [mp 0 0] [mp 0 2; mp 3 0] = 2.
Proof.
  unfold directed_hausdorff. cbn [max_min_score min_score_to].
  rewrite dist_00_02, dist_00_30.
  rewrite Rmin_left; lra.
Qed.

(* Backward: the farther B'-vertex dominates: max(2,3)=3.  h is DIRECTED
   (the asymmetry HKR flags in Section I-A footnote). *)
Lemma w_asym_backward_metric :
  directed_hausdorff [mp 0 2; mp 3 0] [mp 0 0] = 3.
Proof.
  unfold directed_hausdorff. cbn [max_min_score min_score_to].
  rewrite (dist_sym (mp 0 2)), dist_00_02, (dist_sym (mp 3 0)), dist_00_30.
  rewrite Rmax_right; lra.
Qed.

Lemma w_directed_asymmetric_metric :
  directed_hausdorff [mp 0 0] [mp 0 2; mp 3 0]
  <> directed_hausdorff [mp 0 2; mp 3 0] [mp 0 0].
Proof.
  rewrite w_asym_forward_metric, w_asym_backward_metric. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions directed_hausdorff_zero_iff.
Print Assumptions directed_hausdorff_triangle.
Print Assumptions hausdorff_distance_triangle.
Print Assumptions hausdorff_distance_zero_iff.
