(* ============================================================================
   NetTopologySuite.Proofs.HausdorffMetricSym
   ----------------------------------------------------------------------------
   Huttenlocher, Klanderman & Rucklidge, "Comparing Images Using the
   Hausdorff Distance", IEEE Trans. PAMI 15(9):850-863, 1993 -- the
   canonical reference for the (directed) Hausdorff distance that
   JTS/NTS DiscreteHausdorffDistance implements, and the basis of
   epic #423.

   The paper's shape-matching pipeline: a model point set B is compared
   to an image point set A by
       H(A,B) = max( h(A,B), h(B,A) )              (eq (1))
       h(A,B) = max_{a in A} min_{b in B} |a - b|  (eq (2), DIRECTED)
   and Section I-A leans on H being a METRIC (identity, symmetry,
   triangle inequality): "two shapes that are highly dissimilar cannot
   both be similar to some third shape" -- the property that makes a
   ranked model database trustworthy.  The directed h itself is NOT
   symmetric (the paper flags this explicitly).

   What is proved here:

   (a) SYMMETRIZATION LAYER (eq (1) => metric, abstractly).  The metric
       property of H is not about max-min at all: it holds for ANY
       directed dissimilarity h over any carrier once h is nonnegative,
       vanishes exactly on a sub-shape relation, and obeys the DIRECTED
       triangle inequality h(A,C) <= h(A,B) + h(B,C).  Section
       SymmetrizedMetric proves symmetry, the zero law (H = 0 iff
       mutual inclusion, the "identity up to carrier equality" of the
       paper), and the triangle inequality for H := max(h(A,B), h(B,A))
       from exactly those three axioms.  When micro-claims 423-a
       (max-min realization, RED in eval/Claim423a.v) and a future
       directed-triangle claim go Green, instantiating this section at
       the discrete h yields eq (1)'s metric verbatim -- the section
       deliberately does NOT define the discrete max-min itself (that
       is 423-a's claim surface).

   (b) VORONOI-SURFACE LAYER (Section II pins, 1D).  The paper computes
       h via the "Voronoi surface" (distance transform)
       d(x) = min_{b in B} |x - b|: an egg-carton with zeros at the
       sites and ridges between them, and the translation identity
       behind H(A, B (+) t).  For the two-site 1D surface
       vor2 b1 b2 x = min(|x-b1|, |x-b2|) we pin: zeros exactly at the
       sites, the ridge peak (b1+b2)/2 at height (b2-b1)/2, translation
       covariance vor2(b1+t, b2+t, x+t) = vor2(b1, b2, x), the 1-Lipschitz
       cone slope |vor2 x - vor2 x'| <= |x - x'|, and the rational
       egg-carton profile for sites {0,4}.

   All rational Rmin/Rmax/Rabs algebra; no sqrt, no limits.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Symmetrization: eq (1) is a metric for ANY well-behaved directed h.    *)
(* -------------------------------------------------------------------------- *)

Section SymmetrizedMetric.

  (* Shapes and a sub-shape relation ("every point of A is a point of B"
     for point sets; the paper's finite point sets are one instance). *)
  Variable Shape : Type.
  Variable sub : Shape -> Shape -> Prop.

  (* The directed dissimilarity, e.g. eq (2)'s max-min. *)
  Variable h : Shape -> Shape -> R.

  Hypothesis h_nonneg : forall A B, 0 <= h A B.
  Hypothesis h_zero_iff : forall A B, h A B = 0 <-> sub A B.
  Hypothesis h_directed_triangle : forall A B C, h A C <= h A B + h B C.

  (* eq (1): the symmetrized Hausdorff distance. *)
  Definition Hsym (A B : Shape) : R := Rmax (h A B) (h B A).

  Lemma Hsym_nonneg : forall A B, 0 <= Hsym A B.
  Proof.
    intros A B. unfold Hsym.
    pose proof (h_nonneg A B). pose proof (Rmax_l (h A B) (h B A)). lra.
  Qed.

  (* Symmetry -- by construction (Rmax commutes). *)
  Lemma Hsym_symmetric : forall A B, Hsym A B = Hsym B A.
  Proof. intros A B. unfold Hsym. apply Rmax_comm. Qed.

  (* The zero law: H(A,B) = 0 exactly when each shape is a sub-shape of
     the other -- the paper's identity property, stated without baking
     in an extensionality axiom for the carrier. *)
  Lemma Hsym_zero_iff : forall A B, Hsym A B = 0 <-> sub A B /\ sub B A.
  Proof.
    intros A B. unfold Hsym. split.
    - intros H0.
      pose proof (h_nonneg A B). pose proof (h_nonneg B A).
      pose proof (Rmax_l (h A B) (h B A)).
      pose proof (Rmax_r (h A B) (h B A)).
      split; apply h_zero_iff; lra.
    - intros [HAB HBA].
      apply h_zero_iff in HAB. apply h_zero_iff in HBA.
      rewrite HAB, HBA. unfold Rmax.
      destruct (Rle_dec 0 0); lra.
  Qed.

  (* The triangle inequality for H, from the DIRECTED triangle
     inequality for h -- "two highly dissimilar shapes cannot both be
     similar to a third". *)
  Lemma Hsym_triangle : forall A B C, Hsym A C <= Hsym A B + Hsym B C.
  Proof.
    intros A B C. unfold Hsym.
    pose proof (h_directed_triangle A B C) as H1.
    pose proof (h_directed_triangle C B A) as H2.
    pose proof (Rmax_l (h A B) (h B A)) as LAB.
    pose proof (Rmax_r (h A B) (h B A)) as RAB.
    pose proof (Rmax_l (h B C) (h C B)) as LBC.
    pose proof (Rmax_r (h B C) (h C B)) as RBC.
    apply Rmax_lub; lra.
  Qed.

End SymmetrizedMetric.

(* -------------------------------------------------------------------------- *)
(* §2  The 1D two-site Voronoi surface (Section II's distance transform).     *)
(* -------------------------------------------------------------------------- *)

Definition vor2 (b1 b2 x : R) : R := Rmin (Rabs (x - b1)) (Rabs (x - b2)).

Ltac vor_crunch :=
  unfold vor2, Rmin, Rmax, Rabs in *;
  repeat match goal with
         | |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b)
         | H : context [Rle_dec ?a ?b] |- _ => destruct (Rle_dec a b)
         | |- context [Rcase_abs ?t] => destruct (Rcase_abs t)
         | H : context [Rcase_abs ?t] |- _ => destruct (Rcase_abs t)
         end;
  try lra.

(* Zeros exactly at the sites: the egg-carton touches the floor at B. *)
Lemma vor2_zero_at_sites : forall b1 b2,
    vor2 b1 b2 b1 = 0 /\ vor2 b1 b2 b2 = 0.
Proof. intros b1 b2. split; vor_crunch. Qed.

(* Nonnegative everywhere (it is a distance-to-set). *)
Lemma vor2_nonneg : forall b1 b2 x, 0 <= vor2 b1 b2 x.
Proof. intros. vor_crunch. Qed.

(* The ridge between two sites peaks at the midpoint, at half the site
   separation -- the local maximum that makes the surface an egg carton
   and the Voronoi boundary between the two cells. *)
Lemma vor2_midpoint_ridge : forall b1 b2,
    b1 <= b2 ->
    vor2 b1 b2 ((b1 + b2) / 2) = (b2 - b1) / 2.
Proof. intros b1 b2 H. vor_crunch. Qed.

(* Translation covariance: shifting the sites by t shifts the surface by
   t -- the identity behind computing H(A, B (+) t) by sliding fixed
   Voronoi surfaces (Section II's d(a - t) reduction). *)
Lemma vor2_translation : forall b1 b2 t x,
    vor2 (b1 + t) (b2 + t) (x + t) = vor2 b1 b2 x.
Proof.
  intros b1 b2 t x. unfold vor2.
  replace (x + t - (b1 + t)) with (x - b1) by ring.
  replace (x + t - (b2 + t)) with (x - b2) by ring.
  reflexivity.
Qed.

(* The cone slope is 1-Lipschitz: moving the query point by delta moves
   the distance-to-set by at most |delta| -- why rasterizing the surface
   on a unit grid (the paper's Section IV) loses at most half a pixel. *)
Lemma vor2_lipschitz : forall b1 b2 x x',
    Rabs (vor2 b1 b2 x - vor2 b1 b2 x') <= Rabs (x - x').
Proof. intros. vor_crunch. Qed.

(* Rational egg-carton profile for sites {0,4}: floor at the sites, ridge
   of height 2 at the midpoint, unit values one step from each site, and
   the outer cone climbing away from the far site. *)
Lemma vor2_profile_0_4 :
    vor2 0 4 0 = 0 /\ vor2 0 4 1 = 1 /\ vor2 0 4 2 = 2 /\
    vor2 0 4 3 = 1 /\ vor2 0 4 4 = 0 /\ vor2 0 4 5 = 1.
Proof. repeat split; vor_crunch. Qed.

(* MISMATCH PROBE: the ridge height is the distance to the NEAREST site,
   not the farthest -- at the probe x = 1 the far-site reading would say
   3, the surface says 1. *)
Lemma vor2_nearest_not_farthest : vor2 0 4 1 < Rabs (1 - 4).
Proof. vor_crunch. Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions Hsym_triangle.
Print Assumptions Hsym_zero_iff.
Print Assumptions vor2_lipschitz.
