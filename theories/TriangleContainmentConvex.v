(* ============================================================================
   NetTopologySuite.Proofs.TriangleContainmentConvex

   [Issue #67, RelateNG lane track] A building block toward classifying the
   TPR_Contains regime of `triangle_pair_regime`
   (RelateMatrixTriangle.TrianglePairRegime / RelateNG.v).

   `triangle_pair_regime` currently detects TPR_TouchEdge and falls back to
   TPR_Disjoint for every other configuration, including genuine containment
   (RelateNG.v comment: "returning TPR_Disjoint as the default for the
   not-yet-classified regimes (contains/overlap)").  The natural containment
   TEST is cheap to compute -- "all three vertices of triangle B satisfy
   0 <= gtri A" (GeneralTriangleSeparation.v) -- but that vertex-level check
   only justifies classifying TPR_Contains if it forces triangle B's WHOLE
   boundary (not merely its three vertices) inside A: otherwise an edge of B
   could dip outside A between two vertices that individually pass.

   This file supplies exactly that missing step, generically:

     - `gtri_region_is_convex`: the closed CCW/CW-agnostic triangle region
       `{p | 0 <= gtri ax ay bx by_ cx cy p}` is CONVEX.  `gtri` is the min of
       three affine "inward signed area" functions (`gsA`/`gsB`/`gsC`), each
       of which is affine in the query point, so each half-plane
       `{p | 0 <= gsX p}` is closed under convex combinations by the same
       one-line `nra` argument `Convex.half_plane_ge_is_convex` already uses;
       `gtri`'s region is their intersection (via `Lattice.Rmin_le_iff`,
       which decomposes `0 <= Rmin _ _` into the componentwise conjunction),
       hence convex too.

     - `gtri_region_contains_segment`: consequently, if both endpoints of a
       segment lie in A's closed region, so does every point `between` them
       (via `Convex.between_implies_convex_combo`).  Applied to each of B's
       three edges, this is exactly the fact needed to lift "all 3 vertices
       of B are in A" to "B's whole boundary is in A" -- the honest
       remaining obligation before `triangle_pair_regime` can be extended
       with a TPR_Contains case.  Wiring that extension into `RelateNG.v`
       itself (a file other #67 tracks are actively working) is left as
       explicit follow-up; this file is purely additive and does not modify
       any existing definition.

   No new axioms; pure algebra (`nra`) composed with already-Qed
   `Convex.v` / `Lattice.v` / `GeneralTriangleSeparation.v` lemmas.
   No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
From NTS.Proofs Require Import Distance Orientation Segment Convex Lattice
                               GeneralTriangleSeparation.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Each inward half-plane {p | 0 <= gsX p} is convex.                     *)
(* -------------------------------------------------------------------------- *)

Lemma gsA_ge0_is_convex :
  forall ax ay bx by_ : R,
    is_convex (fun p => 0 <= gsA ax ay bx by_ p).
Proof.
  intros ax ay bx by_.
  unfold is_convex, gsA, convex_combination.
  intros P Q t HP HQ Ht0 Ht1. simpl. nra.
Qed.

Lemma gsB_ge0_is_convex :
  forall bx by_ cx cy : R,
    is_convex (fun p => 0 <= gsB bx by_ cx cy p).
Proof.
  intros bx by_ cx cy.
  unfold is_convex, gsB, convex_combination.
  intros P Q t HP HQ Ht0 Ht1. simpl. nra.
Qed.

Lemma gsC_ge0_is_convex :
  forall ax ay cx cy : R,
    is_convex (fun p => 0 <= gsC ax ay cx cy p).
Proof.
  intros ax ay cx cy.
  unfold is_convex, gsC, convex_combination.
  intros P Q t HP HQ Ht0 Ht1. simpl. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  gtri >= 0 decomposes into the three componentwise inequalities.        *)
(* -------------------------------------------------------------------------- *)

Lemma gtri_ge0_iff :
  forall ax ay bx by_ cx cy p,
    0 <= gtri ax ay bx by_ cx cy p <->
    0 <= gsA ax ay bx by_ p /\
    0 <= gsB bx by_ cx cy p /\
    0 <= gsC ax ay cx cy p.
Proof.
  intros ax ay bx by_ cx cy p. unfold gtri. rewrite !Rmin_le_iff. tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Headline: the closed gtri region is convex.                            *)
(* -------------------------------------------------------------------------- *)

Theorem gtri_region_is_convex :
  forall ax ay bx by_ cx cy : R,
    is_convex (fun p => 0 <= gtri ax ay bx by_ cx cy p).
Proof.
  intros ax ay bx by_ cx cy P Q t HP HQ Ht0 Ht1.
  apply gtri_ge0_iff in HP as [HPA [HPB HPC]].
  apply gtri_ge0_iff in HQ as [HQA [HQB HQC]].
  apply gtri_ge0_iff.
  repeat split.
  - exact (gsA_ge0_is_convex ax ay bx by_ P Q t HPA HQA Ht0 Ht1).
  - exact (gsB_ge0_is_convex bx by_ cx cy P Q t HPB HQB Ht0 Ht1).
  - exact (gsC_ge0_is_convex ax ay cx cy P Q t HPC HQC Ht0 Ht1).
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Corollary: a whole segment survives once both endpoints are in.       *)
(* -------------------------------------------------------------------------- *)

Corollary gtri_region_contains_segment :
  forall ax ay bx by_ cx cy P Q Rpt,
    0 <= gtri ax ay bx by_ cx cy P ->
    0 <= gtri ax ay bx by_ cx cy Q ->
    between P Q Rpt ->
    0 <= gtri ax ay bx by_ cx cy Rpt.
Proof.
  intros ax ay bx by_ cx cy P Q Rpt HP HQ Hbtw.
  destruct (between_implies_convex_combo P Q Rpt Hbtw) as [t [[Ht0 Ht1] Heq]].
  subst Rpt.
  exact (gtri_region_is_convex ax ay bx by_ cx cy P Q t HP HQ Ht0 Ht1).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  RGR pivot (risk/cost): the OPEN region {p | 0 < gtri p} is ALSO        *)
(* convex, by the identical `nra` argument -- a convex combination of two     *)
(* strictly-positive values is itself strictly positive for every t in       *)
(* [0,1] (at t=0/1 it IS one of the two positive values; in between it's a    *)
(* sum of two nonnegative terms with at least one strictly positive factor,   *)
(* since (1-t) and t can't both vanish).  This is the sharper fact           *)
(* `contains_b`'s callers actually need: it shows B's whole boundary is      *)
(* STRICTLY interior to A (not merely in A's closure), i.e. B's boundary      *)
(* never touches A's boundary -- exactly the BI/BE emptiness `aa_matrix_     *)
(* contains` (RelateAreaArea.v) claims for the TPR_Contains cell.            *)
(* -------------------------------------------------------------------------- *)

(* Strict positivity needs a three-way split on t: at the endpoints t=0/t=1
   the combination IS one of the two given-positive values outright; only in
   the interior (0<t<1) is it a genuine sum of two strictly-positive products
   -- a disjunctive fact `nra` cannot certify in one shot without the split. *)
Lemma gsA_gt0_is_convex :
  forall ax ay bx by_ : R,
    is_convex (fun p => 0 < gsA ax ay bx by_ p).
Proof.
  intros ax ay bx by_ P Q t HP HQ Ht0 Ht1.
  unfold gsA, convex_combination in *. simpl in *.
  destruct (Req_dec t 0) as [-> | Hne0]; [ nra | ].
  destruct (Req_dec t 1) as [-> | Hne1]; [ nra | ].
  assert (0 < t) by lra. assert (t < 1) by lra. nra.
Qed.

Lemma gsB_gt0_is_convex :
  forall bx by_ cx cy : R,
    is_convex (fun p => 0 < gsB bx by_ cx cy p).
Proof.
  intros bx by_ cx cy P Q t HP HQ Ht0 Ht1.
  unfold gsB, convex_combination in *. simpl in *.
  destruct (Req_dec t 0) as [-> | Hne0]; [ nra | ].
  destruct (Req_dec t 1) as [-> | Hne1]; [ nra | ].
  assert (0 < t) by lra. assert (t < 1) by lra. nra.
Qed.

Lemma gsC_gt0_is_convex :
  forall ax ay cx cy : R,
    is_convex (fun p => 0 < gsC ax ay cx cy p).
Proof.
  intros ax ay cx cy P Q t HP HQ Ht0 Ht1.
  unfold gsC, convex_combination in *. simpl in *.
  destruct (Req_dec t 0) as [-> | Hne0]; [ nra | ].
  destruct (Req_dec t 1) as [-> | Hne1]; [ nra | ].
  assert (0 < t) by lra. assert (t < 1) by lra. nra.
Qed.

Theorem gtri_region_strict_is_convex :
  forall ax ay bx by_ cx cy : R,
    is_convex (fun p => 0 < gtri ax ay bx by_ cx cy p).
Proof.
  intros ax ay bx by_ cx cy P Q t HP HQ Ht0 Ht1.
  apply gtri_pos_iff in HP as [HPA [HPB HPC]].
  apply gtri_pos_iff in HQ as [HQA [HQB HQC]].
  apply gtri_pos_iff.
  repeat split.
  - exact (gsA_gt0_is_convex ax ay bx by_ P Q t HPA HQA Ht0 Ht1).
  - exact (gsB_gt0_is_convex bx by_ cx cy P Q t HPB HQB Ht0 Ht1).
  - exact (gsC_gt0_is_convex ax ay cx cy P Q t HPC HQC Ht0 Ht1).
Qed.

Corollary gtri_region_strict_contains_segment :
  forall ax ay bx by_ cx cy P Q Rpt,
    0 < gtri ax ay bx by_ cx cy P ->
    0 < gtri ax ay bx by_ cx cy Q ->
    between P Q Rpt ->
    0 < gtri ax ay bx by_ cx cy Rpt.
Proof.
  intros ax ay bx by_ cx cy P Q Rpt HP HQ Hbtw.
  destruct (between_implies_convex_combo P Q Rpt Hbtw) as [t [[Ht0 Ht1] Heq]].
  subst Rpt.
  exact (gtri_region_strict_is_convex ax ay bx by_ cx cy P Q t HP HQ Ht0 Ht1).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions gtri_region_is_convex.
Print Assumptions gtri_region_contains_segment.
Print Assumptions gtri_region_strict_is_convex.
Print Assumptions gtri_region_strict_contains_segment.
