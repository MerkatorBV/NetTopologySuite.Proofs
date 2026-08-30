(* ============================================================================
   NetTopologySuite.Proofs.NurbsGeneralLength
   ----------------------------------------------------------------------------
   Issue #508 NURBS next rungs (P1) after the degree-2 single-span landing
   in NurbsQuadraticLength.v:

     1. GENERAL DEGREE (degree-3 rational Bézier, the N-token's next
        stored form after the conic): equal-weights degeneration is the
        polynomial cubic, so is_curve_length transfers through
        Bezier3Length's parameterization.

     2. KNOT SPANS: length on an abutting pair of parameter windows is
        the sum of the span lengths — CurveLength.curve_length_additive
        instantiated as the NURBS knot-span obligation.  Multi-span
        Cox-de Boor evaluation is out of scope (oracle N is single-span).

     3. CONDITIONAL EXACT TIER: the rational arc-length primitive through
        curve_length_of_primitive (ADR-0001 idiom), same shape as the
        ellipse / clothoid parks.

   No ExactNurbsSegment Java type.  No `Admitted`, no `Axiom`, no
   `Parameter`.  3-axiom.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Export BernsteinBasis.
From NTS.Proofs Require Import Distance CurveLength ArcRectifiable
                               Bezier3Length.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Degree-3 rational Bézier (next stored form after the conic).               *)
(* -------------------------------------------------------------------------- *)

Definition nurbs3_den (w0 w1 w2 w3 t : R) : R :=
  bern3_0 t * w0 + bern3_1 t * w1 + bern3_2 t * w2 + bern3_3 t * w3.

Definition nurbs3_pt (p0 p1 p2 p3 : Point) (w0 w1 w2 w3 t : R) : Point :=
  mkPoint ((bern3_0 t * (w0 * px p0) + bern3_1 t * (w1 * px p1)
            + bern3_2 t * (w2 * px p2) + bern3_3 t * (w3 * px p3))
           / nurbs3_den w0 w1 w2 w3 t)
          ((bern3_0 t * (w0 * py p0) + bern3_1 t * (w1 * py p1)
            + bern3_2 t * (w2 * py p2) + bern3_3 t * (w3 * py p3))
           / nurbs3_den w0 w1 w2 w3 t).

Definition nurbs3_param (p0 p1 p2 p3 : Point) (w0 w1 w2 w3 : R) : Curve :=
  nurbs3_pt p0 p1 p2 p3 w0 w1 w2 w3.

Lemma nurbs3_den_equal : forall w t,
  nurbs3_den w w w w t = w.
Proof.
  intros w t. unfold nurbs3_den.
  pose proof (bern3_partition t) as Hp.
  unfold bern3_0, bern3_1, bern3_2, bern3_3 in *.
  lra.
Qed.

Lemma nurbs3_equal_weights_pt : forall p0 p1 p2 p3 w t,
  w <> 0 ->
  nurbs3_pt p0 p1 p2 p3 w w w w t = bezier3_pt p0 p1 p2 p3 t.
Proof.
  intros p0 p1 p2 p3 w t Hw.
  unfold nurbs3_pt, bezier3_pt.
  rewrite nurbs3_den_equal.
  unfold bern3_0, bern3_1, bern3_2, bern3_3.
  f_equal; field; exact Hw.
Qed.

(* WITNESS {"claimId":"nurbsgenerallength-nurbs3-equal-weights-length","topic":"metric","lemma":"nurbs3_equal_weights_length","title":"Equal-weight rational cubic carries the same is_curve_length values as the polynomial cubic","file":"theories/NurbsGeneralLength.v"} *)

Theorem nurbs3_equal_weights_length : forall p0 p1 p2 p3 w a b L,
  w <> 0 ->
  is_curve_length (nurbs3_param p0 p1 p2 p3 w w w w) a b L <->
  is_curve_length (bezier3_param p0 p1 p2 p3) a b L.
Proof.
  intros p0 p1 p2 p3 w a b L Hw. split; intro H.
  - apply (is_curve_length_ext (nurbs3_param p0 p1 p2 p3 w w w w));
      [| exact H].
    intro t. apply nurbs3_equal_weights_pt; exact Hw.
  - apply (is_curve_length_ext (bezier3_param p0 p1 p2 p3)); [| exact H].
    intro t. symmetry. apply nurbs3_equal_weights_pt; exact Hw.
Qed.

(* -------------------------------------------------------------------------- *)
(* Knot spans: abutting windows add.  Oracle N stays single-span; this is     *)
(* the named obligation for a future multi-span evaluation.                   *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"nurbsgenerallength-nurbs-knot-span-additive","topic":"metric","lemma":"nurbs_knot_span_additive","title":"NURBS length on abutting knot spans is the sum of the span lengths","file":"theories/NurbsGeneralLength.v"} *)

Theorem nurbs_knot_span_additive : forall (g : Curve) a k b L1 L2,
  a <= k -> k <= b ->
  is_curve_length g a k L1 ->
  is_curve_length g k b L2 ->
  is_curve_length g a b (L1 + L2).
Proof.
  intros g a k b L1 L2 Hak Hkb.
  apply curve_length_additive; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conditional exact tier: rational arc-length primitive.                     *)
(* -------------------------------------------------------------------------- *)

Section NurbsExactPrimitive.
  Variable g : Curve.
  Variable F : R -> R.

  Hypothesis H_F_chord : forall s t,
    s <= t -> dist (g s) (g t) <= F t - F s.

  Hypothesis H_F_approx : forall eps, 0 < eps ->
    exists delta, 0 < delta /\
      forall s t, s <= t -> t - s < delta ->
        F t - F s - dist (g s) (g t) <= eps * (t - s).

  Theorem nurbs_conditional_is_curve_length : forall a b,
    a <= b -> is_curve_length g a b (F b - F a).
  Proof.
    intros a b Hab.
    apply (curve_length_of_primitive g F a b); [| | exact Hab].
    - intros s t _ Hst _. apply H_F_chord; exact Hst.
    - intros eps Heps.
      destruct (H_F_approx eps Heps) as (delta & Hd0 & Hd).
      exists delta. split; [exact Hd0 |].
      intros s t _ Hst _ Hts. apply Hd; assumption.
  Qed.

End NurbsExactPrimitive.

Print Assumptions nurbs3_equal_weights_length.
Print Assumptions nurbs_knot_span_additive.
Print Assumptions nurbs_conditional_is_curve_length.
