(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgePosOrder
   ----------------------------------------------------------------------------
   Exact total ordering of edge positions by a single int128 cross-multiply.

   In the integer-coordinate robust pipeline (Romanschek, Clemen & Huhnt 2021;
   see RelateIntDetBound.v), the position of an intersection point along an
   oriented edge is a RATIONAL number `num / den`, where both `num` and `den`
   are orientation determinants (`idet`) of integer-coordinate triangles.  To
   NODE an edge -- to sort all the intersection points that fall on it into a
   single monotone sequence -- these rational positions must be compared
   EXACTLY, with no rounding.

   Comparing two rationals `n1/d1` and `n2/d2` (positive denominators) is one
   cross-multiplication:

       n1/d1  <  n2/d2   <->   n1*d2  <  n2*d1.

   The right-hand side avoids division entirely, so the comparison is exact.
   The governing overflow question is the width of the products `n1*d2` and
   `n2*d1`.  Each factor is an `idet`, hence (over the paper's `cmax`
   coordinate window) bounded by `cmax^2 <= 2^63-1` -- so each product is
   bounded by `cmax^4`, which fits signed 128-bit: `cmax^4 <= 2^127-1`.  The
   difference `n1*d2 - n2*d1` (a single subtraction, whose sign IS the
   comparison result) also fits, `2*cmax^4 <= 2^127-1`.  Thus one int128
   cross-multiply totally orders edge positions with zero rounding -- the
   arithmetic brick the exact noding lane is gated on.

   This module lands (a) the comparator, (b) its correctness against the true
   real-number order of the ratios, and (c) the int128 fit.  Wiring the
   comparator to actual segment/segment intersection coordinates
   (num, den = specific `idet`s of the four endpoints) is a separate step.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith Lia Reals Lra.
From NTS.Proofs Require Import RelateIntDetBound.

Local Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The exact cross-multiply comparator.                                   *)
(*                                                                            *)
(* `pos_compare n1 d1 n2 d2` decides the order of the rationals n1/d1 and     *)
(* n2/d2 (for positive denominators) as a single integer cross-multiply.      *)
(* -------------------------------------------------------------------------- *)

Definition pos_compare (n1 d1 n2 d2 : Z) : comparison :=
  Z.compare (n1 * d2) (n2 * d1).

(* -------------------------------------------------------------------------- *)
(* §2  Correctness against the true real-number order of the ratios.          *)
(*                                                                            *)
(* The edge positions live in R (the corpus's coordinate field); the         *)
(* comparator computes their order without ever forming the quotient.         *)
(* -------------------------------------------------------------------------- *)

(* Clearing denominators: for positive b, d, the ratio order a/b vs c/d is
   the cross-multiplied order a*d vs c*b.  Pure real algebra. *)
Lemma ratio_lt_cross_real :
  forall a b c d : R,
    (0 < b)%R -> (0 < d)%R ->
    ((a / b < c / d)%R <-> (a * d < c * b)%R).
Proof.
  intros a b c d Hb Hd.
  assert (Hbd : (0 < b * d)%R) by (apply Rmult_lt_0_compat; assumption).
  split; intro H.
  - pose proof (Rmult_lt_compat_r (b * d) (a / b) (c / d) Hbd H) as H2.
    replace (a / b * (b * d))%R with (a * d)%R in H2 by (field; lra).
    replace (c / d * (b * d))%R with (c * b)%R in H2 by (field; lra).
    exact H2.
  - apply Rmult_lt_reg_r with (r := (b * d)%R); [ exact Hbd | ].
    replace (a / b * (b * d))%R with (a * d)%R by (field; lra).
    replace (c / d * (b * d))%R with (c * b)%R by (field; lra).
    exact H.
Qed.

Lemma ratio_eq_cross_real :
  forall a b c d : R,
    (0 < b)%R -> (0 < d)%R ->
    ((a / b = c / d)%R <-> (a * d = c * b)%R).
Proof.
  intros a b c d Hb Hd.
  assert (Hbd : (0 < b * d)%R) by (apply Rmult_lt_0_compat; assumption).
  assert (Hne : (b * d <> 0)%R) by (apply Rgt_not_eq; exact Hbd).
  split; intro H.
  - apply (Rmult_eq_compat_r (b * d)) in H.
    replace (a / b * (b * d))%R with (a * d)%R in H by (field; lra).
    replace (c / d * (b * d))%R with (c * b)%R in H by (field; lra).
    exact H.
  - apply (Rmult_eq_reg_r (b * d)); [ | exact Hne ].
    replace (a / b * (b * d))%R with (a * d)%R by (field; lra).
    replace (c / d * (b * d))%R with (c * b)%R by (field; lra).
    exact H.
Qed.

(* Positive integer denominator gives positive real denominator. *)
Lemma IZR_pos : forall d : Z, 0 < d -> (0 < IZR d)%R.
Proof.
  intros d Hd.
  assert (H : (IZR 0 < IZR d)%R) by (apply IZR_lt; exact Hd).
  change (IZR 0) with 0%R in H. exact H.
Qed.

(* The cross-multiplied real order is exactly the integer cross order. *)
Lemma cross_real_iff_Z :
  forall n1 d1 n2 d2 : Z,
    ((IZR n1 * IZR d2 < IZR n2 * IZR d1)%R <-> (n1 * d2 < n2 * d1)%Z).
Proof.
  intros n1 d1 n2 d2.
  rewrite <- !mult_IZR.
  split; [ apply lt_IZR | apply IZR_lt ].
Qed.

(* HEADLINE (strict): the cross-multiply decides the real ratio order. *)
Theorem pos_lt_iff_cross :
  forall n1 d1 n2 d2 : Z,
    0 < d1 -> 0 < d2 ->
    ((IZR n1 / IZR d1 < IZR n2 / IZR d2)%R <-> (n1 * d2 < n2 * d1)%Z).
Proof.
  intros n1 d1 n2 d2 Hd1 Hd2.
  rewrite (ratio_lt_cross_real (IZR n1) (IZR d1) (IZR n2) (IZR d2)
             (IZR_pos d1 Hd1) (IZR_pos d2 Hd2)).
  apply cross_real_iff_Z.
Qed.

(* HEADLINE (equality): equal ratios iff equal cross-products. *)
Theorem pos_eq_iff_cross :
  forall n1 d1 n2 d2 : Z,
    0 < d1 -> 0 < d2 ->
    ((IZR n1 / IZR d1 = IZR n2 / IZR d2)%R <-> (n1 * d2 = n2 * d1)%Z).
Proof.
  intros n1 d1 n2 d2 Hd1 Hd2.
  rewrite (ratio_eq_cross_real (IZR n1) (IZR d1) (IZR n2) (IZR d2)
             (IZR_pos d1 Hd1) (IZR_pos d2 Hd2)).
  rewrite <- !mult_IZR.
  split; [ apply eq_IZR | intro H; rewrite H; reflexivity ].
Qed.

(* FULL SPEC: `pos_compare` classifies the real ratio order three ways. *)
Theorem pos_compare_spec :
  forall n1 d1 n2 d2 : Z,
    0 < d1 -> 0 < d2 ->
    match pos_compare n1 d1 n2 d2 with
    | Lt => (IZR n1 / IZR d1 < IZR n2 / IZR d2)%R
    | Eq => (IZR n1 / IZR d1 = IZR n2 / IZR d2)%R
    | Gt => (IZR n2 / IZR d2 < IZR n1 / IZR d1)%R
    end.
Proof.
  intros n1 d1 n2 d2 Hd1 Hd2. unfold pos_compare.
  destruct (Z.compare_spec (n1 * d2) (n2 * d1)) as [He | Hl | Hg].
  - apply pos_eq_iff_cross; assumption.
  - apply pos_lt_iff_cross; assumption.
  - apply pos_lt_iff_cross; [ assumption | assumption | ].
    (* Gt: n2*d1 < n1*d2, i.e. the swapped strict cross order. *)
    lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  int128 fit of the cross-multiply.                                      *)
(*                                                                            *)
(* Over the paper's cmax coordinate window every orientation determinant is   *)
(* bounded by cmax^2 (RelateIntDetBound.idet_abs_le_sq); the cross-products   *)
(* and their difference then fit signed 128-bit.                             *)
(* -------------------------------------------------------------------------- *)

Definition int128_max : Z := 2 ^ 127 - 1.

(* cmax^4 fits int128 (product of two determinant-range values). *)
Theorem cmax_4th_le_int128 : (cmax * cmax) * (cmax * cmax) <= int128_max.
Proof. unfold int128_max, cmax. lia. Qed.

(* 2 * cmax^4 fits int128 (the difference of two such products). *)
Theorem cmax_2_4th_le_int128 : 2 * ((cmax * cmax) * (cmax * cmax)) <= int128_max.
Proof. unfold int128_max, cmax. lia. Qed.

(* Any two ratios whose numerators and denominators are within the
   determinant range [-cmax^2, cmax^2] cross-multiply inside int128, and the
   deciding difference does too -- one int128 op suffices. *)
Theorem pos_cross_fits_int128 :
  forall n1 d1 n2 d2 : Z,
    Z.abs n1 <= cmax * cmax -> Z.abs d1 <= cmax * cmax ->
    Z.abs n2 <= cmax * cmax -> Z.abs d2 <= cmax * cmax ->
    Z.abs (n1 * d2) <= int128_max /\
    Z.abs (n2 * d1) <= int128_max /\
    Z.abs (n1 * d2 - n2 * d1) <= int128_max.
Proof.
  intros n1 d1 n2 d2 Hn1 Hd1 Hn2 Hd2.
  pose proof cmax_4th_le_int128 as H4.
  pose proof cmax_2_4th_le_int128 as H24.
  assert (Hnn : 0 <= cmax * cmax) by (unfold cmax; lia).
  (* product bounds via |a*b| = |a|*|b| *)
  assert (P1 : Z.abs (n1 * d2) <= (cmax * cmax) * (cmax * cmax)).
  { rewrite Z.abs_mul. nia. }
  assert (P2 : Z.abs (n2 * d1) <= (cmax * cmax) * (cmax * cmax)).
  { rewrite Z.abs_mul. nia. }
  (* difference bound via triangle inequality *)
  assert (P3 : Z.abs (n1 * d2 - n2 * d1) <= Z.abs (n1 * d2) + Z.abs (n2 * d1)).
  { unfold Z.sub. eapply Z.le_trans; [ apply Z.abs_triangle | ].
    rewrite Z.abs_opp. lia. }
  repeat split; lia.
Qed.

(* Linkage: an orientation determinant over the cmax window lands in the
   determinant range the fit above assumes.  (Reuses idet_abs_le_sq.) *)
Corollary idet_abs_le_cmax_sq :
  forall ax ay bx by_ cx cy,
    0 <= ax <= cmax -> 0 <= ay <= cmax -> 0 <= bx <= cmax ->
    0 <= by_ <= cmax -> 0 <= cx <= cmax -> 0 <= cy <= cmax ->
    Z.abs (idet ax ay bx by_ cx cy) <= cmax * cmax.
Proof.
  intros. apply idet_abs_le_sq; try assumption. unfold cmax; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions pos_lt_iff_cross.
Print Assumptions pos_eq_iff_cross.
Print Assumptions pos_compare_spec.
Print Assumptions pos_cross_fits_int128.
Print Assumptions idet_abs_le_cmax_sq.
