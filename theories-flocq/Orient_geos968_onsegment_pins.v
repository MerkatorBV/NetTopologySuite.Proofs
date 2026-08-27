(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Orient_geos968_onsegment_pins
   ----------------------------------------------------------------------------
   Machine-checked binary64 pins for the two determinant scales behind
   GEOS #968 / libgeos/geos#1505 (`PointLocation::isOnSegment`).

   GEOS evaluates the Ozaki DAG (same intermediates as
   `CGAlgorithmsDD.orientationIndexFilter`):

       detleft  = (p0.x - p.x) * (p1.y - p.y)
       detright = (p0.y - p.y) * (p1.x - p.x)
       det      = detleft - detright
       errbound = |detleft + detright| * 3.3306690621773724e-16
       FAILURE  iff  |det| < errbound

   This file pins the arithmetic.  It does NOT prove the Ozaki bound
   sound, add an Ozaki FFI symbol, or remint ADR-0004.

   Two triples:

     #968  LINESTRING (1 0, 0 2) / POINT (0.9 0.2)
           and the mirror POINT (0.1 1.8).
           WKT decimals are collinear over ℝ.  Their binary64 encodings
           are not: the rounded det is −2⁻⁵⁴ ≈ −5.551115123125783e-17.

     Review pair (libgeos/geos#1505)
           LINESTRING (0 0, 1e16 1e16) / POINT (5e15, 5e15+1).
           Coordinates are exact integers.  The true cross is 10¹⁶.
           The rounded det is 2⁵³ = 9007199254740992.

   The #1505 membership cap `1e-12` is a new explicit absolute tolerance
   on |det|, not the Ozaki relative bound.  It sits strictly between
   those two measured |det| scales.

topic: binary64
claimId: none
witness: geos968-covers

   Not a minted micro-RGR / ADR-0004 teaching card.  Ozaki stays cold.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Abs, matching Orientation_b64.b64_abs (copied so this pin file depends    *)
(* only on Validate_binary64).                                               *)
(* -------------------------------------------------------------------------- *)

Definition default_abs_nan_b64
    (x : Binary.binary_float prec emax)
  : { z : Binary.binary_float prec emax | Binary.is_nan prec emax z = true } :=
  exist _ (Binary.B754_nan prec emax false 1 eq_refl) eq_refl.

Definition b64_abs (x : binary64) : binary64 :=
  Binary.Babs prec emax default_abs_nan_b64 x.

(* -------------------------------------------------------------------------- *)
(* GEOS PointLocation / orientationIndexFilter DAG.                          *)
(* -------------------------------------------------------------------------- *)

Definition b64_geos_detleft (p0 p1 p : BPoint) : binary64 :=
  b64_mult (b64_minus (bx p0) (bx p)) (b64_minus (by_ p1) (by_ p)).

Definition b64_geos_detright (p0 p1 p : BPoint) : binary64 :=
  b64_mult (b64_minus (by_ p0) (by_ p)) (b64_minus (bx p1) (bx p)).

Definition b64_geos_onsegment_det (p0 p1 p : BPoint) : binary64 :=
  b64_minus (b64_geos_detleft p0 p1 p) (b64_geos_detright p0 p1 p).

(* Published Ozaki double; pin only, not a soundness theorem. *)
Definition b64_ozaki_K : binary64 :=
  Binary.B754_finite prec emax false 6755399417329184 (-104) eq_refl.

Definition b64_ozaki_errbound (detleft detright : binary64) : binary64 :=
  b64_mult (b64_abs (b64_plus detleft detright)) b64_ozaki_K.

(* Strict |det| < errbound, matching GEOS FAILURE (CERTAIN uses >=). *)
Definition b64_ozaki_failure (p0 p1 p : BPoint) : bool :=
  match b64_compare
          (b64_abs (b64_geos_onsegment_det p0 p1 p))
          (b64_ozaki_errbound (b64_geos_detleft p0 p1 p)
                              (b64_geos_detright p0 p1 p))
  with
  | Some Lt => true
  | _ => false
  end.

(* #1505 membership cap: the binary64 constant written `1e-12`. *)
Definition b64_1e_12 : binary64 :=
  Binary.B754_finite prec emax false 4951760157141521 (-92) eq_refl.

(* Rounded #968 det is −2⁻⁵⁴ (sign true, m=2⁵², e=−106).
   Rounded review det is 2⁵³ (sign false, m=2⁵², e=1). *)

(* -------------------------------------------------------------------------- *)
(* Concrete points.                                                          *)
(* -------------------------------------------------------------------------- *)

Definition b64_0 : binary64 := Binary.B754_zero prec emax false.
Definition b64_1 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-52) eq_refl.
Definition b64_2 : binary64 :=
  Binary.B754_finite prec emax false 4503599627370496 (-51) eq_refl.
Definition b64_09 : binary64 :=
  Binary.B754_finite prec emax false 8106479329266893 (-53) eq_refl.
Definition b64_02 : binary64 :=
  Binary.B754_finite prec emax false 7205759403792794 (-55) eq_refl.
Definition b64_01 : binary64 :=
  Binary.B754_finite prec emax false 7205759403792794 (-56) eq_refl.
Definition b64_18 : binary64 :=
  Binary.B754_finite prec emax false 8106479329266893 (-52) eq_refl.
Definition b64_1e16 : binary64 :=
  Binary.B754_finite prec emax false 5000000000000000 1 eq_refl.
Definition b64_5e15 : binary64 :=
  Binary.B754_finite prec emax false 5000000000000000 0 eq_refl.
Definition b64_5e15p1 : binary64 :=
  Binary.B754_finite prec emax false 5000000000000001 0 eq_refl.

Definition p0_968 : BPoint := mkBP b64_1 b64_0.
Definition p1_968 : BPoint := mkBP b64_0 b64_2.
Definition q_968_orig : BPoint := mkBP b64_09 b64_02.
Definition q_968_mirror : BPoint := mkBP b64_01 b64_18.

Definition p0_rev : BPoint := mkBP b64_0 b64_0.
Definition p1_rev : BPoint := mkBP b64_1e16 b64_1e16.
Definition q_rev : BPoint := mkBP b64_5e15 b64_5e15p1.

(* -------------------------------------------------------------------------- *)
(* Helpers: B2R of the named powers of two.                                  *)
(* -------------------------------------------------------------------------- *)

Lemma bpow_zero : bpow radix2 0 = 1.
Proof. reflexivity. Qed.

Lemma IZR_two52 : IZR 4503599627370496 = bpow radix2 52.
Proof.
  replace 4503599627370496%Z with (Z.pow (radix_val radix2) 52) by reflexivity.
  apply IZR_Zpower. lia.
Qed.

Lemma B2R_finite_unsigned (m : positive) (e : Z) pf :
  Binary.B2R prec emax (Binary.B754_finite prec emax false m e pf) =
  IZR (Z.pos m) * bpow radix2 e.
Proof. reflexivity. Qed.

Lemma B2R_finite_signed (m : positive) (e : Z) pf :
  Binary.B2R prec emax (Binary.B754_finite prec emax true m e pf) =
  - IZR (Z.pos m) * bpow radix2 e.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* #968 decimals are collinear over ℝ; their binary64 encodings are not      *)
(* those decimals.                                                           *)
(* -------------------------------------------------------------------------- *)

Lemma geos968_decimal_collinear :
  (0 - 1) * (1 / 5 - 0) - (9 / 10 - 1) * (2 - 0) = 0.
Proof. lra. Qed.

Lemma geos968_b64_09_gt_dec :
  9 / 10 < Binary.B2R prec emax b64_09.
Proof.
  unfold b64_09.
  rewrite B2R_finite_unsigned.
  apply (Rmult_lt_reg_r (IZR 10 * bpow radix2 53%Z)).
  { apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]. }
  replace ((9 / 10) * (IZR 10 * bpow radix2 53%Z)) with (IZR 9 * bpow radix2 53%Z)
    by field.
  replace (IZR (Z.pos 8106479329266893) * bpow radix2 (-53)%Z
             * (IZR 10 * bpow radix2 53%Z))
    with (IZR (8106479329266893 * 10)).
  2: {
    replace (IZR (Z.pos 8106479329266893) * bpow radix2 (-53)%Z
               * (IZR 10 * bpow radix2 53%Z))
      with (IZR (Z.pos 8106479329266893) * IZR 10 * (bpow radix2 (-53)%Z * bpow radix2 53%Z))
      by ring.
    rewrite <- bpow_plus.
    replace ((-53) + 53)%Z with 0%Z by reflexivity.
    rewrite bpow_zero, Rmult_1_r, <- mult_IZR.
    reflexivity.
  }
  rewrite <- (IZR_Zpower radix2 53%Z) by lia.
  rewrite <- mult_IZR.
  replace (Z.pow (radix_val radix2) 53) with (2 ^ 53)%Z by reflexivity.
  apply IZR_lt. lia.
Qed.

Lemma geos968_b64_02_gt_dec :
  1 / 5 < Binary.B2R prec emax b64_02.
Proof.
  unfold b64_02.
  rewrite B2R_finite_unsigned.
  apply (Rmult_lt_reg_r (IZR 5 * bpow radix2 55%Z)).
  { apply Rmult_lt_0_compat; [apply IZR_lt; lia | apply bpow_gt_0]. }
  replace ((1 / 5) * (IZR 5 * bpow radix2 55%Z)) with (bpow radix2 55%Z) by field.
  replace (IZR (Z.pos 7205759403792794) * bpow radix2 (-55)%Z
             * (IZR 5 * bpow radix2 55%Z))
    with (IZR (7205759403792794 * 5)).
  2: {
    replace (IZR (Z.pos 7205759403792794) * bpow radix2 (-55)%Z
               * (IZR 5 * bpow radix2 55%Z))
      with (IZR (Z.pos 7205759403792794) * IZR 5 * (bpow radix2 (-55)%Z * bpow radix2 55%Z))
      by ring.
    rewrite <- bpow_plus.
    replace ((-55) + 55)%Z with 0%Z by reflexivity.
    rewrite bpow_zero, Rmult_1_r, <- mult_IZR.
    reflexivity.
  }
  rewrite <- (IZR_Zpower radix2 55%Z) by lia.
  replace (Z.pow (radix_val radix2) 55) with (2 ^ 55)%Z by reflexivity.
  apply IZR_lt. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Rounded dets.                                                             *)
(* -------------------------------------------------------------------------- *)

(* Constructor proofs of `bounded` differ after rounding; pin the payload. *)
Lemma geos968_orig_payload :
  match b64_geos_onsegment_det p0_968 p1_968 q_968_orig with
  | Binary.B754_finite _ _ s m e _ =>
      s = true /\ m = 4503599627370496%positive /\ e = (-106)%Z
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma geos968_mirror_payload :
  match b64_geos_onsegment_det p0_968 p1_968 q_968_mirror with
  | Binary.B754_finite _ _ s m e _ =>
      s = true /\ m = 4503599627370496%positive /\ e = (-106)%Z
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma geos1505_review_payload :
  match b64_geos_onsegment_det p0_rev p1_rev q_rev with
  | Binary.B754_finite _ _ s m e _ =>
      s = false /\ m = 4503599627370496%positive /\ e = 1%Z
  | _ => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma geos968_orig_det_B2R :
  Binary.B2R prec emax (b64_geos_onsegment_det p0_968 p1_968 q_968_orig)
    = - bpow radix2 (-54).
Proof.
  set (x := b64_geos_onsegment_det p0_968 p1_968 q_968_orig).
  assert (H : match x with
              | Binary.B754_finite _ _ s m e _ =>
                  s = true /\ m = 4503599627370496%positive /\ e = (-106)%Z
              | _ => False
              end).
  { subst x. exact geos968_orig_payload. }
  destruct x as [s | s | s pl Hpl | s m e He]; try contradiction.
  destruct H as (Hs & Hm & He0). subst s m e.
  rewrite B2R_finite_signed.
  replace (IZR (Z.pos 4503599627370496)) with (bpow radix2 52) by apply IZR_two52.
  rewrite <- Ropp_mult_distr_l, <- bpow_plus.
  reflexivity.
Qed.

Lemma geos968_mirror_det_B2R :
  Binary.B2R prec emax (b64_geos_onsegment_det p0_968 p1_968 q_968_mirror)
    = - bpow radix2 (-54).
Proof.
  set (x := b64_geos_onsegment_det p0_968 p1_968 q_968_mirror).
  assert (H : match x with
              | Binary.B754_finite _ _ s m e _ =>
                  s = true /\ m = 4503599627370496%positive /\ e = (-106)%Z
              | _ => False
              end).
  { subst x. exact geos968_mirror_payload. }
  destruct x as [s | s | s pl Hpl | s m e He]; try contradiction.
  destruct H as (Hs & Hm & He0). subst s m e.
  rewrite B2R_finite_signed.
  replace (IZR (Z.pos 4503599627370496)) with (bpow radix2 52) by apply IZR_two52.
  rewrite <- Ropp_mult_distr_l, <- bpow_plus.
  reflexivity.
Qed.

Lemma geos1505_review_det_B2R :
  Binary.B2R prec emax (b64_geos_onsegment_det p0_rev p1_rev q_rev)
    = IZR (2 ^ 53).
Proof.
  set (x := b64_geos_onsegment_det p0_rev p1_rev q_rev).
  assert (H : match x with
              | Binary.B754_finite _ _ s m e _ =>
                  s = false /\ m = 4503599627370496%positive /\ e = 1%Z
              | _ => False
              end).
  { subst x. exact geos1505_review_payload. }
  destruct x as [s | s | s pl Hpl | s m e He]; try contradiction.
  destruct H as (Hs & Hm & He0). subst s m e.
  rewrite B2R_finite_unsigned.
  replace (IZR (Z.pos 4503599627370496)) with (bpow radix2 52) by apply IZR_two52.
  rewrite <- bpow_plus.
  replace (bpow radix2 53) with (IZR (2 ^ 53)).
  2: {
    replace (2 ^ 53)%Z with (Z.pow (radix_val radix2) 53) by reflexivity.
    apply IZR_Zpower. lia.
  }
  reflexivity.
Qed.

Lemma geos968_orig_ozaki_failure :
  b64_ozaki_failure p0_968 p1_968 q_968_orig = true.
Proof. vm_compute. reflexivity. Qed.

Lemma geos968_mirror_ozaki_failure :
  b64_ozaki_failure p0_968 p1_968 q_968_mirror = true.
Proof. vm_compute. reflexivity. Qed.

Lemma geos1505_review_ozaki_failure :
  b64_ozaki_failure p0_rev p1_rev q_rev = true.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Review pair: coordinates are the integers; true cross is 10¹⁶.            *)
(* -------------------------------------------------------------------------- *)

Lemma B2R_b64_0 : Binary.B2R prec emax b64_0 = 0.
Proof. reflexivity. Qed.

Lemma B2R_b64_1e16 :
  Binary.B2R prec emax b64_1e16 = IZR 10000000000000000.
Proof.
  unfold b64_1e16.
  rewrite B2R_finite_unsigned, bpow_1, <- mult_IZR.
  reflexivity.
Qed.

Lemma B2R_b64_5e15 :
  Binary.B2R prec emax b64_5e15 = IZR 5000000000000000.
Proof.
  unfold b64_5e15.
  rewrite B2R_finite_unsigned, bpow_zero, Rmult_1_r.
  reflexivity.
Qed.

Lemma B2R_b64_5e15p1 :
  Binary.B2R prec emax b64_5e15p1 = IZR 5000000000000001.
Proof.
  unfold b64_5e15p1.
  rewrite B2R_finite_unsigned, bpow_zero, Rmult_1_r.
  reflexivity.
Qed.

Lemma geos1505_review_true_cross :
  (Binary.B2R prec emax (bx p1_rev) - Binary.B2R prec emax (bx p0_rev))
    * (Binary.B2R prec emax (by_ q_rev) - Binary.B2R prec emax (by_ p0_rev))
  - (Binary.B2R prec emax (bx q_rev) - Binary.B2R prec emax (bx p0_rev))
    * (Binary.B2R prec emax (by_ p1_rev) - Binary.B2R prec emax (by_ p0_rev))
  = IZR 10000000000000000.
Proof.
  unfold p0_rev, p1_rev, q_rev.
  cbn [bx by_].
  rewrite B2R_b64_0, B2R_b64_1e16, B2R_b64_5e15, B2R_b64_5e15p1.
  rewrite !Rminus_0_r.
  rewrite <- !mult_IZR, <- minus_IZR.
  reflexivity.
Qed.

Lemma geos1505_review_rounded_ne_true :
  IZR (2 ^ 53) <> IZR 10000000000000000.
Proof.
  intros H.
  apply eq_IZR in H.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* 2⁻⁵⁴ < B2R(1e-12) < 2⁵³, and 1e-12 is not the Ozaki K.                    *)
(* -------------------------------------------------------------------------- *)

Lemma two_pow_m54_lt_1e_12 :
  bpow radix2 (-54) < Binary.B2R prec emax b64_1e_12.
Proof.
  unfold b64_1e_12.
  rewrite B2R_finite_unsigned.
  apply (Rmult_lt_reg_r (bpow radix2 106%Z)); [apply bpow_gt_0 |].
  rewrite <- bpow_plus.
  rewrite (Rmult_assoc (IZR (Z.pos 4951760157141521))), <- bpow_plus.
  replace ((-54) + 106)%Z with 52%Z by reflexivity.
  replace ((-92) + 106)%Z with 14%Z by reflexivity.
  rewrite <- (IZR_Zpower radix2 52%Z) by lia.
  rewrite <- (IZR_Zpower radix2 14%Z) by lia.
  rewrite <- mult_IZR.
  replace (Z.pow (radix_val radix2) 52) with (2 ^ 52)%Z by reflexivity.
  replace (Z.pow (radix_val radix2) 14) with (2 ^ 14)%Z by reflexivity.
  apply IZR_lt.
  lia.
Qed.

Lemma one_e_12_lt_two_pow_53 :
  Binary.B2R prec emax b64_1e_12 < IZR (2 ^ 53).
Proof.
  unfold b64_1e_12.
  rewrite B2R_finite_unsigned.
  apply (Rmult_lt_reg_r (bpow radix2 92%Z)); [apply bpow_gt_0 |].
  rewrite (Rmult_assoc (IZR (Z.pos 4951760157141521))), <- bpow_plus.
  replace ((-92) + 92)%Z with 0%Z by reflexivity.
  rewrite bpow_zero, Rmult_1_r.
  replace (IZR (2 ^ 53) * bpow radix2 92%Z)
    with (IZR (2 ^ 53 * 2 ^ 92)).
  2: {
    rewrite <- (IZR_Zpower radix2 92%Z) by lia.
    rewrite <- mult_IZR.
    reflexivity.
  }
  replace (Z.pow (radix_val radix2) 92) with (2 ^ 92)%Z by reflexivity.
  apply IZR_lt.
  lia.
Qed.

Lemma geos1505_tol_neq_ozaki_K :
  Binary.B2R prec emax b64_1e_12 <> Binary.B2R prec emax b64_ozaki_K.
Proof.
  unfold b64_1e_12, b64_ozaki_K.
  rewrite !B2R_finite_unsigned.
  intros H.
  apply (Rmult_eq_compat_r (bpow radix2 104%Z)) in H.
  rewrite (Rmult_assoc (IZR (Z.pos 4951760157141521))), <- bpow_plus in H.
  rewrite (Rmult_assoc (IZR (Z.pos 6755399417329184))), <- bpow_plus in H.
  replace ((-92) + 104)%Z with 12%Z in H by reflexivity.
  replace ((-104) + 104)%Z with 0%Z in H by reflexivity.
  rewrite bpow_zero, Rmult_1_r in H.
  rewrite <- (IZR_Zpower radix2 12%Z) in H by lia.
  rewrite <- mult_IZR in H.
  replace (Z.pow (radix_val radix2) 12) with (2 ^ 12)%Z in H by reflexivity.
  apply eq_IZR in H.
  discriminate.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: the two measured |det| scales and the #1505 cap between them.   *)
(* -------------------------------------------------------------------------- *)

Theorem geos1505_onsegment_det_scales :
  Binary.B2R prec emax (b64_geos_onsegment_det p0_968 p1_968 q_968_orig)
    = - bpow radix2 (-54)
  /\ Binary.B2R prec emax (b64_geos_onsegment_det p0_968 p1_968 q_968_mirror)
    = - bpow radix2 (-54)
  /\ Binary.B2R prec emax (b64_geos_onsegment_det p0_rev p1_rev q_rev)
    = IZR (2 ^ 53)
  /\ Rabs (Binary.B2R prec emax (b64_geos_onsegment_det p0_968 p1_968 q_968_orig))
       < Binary.B2R prec emax b64_1e_12
  /\ Binary.B2R prec emax b64_1e_12
       < Rabs (Binary.B2R prec emax (b64_geos_onsegment_det p0_rev p1_rev q_rev)).
Proof.
  rewrite geos968_orig_det_B2R, geos968_mirror_det_B2R, geos1505_review_det_B2R.
  split; [reflexivity |].
  split; [reflexivity |].
  split; [reflexivity |].
  rewrite Rabs_Ropp.
  rewrite (Rabs_right (bpow radix2 (-54)))
    by (apply Rle_ge; apply Rlt_le; apply bpow_gt_0).
  rewrite (Rabs_right (IZR (2 ^ 53)))
    by (apply Rle_ge; apply IZR_le; lia).
  split.
  - apply two_pow_m54_lt_1e_12.
  - apply one_e_12_lt_two_pow_53.
Qed.

Print Assumptions geos1505_onsegment_det_scales.
Print Assumptions geos968_decimal_collinear.
Print Assumptions geos1505_review_true_cross.
Print Assumptions geos968_orig_ozaki_failure.
Print Assumptions geos1505_review_ozaki_failure.
Print Assumptions geos1505_tol_neq_ozaki_K.
