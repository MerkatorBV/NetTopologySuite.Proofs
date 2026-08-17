(* ============================================================================
   NetTopologySuite.Proofs.RocqRefRunner
   ----------------------------------------------------------------------------
   The JTS / NTS RocqRefRunner integer algorithm is this Z determinant
   sign.  JTS reconstructs it in Java (`RocqRefRunner.refSign`); the NTS
   catalyst port reconstructs the same formula in C# (`RocqRefRunner.RefSign`).

   This file does NOT claim that production `Orientation.index` (double-
   double) is sound.  It proves that the RocqRefRunner *reference*
   algorithm — the thing both ports compute — is the exact orientation
   sign of the integer points, and that a signed 64-bit `long` is wide
   enough to evaluate it on the certified domain |coord| <= 2^25.

   Formula (JTS RocqRefRunner.refSign / theories/Orientation.v `cross`):

       det = (p1x - p0x) * (qy - p0y) - (qx - p0x) * (p1y - p0y)
       sign = sgn(det)     (* -1 CW, 0 collinear, +1 CCW *)

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
   ========================================================================== *)

From Stdlib Require Import Reals ZArith Lia Lra.
From NTS.Proofs Require Import Distance Orientation.

Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* Domain: the JTS / NTS SAFE_BOUND.                                          *)
(* -------------------------------------------------------------------------- *)

Definition rocqref_SAFE_BOUND : Z := 2 ^ 25.

Definition rocqref_in_domain (c : Z) : Prop :=
  - rocqref_SAFE_BOUND <= c <= rocqref_SAFE_BOUND.

(* -------------------------------------------------------------------------- *)
(* The algorithm both language ports implement.                               *)
(* -------------------------------------------------------------------------- *)

Definition rocqref_idet (p0x p0y p1x p1y qx qy : Z) : Z :=
  (p1x - p0x) * (qy - p0y) - (qx - p0x) * (p1y - p0y).

Definition rocqref_refSign (p0x p0y p1x p1y qx qy : Z) : Z :=
  Z.sgn (rocqref_idet p0x p0y p1x p1y qx qy).

(* -------------------------------------------------------------------------- *)
(* det as IZR equals the real `cross` of the embedded points.                 *)
(* -------------------------------------------------------------------------- *)

Lemma rocqref_idet_IZR :
  forall p0x p0y p1x p1y qx qy,
    IZR (rocqref_idet p0x p0y p1x p1y qx qy) =
    cross (mkPoint (IZR p0x) (IZR p0y))
          (mkPoint (IZR p1x) (IZR p1y))
          (mkPoint (IZR qx) (IZR qy)).
Proof.
  intros p0x p0y p1x p1y qx qy.
  unfold rocqref_idet, cross, px, py; simpl.
  rewrite !minus_IZR, !mult_IZR, !minus_IZR.
  ring.
Qed.

Lemma sgn_1_iff : forall n : Z, Z.sgn n = 1 <-> 0 < n.
Proof.
  intros n. unfold Z.sgn. destruct n; simpl; split; intro H; lia || discriminate.
Qed.

Lemma sgn_m1_iff : forall n : Z, Z.sgn n = (-1) <-> n < 0.
Proof.
  intros n. unfold Z.sgn. destruct n; simpl; split; intro H; lia || discriminate.
Qed.

Lemma sgn_0_iff : forall n : Z, Z.sgn n = 0 <-> n = 0.
Proof.
  intros n. unfold Z.sgn. destruct n; simpl; split; intro H; lia || discriminate.
Qed.

Lemma IZR_pos_iff : forall n : Z, (0 < IZR n)%R <-> 0 < n.
Proof.
  intros n. split.
  - intro H. apply (lt_IZR 0 n). change (IZR 0) with 0%R. exact H.
  - intro H. apply (IZR_lt 0 n) in H. change (IZR 0) with 0%R in H. exact H.
Qed.

Lemma IZR_neg_iff : forall n : Z, (IZR n < 0)%R <-> n < 0.
Proof.
  intros n. split.
  - intro H. apply (lt_IZR n 0). change (IZR 0) with 0%R. exact H.
  - intro H. apply (IZR_lt n 0) in H. change (IZR 0) with 0%R in H. exact H.
Qed.

Lemma IZR_zero_iff : forall n : Z, IZR n = 0%R <-> n = 0.
Proof.
  intros n. split.
  - intro H. apply (eq_IZR n 0). change (IZR 0) with 0%R. exact H.
  - intro H. rewrite H. change (IZR 0) with 0%R. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: RocqRefRunner.refSign is the exact orientation of the Z-points.  *)
(* -------------------------------------------------------------------------- *)

Theorem rocqref_refSign_eq_cross :
  forall p0x p0y p1x p1y qx qy,
    let P0 := mkPoint (IZR p0x) (IZR p0y) in
    let P1 := mkPoint (IZR p1x) (IZR p1y) in
    let Q  := mkPoint (IZR qx) (IZR qy) in
    (0 < cross P0 P1 Q   <-> rocqref_refSign p0x p0y p1x p1y qx qy = 1) /\
    (cross P0 P1 Q < 0   <-> rocqref_refSign p0x p0y p1x p1y qx qy = (-1)) /\
    (cross P0 P1 Q = 0   <-> rocqref_refSign p0x p0y p1x p1y qx qy = 0).
Proof.
  intros p0x p0y p1x p1y qx qy.
  unfold rocqref_refSign.
  rewrite <- rocqref_idet_IZR.
  split; [|split].
  - rewrite sgn_1_iff. rewrite IZR_pos_iff. reflexivity.
  - rewrite sgn_m1_iff. rewrite IZR_neg_iff. reflexivity.
  - rewrite sgn_0_iff. rewrite IZR_zero_iff. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* |coord| <= 2^25  ⇒  |det| <= 2^53  ⇒  signed 64-bit `long` is exact.       *)
(* This is the JTS class-doc argument (diffs 2^26, products 2^52, det 2^53).  *)
(* -------------------------------------------------------------------------- *)

Lemma rocqref_diff_bound :
  forall a b,
    rocqref_in_domain a ->
    rocqref_in_domain b ->
    Z.abs (a - b) <= 2 ^ 26.
Proof.
  intros a b Ha Hb.
  unfold rocqref_in_domain, rocqref_SAFE_BOUND in *.
  lia.
Qed.

Lemma rocqref_idet_abs_le_2pow53 :
  forall p0x p0y p1x p1y qx qy,
    rocqref_in_domain p0x -> rocqref_in_domain p0y ->
    rocqref_in_domain p1x -> rocqref_in_domain p1y ->
    rocqref_in_domain qx  -> rocqref_in_domain qy  ->
    Z.abs (rocqref_idet p0x p0y p1x p1y qx qy) <= 2 ^ 53.
Proof.
  intros p0x p0y p1x p1y qx qy H0x H0y H1x H1y Hqx Hqy.
  unfold rocqref_idet.
  pose proof (rocqref_diff_bound p1x p0x H1x H0x) as Hd1.
  pose proof (rocqref_diff_bound qy p0y Hqy H0y) as Hd2.
  pose proof (rocqref_diff_bound qx p0x Hqx H0x) as Hd3.
  pose proof (rocqref_diff_bound p1y p0y H1y H0y) as Hd4.
  unfold rocqref_SAFE_BOUND in *.
  assert (Hp1 : Z.abs ((p1x - p0x) * (qy - p0y)) <= 2 ^ 52).
  { rewrite Z.abs_mul. nia. }
  assert (Hp2 : Z.abs ((qx - p0x) * (p1y - p0y)) <= 2 ^ 52).
  { rewrite Z.abs_mul. nia. }
  nia.
Qed.

Theorem rocqref_idet_fits_int64 :
  forall p0x p0y p1x p1y qx qy,
    rocqref_in_domain p0x -> rocqref_in_domain p0y ->
    rocqref_in_domain p1x -> rocqref_in_domain p1y ->
    rocqref_in_domain qx  -> rocqref_in_domain qy  ->
    Z.abs (rocqref_idet p0x p0y p1x p1y qx qy) <= 2 ^ 63 - 1.
Proof.
  intros p0x p0y p1x p1y qx qy H0x H0y H1x H1y Hqx Hqy.
  pose proof (rocqref_idet_abs_le_2pow53
                p0x p0y p1x p1y qx qy H0x H0y H1x H1y Hqx Hqy) as H.
  lia.
Qed.

(* Locked pins: the same unit triangles both language ports ship. *)

Example rocqref_unit_ccw : rocqref_refSign 0 0 1 0 0 1 = 1.
Proof. reflexivity. Qed.

Example rocqref_unit_cw : rocqref_refSign 0 0 1 0 0 (-1) = (-1).
Proof. reflexivity. Qed.

Example rocqref_unit_collinear : rocqref_refSign 0 0 2 2 1 1 = 0.
Proof. reflexivity. Qed.
