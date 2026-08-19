(* ============================================================================
   NetTopologySuite.Proofs.Flocq.InCircle_b64_exact_refs
   ----------------------------------------------------------------------------
   PURE-Z / PURE-R KERNEL: the integer-determinant algebra that the
   binary64 in-circle sign and integer-regime stories factor through.

     - eight-way `Z.min` fold
     - IZR packing lemmas for products, squares, and the degree-4 det
     - `|n| <= 2^k` magnitude bounds used by the `2^11` integer regime

   This module imports NO Flocq: its Print Assumptions footprint is the
   standard Reals trio only (no `Classical_Prop.classic`), so it is
   deliberately NOT on docs/audit-exceptions.txt -- the first
   InCircle-lineage module to leave the Category C1 block, mirroring
   Intersect_b64_exact_refs.v and the slice-12 half of
   PassesThrough_b64_grid_gap_kernel.v (meso-audit B4).

   Split out of the former 1205-line InCircle_b64_exact.v monolith
   (issue #64 ask #4b; topic: binary64, claimId: 64-d, witness:
   perron-sliver); InCircle_b64_exact.v remains as the Require Export
   umbrella, so reverse dependencies import unchanged.  Declarations
   and proofs carried over verbatim.  No Admitted, no Axiom, no
   Parameter.
   topic: binary64
   claimId: 64-d
   witness: none
   ============================================================================ *)

From Stdlib Require Import Reals ZArith Lia.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Eight-way Z.min fold (common-exponent selection).                          *)
(* -------------------------------------------------------------------------- *)

Definition Zfold_min8 (e1 e2 e3 e4 e5 e6 e7 e8 : Z) : Z :=
  Z.min e1 (Z.min e2 (Z.min e3 (Z.min e4 (Z.min e5 (Z.min e6 (Z.min e7 e8)))))).

Lemma Zfold_min8_le1 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e1)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le2 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e2)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le3 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e3)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le4 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e4)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le5 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e5)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le6 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e6)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le7 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e7)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

Lemma Zfold_min8_le8 : forall e1 e2 e3 e4 e5 e6 e7 e8 : Z,
  (Zfold_min8 e1 e2 e3 e4 e5 e6 e7 e8 <= e8)%Z.
Proof. intros. unfold Zfold_min8. lia. Qed.

(* -------------------------------------------------------------------------- *)
(* IZR packing for the degree-4 in-circle determinant.                        *)
(* -------------------------------------------------------------------------- *)

Lemma IZR_mul_diff (za zc : Z) (rb : R) :
  IZR za * rb - IZR zc * rb = IZR (za - zc)%Z * rb.
Proof. rewrite <- Rmult_minus_distr_r, minus_IZR. reflexivity. Qed.

Lemma IZR_mul_sq (za : Z) (rb : R) :
  (IZR za * rb) * (IZR za * rb) = IZR (za * za)%Z * (rb * rb).
Proof.
  transitivity (IZR za * IZR za * rb * rb); [ring |].
  rewrite mult_IZR. ring.
Qed.

Lemma IZR_sq_sum (z1 z2 : Z) :
  IZR z1 * IZR z1 + IZR z2 * IZR z2 = IZR (z1 * z1 + z2 * z2)%Z.
Proof.
  rewrite <- !mult_IZR.
  rewrite <- plus_IZR.
  reflexivity.
Qed.

Lemma IZR_coord_sq_pair (z1 z2 : Z) (b : R) :
  (IZR z1 * b) * (IZR z1 * b) + (IZR z2 * b) * (IZR z2 * b)
  = IZR ((z1 * z1 + z2 * z2)%Z) * (b * b).
Proof.
  rewrite !IZR_mul_sq.
  rewrite <- Rmult_plus_distr_r, plus_IZR.
  reflexivity.
Qed.

Lemma inCircle_Zdet_distrib :
  forall (axz ayz bxz byz cxz cyz : Z),
  (axz * byz * (cxz * cxz + cyz * cyz) - axz * cyz * (bxz * bxz + byz * byz)
   - ayz * bxz * (cxz * cxz + cyz * cyz) + ayz * cxz * (bxz * bxz + byz * byz)
   + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z
  = (axz * (byz * (cxz * cxz + cyz * cyz) - cyz * (bxz * bxz + byz * byz))%Z
     - ayz * (bxz * (cxz * cxz + cyz * cyz) - cxz * (bxz * bxz + byz * byz))%Z
     + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z.
Proof.
  intros.
  Open Scope Z_scope.
  ring.
  Close Scope Z_scope.
Qed.

Lemma inCircle_shift_quartic_IZR_pack :
  forall (axz ayz bxz byz cxz cyz : Z),
  IZR axz * (IZR byz * IZR ((cxz * cxz + cyz * cyz)%Z) - IZR cyz * IZR ((bxz * bxz + byz * byz)%Z))
  - IZR ayz * (IZR bxz * IZR ((cxz * cxz + cyz * cyz)%Z) - IZR cxz * IZR ((bxz * bxz + byz * byz)%Z))
  + IZR ((axz * axz + ayz * ayz)%Z)
    * (IZR bxz * IZR cyz - IZR cxz * IZR byz)
  = IZR ((axz * byz * (cxz * cxz + cyz * cyz)
          - axz * cyz * (bxz * bxz + byz * byz)
          - ayz * bxz * (cxz * cxz + cyz * cyz)
          + ayz * cxz * (bxz * bxz + byz * byz)
          + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z).
Proof.
  intros axz ayz bxz byz cxz cyz.
  repeat rewrite Rmult_minus_distr_l.
  repeat rewrite Rmult_assoc.
  repeat rewrite mult_IZR.
  repeat rewrite minus_IZR.
  repeat rewrite Rmult_minus_distr_l.
  repeat rewrite Rmult_assoc.
  repeat rewrite <- mult_IZR.
  repeat rewrite <- minus_IZR.
  repeat rewrite <- plus_IZR.
  f_equal.
  Open Scope Z_scope.
  ring.
  Close Scope Z_scope.
Qed.

Lemma inCircle_shift_quartic_homog :
  forall (axz ayz bxz byz cxz cyz : Z) (b : R),
  (IZR axz * b) * ((IZR byz * b) * (IZR ((cxz * cxz + cyz * cyz)%Z) * (b * b))
                   - (IZR cyz * b) * (IZR ((bxz * bxz + byz * byz)%Z) * (b * b)))
  - (IZR ayz * b) * ((IZR bxz * b) * (IZR ((cxz * cxz + cyz * cyz)%Z) * (b * b))
                   - (IZR cxz * b) * (IZR ((bxz * bxz + byz * byz)%Z) * (b * b)))
  + (IZR ((axz * axz + ayz * ayz)%Z) * (b * b))
    * ((IZR bxz * b) * (IZR cyz * b) - (IZR cxz * b) * (IZR byz * b))
  = (b * b * b * b)
    * IZR ((axz * (byz * (cxz * cxz + cyz * cyz) - cyz * (bxz * bxz + byz * byz))%Z
            - ayz * (bxz * (cxz * cxz + cyz * cyz) - cxz * (bxz * bxz + byz * byz))%Z
            + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z).
Proof.
  intros axz ayz bxz byz cxz cyz b.
  set (uax := IZR axz).
  set (uay := IZR ayz).
  set (ubx := IZR bxz).
  set (uby := IZR byz).
  set (ucx := IZR cxz).
  set (ucy := IZR cyz).
  set (una := IZR ((axz * axz + ayz * ayz)%Z)).
  set (unb := IZR ((bxz * bxz + byz * byz)%Z)).
  set (unc := IZR ((cxz * cxz + cyz * cyz)%Z)).
  transitivity (b * b * b * b
    * (uax * (uby * unc - ucy * unb)
       - uay * (ubx * unc - ucx * unb)
       + una * (ubx * ucy - ucx * uby))).
  - repeat (match goal with
            | |- context[IZR axz] => change (IZR axz) with uax
            | |- context[IZR ayz] => change (IZR ayz) with uay
            | |- context[IZR bxz] => change (IZR bxz) with ubx
            | |- context[IZR byz] => change (IZR byz) with uby
            | |- context[IZR cxz] => change (IZR cxz) with ucx
            | |- context[IZR cyz] => change (IZR cyz) with ucy
            | |- context[IZR ((axz * axz + ayz * ayz)%Z)] =>
                change (IZR ((axz * axz + ayz * ayz)%Z)) with una
            | |- context[IZR ((bxz * bxz + byz * byz)%Z)] =>
                change (IZR ((bxz * bxz + byz * byz)%Z)) with unb
            | |- context[IZR ((cxz * cxz + cyz * cyz)%Z)] =>
                change (IZR ((cxz * cxz + cyz * cyz)%Z)) with unc
            end).
    ring.
  - f_equal.
    transitivity (IZR ((axz * byz * (cxz * cxz + cyz * cyz)
                        - axz * cyz * (bxz * bxz + byz * byz)
                        - ayz * bxz * (cxz * cxz + cyz * cyz)
                        + ayz * cxz * (bxz * bxz + byz * byz)
                        + (axz * axz + ayz * ayz) * (bxz * cyz - cxz * byz))%Z)).
    + unfold uax, uay, ubx, uby, ucx, ucy, una, unb, unc.
      apply inCircle_shift_quartic_IZR_pack.
    + f_equal. apply inCircle_Zdet_distrib.
Qed.

Lemma IZR_na_cross_pack (na bx' by' cx cy : Z) :
  IZR na * (IZR bx' * IZR cy - IZR cx * IZR by')
  = IZR na * IZR (bx' * cy - cx * by').
Proof.
  f_equal.
  rewrite <- mult_IZR.
  rewrite <- mult_IZR.
  rewrite <- minus_IZR.
  reflexivity.
Qed.

Lemma inCircle_det_IZR_pack :
  forall (ax ay bx' by' cx cy na nb nc : Z),
  IZR ax * (IZR by' * IZR nc - IZR cy * IZR nb)
  - IZR ay * (IZR bx' * IZR nc - IZR cx * IZR nb)
  + IZR na * IZR (bx' * cy - cx * by')
  = IZR (ax * (by' * nc - cy * nb)
         - ay * (bx' * nc - cx * nb)
         + na * (bx' * cy - cx * by'))%Z.
Proof.
  intros.
  transitivity (IZR ax * (IZR (by' * nc)%Z - IZR (cy * nb)%Z)
                  - IZR ay * (IZR (bx' * nc)%Z - IZR (cx * nb)%Z)
                  + IZR (na * (bx' * cy - cx * by'))%Z).
  { repeat rewrite mult_IZR. reflexivity. }
  pose proof (minus_IZR (by' * nc)%Z (cy * nb)%Z) as H1.
  pose proof (minus_IZR (bx' * nc)%Z (cx * nb)%Z) as H2.
  rewrite <- H1.
  rewrite <- H2.
  transitivity (IZR (ax * (by' * nc - cy * nb))%Z - IZR (ay * (bx' * nc - cx * nb))%Z
                  + IZR (na * (bx' * cy - cx * by'))%Z).
  { repeat rewrite mult_IZR. reflexivity. }
  pose proof (minus_IZR (ax * (by' * nc - cy * nb))%Z (ay * (bx' * nc - cx * nb))%Z) as H3.
  rewrite <- H3.
  rewrite <- plus_IZR.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Magnitude bounds for the `|coord| <= 2^11` integer regime.                 *)
(* -------------------------------------------------------------------------- *)

Lemma arc_diff_bound_2p12 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 11)%Z -> (Z.abs b <= 2 ^ 11)%Z ->
    (Z.abs (a - b) <= 2 ^ 12)%Z.
Proof. intros. replace (2 ^ 12)%Z with (2 ^ 11 + 2 ^ 11)%Z by lia. lia. Qed.

Lemma arc_sq_bound_2p24 :
  forall (a : Z),
    (Z.abs a <= 2 ^ 12)%Z -> (Z.abs (a * a) <= 2 ^ 24)%Z.
Proof.
  intros a Ha.
  rewrite Z.abs_mul.
  replace (2 ^ 24)%Z with (2 ^ 12 * 2 ^ 12)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma arc_sum_sq_bound_2p25 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 24)%Z -> (Z.abs b <= 2 ^ 24)%Z ->
    (Z.abs (a + b) <= 2 ^ 25)%Z.
Proof. intros. replace (2 ^ 25)%Z with (2 ^ 24 + 2 ^ 24)%Z by lia. lia. Qed.

Lemma arc_product_bound_2p24 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 12)%Z -> (Z.abs b <= 2 ^ 12)%Z ->
    (Z.abs (a * b) <= 2 ^ 24)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 24)%Z with (2 ^ 12 * 2 ^ 12)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma arc_product_bound_2p37 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 12)%Z -> (Z.abs b <= 2 ^ 25)%Z ->
    (Z.abs (a * b) <= 2 ^ 37)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 37)%Z with (2 ^ 12 * 2 ^ 25)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma arc_product_bound_2p50_12_38 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 12)%Z -> (Z.abs b <= 2 ^ 38)%Z ->
    (Z.abs (a * b) <= 2 ^ 50)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 50)%Z with (2 ^ 12 * 2 ^ 38)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma arc_diff_bound_2p25 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 24)%Z -> (Z.abs b <= 2 ^ 24)%Z ->
    (Z.abs (a - b) <= 2 ^ 25)%Z.
Proof. intros. replace (2 ^ 25)%Z with (2 ^ 24 + 2 ^ 24)%Z by lia. lia. Qed.

Lemma arc_row3_diff_bound_2p38 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 37)%Z -> (Z.abs b <= 2 ^ 37)%Z ->
    (Z.abs (a - b) <= 2 ^ 38)%Z.
Proof. intros. replace (2 ^ 38)%Z with (2 ^ 37 + 2 ^ 37)%Z by lia. lia. Qed.

Lemma arc_row4_bound_2p50 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 25)%Z -> (Z.abs b <= 2 ^ 25)%Z ->
    (Z.abs (a * b) <= 2 ^ 50)%Z.
Proof.
  intros a b Ha Hb.
  rewrite Z.abs_mul.
  replace (2 ^ 50)%Z with (2 ^ 25 * 2 ^ 25)%Z by lia.
  apply Z.mul_le_mono_nonneg; try apply Z.abs_nonneg; assumption.
Qed.

Lemma arc_outer_diff_bound_2p51 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 50)%Z -> (Z.abs b <= 2 ^ 50)%Z ->
    (Z.abs (a - b) <= 2 ^ 51)%Z.
Proof. intros. replace (2 ^ 51)%Z with (2 ^ 50 + 2 ^ 50)%Z by lia. lia. Qed.

Lemma arc_final_sum_bound_2p52 :
  forall (a b : Z),
    (Z.abs a <= 2 ^ 51)%Z -> (Z.abs b <= 2 ^ 50)%Z ->
    (Z.abs (a + b) <= 2 ^ 52)%Z.
Proof.
  intros a b Ha Hb.
  apply (Z.le_trans _ (Z.abs a + Z.abs b)%Z); [apply Z.abs_triangle |].
  apply (Z.le_trans _ (2 ^ 51 + 2 ^ 50)%Z); [lia |].
  replace (2 ^ 51 + 2 ^ 50)%Z with (3 * 2 ^ 50)%Z by lia.
  replace (2 ^ 52)%Z with (4 * 2 ^ 50)%Z by lia.
  lia.
Qed.

Print Assumptions Zfold_min8_le1.
Print Assumptions Zfold_min8_le2.
Print Assumptions Zfold_min8_le3.
Print Assumptions Zfold_min8_le4.
Print Assumptions Zfold_min8_le5.
Print Assumptions Zfold_min8_le6.
Print Assumptions Zfold_min8_le7.
Print Assumptions Zfold_min8_le8.
Print Assumptions IZR_mul_diff.
Print Assumptions IZR_mul_sq.
Print Assumptions IZR_sq_sum.
Print Assumptions IZR_coord_sq_pair.
Print Assumptions inCircle_Zdet_distrib.
Print Assumptions inCircle_shift_quartic_IZR_pack.
Print Assumptions inCircle_shift_quartic_homog.
Print Assumptions IZR_na_cross_pack.
Print Assumptions inCircle_det_IZR_pack.
Print Assumptions arc_diff_bound_2p12.
Print Assumptions arc_sq_bound_2p24.
Print Assumptions arc_sum_sq_bound_2p25.
Print Assumptions arc_product_bound_2p24.
Print Assumptions arc_product_bound_2p37.
Print Assumptions arc_product_bound_2p50_12_38.
Print Assumptions arc_diff_bound_2p25.
Print Assumptions arc_row3_diff_bound_2p38.
Print Assumptions arc_row4_bound_2p50.
Print Assumptions arc_outer_diff_bound_2p51.
Print Assumptions arc_final_sum_bound_2p52.
