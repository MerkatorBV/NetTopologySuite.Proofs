(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_grid_separation
   ----------------------------------------------------------------------------
   SLICES 14-18: gap-beats-band and the unconditional headline.

   Slices 14-18: the bricks combine (determinant gap strictly exceeds the
   rounding band); the RELATIVE ulp bound removing the [-1,1] cap; the
   value-0 edge; the gridbound packaging algebra; and the discharge of
   clip_separated on the tight integer grid |n| <= 2^22, yielding the
   unconditional headline b64_passes_through_grid_exact (compute = spec
   on the tight grid, no named hypotheses).

   Split out of the former 1896-line PassesThrough_b64_grid_exact.v
   monolith (issue #66 C1; topic: binary64, claimId: 66-c1, witness:
   grid-unit); PassesThrough_b64_grid_exact.v remains as the Require
   Export umbrella, so reverse dependencies import unchanged.  Slice
   text, declarations, and Print Assumptions footers carried over
   verbatim.  No Admitted, no Axiom, no Parameter.
   ============================================================================ *)

From Stdlib Require Import Bool.
From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.
From NTS.Proofs.Flocq Require Import B64_lib.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import SnapRounding_b64.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.
From NTS.Proofs.Flocq Require Import Orient_b64_exact.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_grid_core.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_grid_bounds.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_grid_complete.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_grid_gap_kernel.

(* ----------------------------------------------------------------------------
   SLICE 14: the three bricks combine -- the determinant gap STRICTLY EXCEEDS
   the rounding band for two distinct bounded grid ratios.

   For u = na/da, v = nb/db two DISTINCT ratios that are (i) in [-1,1] and
   (ii) have denominators |da|,|db| <= 2^24 (the tight-regime t-bound shape:
   denominator 2(c1-c0) with |c1-c0| <= 2^24, i.e. |n| <= 2^23):

       1/2 ulp(round u) + 1/2 ulp(round v)  <  |u - v|.

   Proof = Slice 13 (ulp band <= 2^-52, since |u|,|v| <= 1) + Slice 12 (gap
   >= 1/(|da||db|) >= 2^-48) + 2^-52 < 2^-48.  This is EXACTLY the right disjunct
   of `clip_separated` for the binding (tmin_e, tmax_e) pair -- the quantitative
   heart of unconditional on-grid soundness in the tight regime.  What remains
   to assemble `clip_separated` itself is purely structural: exhibit tmin_e /
   tmax_e as such bounded ratios (the Rmax/Rmin selects one element each;
   grid_quotient_ratio gives the ratio form; the clip gives the [-1,1] bound in
   the binding case).
   ---------------------------------------------------------------------------- *)
Lemma grid_ratio_gap_exceeds_ulp_band :
  forall (u v : R) (na da nb db : Z),
    u = (IZR na / IZR da)%R -> v = (IZR nb / IZR db)%R ->
    (da <> 0)%Z -> (db <> 0)%Z ->
    (Z.abs da <= 2 ^ 24)%Z -> (Z.abs db <= 2 ^ 24)%Z ->
    (Rabs u <= 1)%R -> (Rabs v <= 1)%R ->
    u <> v ->
    (b64_ulp (b64_round u) / 2 + b64_ulp (b64_round v) / 2 < Rabs (u - v))%R.
Proof.
  intros u v na da nb db Hu Hv Hda Hdb HdaB HdbB Hu1 Hv1 Hne.
  (* (A) the rounding band is <= bpow (1 - prec) = 2^-52 *)
  pose proof (b64_ulp_round_le_unit u Hu1) as Hulpu.
  pose proof (b64_ulp_round_le_unit v Hv1) as Hulpv.
  assert (Hband : (b64_ulp (b64_round u) / 2 + b64_ulp (b64_round v) / 2
                    <= bpow radix2 (1 - prec))%R) by lra.
  (* (B) distinct ratios cross-multiply distinctly *)
  assert (Hcross : (na * db <> nb * da)%Z).
  { intro Hc. apply Hne. rewrite Hu, Hv.
    field_simplify_eq; [ | split; apply IZR_neq; assumption ].
    rewrite <- !mult_IZR. f_equal. lia. }
  pose proof (rational_gap na da nb db Hda Hdb Hcross) as Hgap.
  rewrite <- Hu, <- Hv in Hgap.
  (* (C) the gap is >= bpow (-48): denominators bounded by bpow 24 *)
  assert (HdaR : (Rabs (IZR da) <= bpow radix2 24)%R).
  { rewrite <- abs_IZR, <- (IZR_Zpower radix2 24) by lia. apply IZR_le. exact HdaB. }
  assert (HdbR : (Rabs (IZR db) <= bpow radix2 24)%R).
  { rewrite <- abs_IZR, <- (IZR_Zpower radix2 24) by lia. apply IZR_le. exact HdbB. }
  assert (Hdapos : (0 < Rabs (IZR da))%R) by (apply Rabs_pos_lt, IZR_neq; assumption).
  assert (Hdbpos : (0 < Rabs (IZR db))%R) by (apply Rabs_pos_lt, IZR_neq; assumption).
  assert (Hprodpos : (0 < Rabs (IZR da) * Rabs (IZR db))%R)
    by (apply Rmult_lt_0_compat; assumption).
  assert (Hprod : (Rabs (IZR da) * Rabs (IZR db) <= bpow radix2 48)%R).
  { replace (bpow radix2 48) with (bpow radix2 24 * bpow radix2 24)%R
      by (rewrite <- bpow_plus; reflexivity).
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (Hgap48 : (/ bpow radix2 48 <= Rabs (u - v))%R).
  { apply (Rle_trans _ (1 / (Rabs (IZR da) * Rabs (IZR db)))%R); [ | exact Hgap ].
    unfold Rdiv. rewrite Rmult_1_l.
    apply Rinv_le_contravar; [ exact Hprodpos | exact Hprod ]. }
  (* (D) chain: band <= 2^-52 < 2^-48 = / bpow 48 <= gap *)
  assert (Hlt : (bpow radix2 (1 - prec) < / bpow radix2 48)%R).
  { apply (Rmult_lt_reg_r (bpow radix2 48)); [ apply bpow_gt_0 | ].
    rewrite Rinv_l by (apply Rgt_not_eq, bpow_gt_0).
    rewrite <- bpow_plus.
    replace (1 - prec + 48)%Z with (-4)%Z by (unfold prec; lia).
    replace 1%R with (bpow radix2 0) by reflexivity.
    apply bpow_lt. lia. }
  lra.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 15: the RELATIVE ulp bound, and the general gap-beats-band.

   Slice 14's `[-1,1]` restriction is too tight for the binding t-bounds (which
   can be larger).  The fix is the relative bound `ulp(round x) <= |x| *
   2^(2-prec)` (Slice 13 at e = mag x, plus the mag sandwich
   `bpow(mag x - 1) <= |x| < bpow(mag x)`), valid for |x| >= 2^-24 (every nonzero
   grid t-bound, whose |value| = |num|/|den| >= 1/2^24).  With it, the band
   telescopes against the gap through the numerator/denominator bounds, with no
   value-range restriction: for nonzero grid ratios the gap always beats the
   band in the |n| <= 2^23 regime.
   ---------------------------------------------------------------------------- *)

(* Relative ulp bound: round-to-nearest's ulp is at most the value times one
   binade of relative precision (for x bounded away from the subnormals). *)
Lemma b64_ulp_round_le_rel :
  forall x : R,
    (bpow radix2 (-24) <= Rabs x)%R ->
    (b64_ulp (b64_round x) <= Rabs x * bpow radix2 (2 - prec))%R.
Proof.
  intros x Hx.
  assert (Hxne : x <> 0%R).
  { intro Hz. rewrite Hz, Rabs_R0 in Hx. pose proof (bpow_gt_0 radix2 (-24)). lra. }
  pose proof (mag_gt_bpow radix2 x (-24) Hx) as Hmag.   (* -24 < mag x *)
  assert (He1 : (3 - emax <= mag radix2 x + 1)%Z) by (unfold emax; lia).
  assert (Hxle : (Rabs x <= bpow radix2 (mag radix2 x))%R)
    by (apply Rlt_le, (bpow_mag_gt radix2 x)).
  pose proof (b64_ulp_round_le_bpow x (mag radix2 x) He1 Hxle) as Hub.
  apply (Rle_trans _ (bpow radix2 (mag radix2 x + 1 - prec))); [ exact Hub | ].
  replace (mag radix2 x + 1 - prec)%Z
    with ((mag radix2 x - 1) + (2 - prec))%Z by lia.
  rewrite bpow_plus.
  apply Rmult_le_compat_r; [ apply bpow_ge_0 | ].
  apply (bpow_mag_le radix2 x). exact Hxne.
Qed.

(* General gap-beats-band: NO value-range restriction.  For two distinct nonzero
   grid ratios (numerator <= 2^25, denominator <= 2^24, |value| >= 2^-24), the
   determinant gap strictly exceeds the rounding band.  Covers every nonzero
   binding bound, including the constant 1 = 1/1. *)
Lemma grid_ratio_gap_exceeds_ulp_band_rel :
  forall (u v : R) (na da nb db : Z),
    u = (IZR na / IZR da)%R -> v = (IZR nb / IZR db)%R ->
    (da <> 0)%Z -> (db <> 0)%Z ->
    (Z.abs na <= 2 ^ 25)%Z -> (Z.abs nb <= 2 ^ 25)%Z ->
    (Z.abs da <= 2 ^ 24)%Z -> (Z.abs db <= 2 ^ 24)%Z ->
    (bpow radix2 (-24) <= Rabs u)%R -> (bpow radix2 (-24) <= Rabs v)%R ->
    u <> v ->
    (b64_ulp (b64_round u) / 2 + b64_ulp (b64_round v) / 2 < Rabs (u - v))%R.
Proof.
  intros u v na da nb db Hu Hv Hda Hdb HnaB HnbB HdaB HdbB Hu24 Hv24 Hne.
  set (P := (Rabs (IZR da) * Rabs (IZR db))%R).
  assert (Hdane : IZR da <> 0%R) by (apply IZR_neq; exact Hda).
  assert (Hdbne : IZR db <> 0%R) by (apply IZR_neq; exact Hdb).
  assert (HPpos : (0 < P)%R)
    by (unfold P; apply Rmult_lt_0_compat; apply Rabs_pos_lt; assumption).
  (* relative ulp bounds *)
  pose proof (b64_ulp_round_le_rel u Hu24) as Hru.
  pose proof (b64_ulp_round_le_rel v Hv24) as Hrv.
  (* |u| * P = |IZR na| * |IZR db| <= 2^25 * 2^24 = 2^49 *)
  assert (HnaR : (Rabs (IZR na) <= bpow radix2 25)%R).
  { rewrite <- abs_IZR, <- (IZR_Zpower radix2 25) by lia. apply IZR_le. exact HnaB. }
  assert (HnbR : (Rabs (IZR nb) <= bpow radix2 25)%R).
  { rewrite <- abs_IZR, <- (IZR_Zpower radix2 25) by lia. apply IZR_le. exact HnbB. }
  assert (HdaR : (Rabs (IZR da) <= bpow radix2 24)%R).
  { rewrite <- abs_IZR, <- (IZR_Zpower radix2 24) by lia. apply IZR_le. exact HdaB. }
  assert (HdbR : (Rabs (IZR db) <= bpow radix2 24)%R).
  { rewrite <- abs_IZR, <- (IZR_Zpower radix2 24) by lia. apply IZR_le. exact HdbB. }
  assert (HuP : (Rabs u * P = Rabs (IZR na) * Rabs (IZR db))%R).
  { unfold P. rewrite Hu. unfold Rdiv. rewrite Rabs_mult, Rabs_inv. field.
    apply Rabs_no_R0. exact Hdane. }
  assert (HvP : (Rabs v * P = Rabs (IZR nb) * Rabs (IZR da))%R).
  { unfold P. rewrite Hv. unfold Rdiv. rewrite Rabs_mult, Rabs_inv. field.
    apply Rabs_no_R0. exact Hdbne. }
  (* band * P <= 2^49 * 2^(2-prec) = bpow(-2) = 1/4 *)
  assert (Hb49 : (bpow radix2 25 * bpow radix2 24 = bpow radix2 49)%R)
    by (rewrite <- bpow_plus; reflexivity).
  assert (HuP49 : (Rabs u * P <= bpow radix2 49)%R).
  { rewrite HuP. rewrite <- Hb49. apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (HvP49 : (Rabs v * P <= bpow radix2 49)%R).
  { rewrite HvP. rewrite <- Hb49.
    apply Rmult_le_compat; try apply Rabs_pos; assumption. }
  assert (Hpos2 : (0 < bpow radix2 (2 - prec))%R) by apply bpow_gt_0.
  assert (HbandP : ((b64_ulp (b64_round u) / 2 + b64_ulp (b64_round v) / 2) * P
                     <= bpow radix2 (-2))%R).
  { (* ulp(round u) <= |u| bpow(2-prec) etc; multiply through by P >= 0 *)
    apply (Rle_trans _ ((Rabs u * bpow radix2 (2 - prec) / 2
                          + Rabs v * bpow radix2 (2 - prec) / 2) * P)).
    { apply Rmult_le_compat_r; [ lra | lra ]. }
    (* = (|u|P + |v|P) * bpow(2-prec)/2 <= (2^49+2^49)*bpow(2-prec)/2 = bpow(-2) *)
    replace ((Rabs u * bpow radix2 (2 - prec) / 2
               + Rabs v * bpow radix2 (2 - prec) / 2) * P)%R
      with ((Rabs u * P + Rabs v * P) * bpow radix2 (2 - prec) / 2)%R by (unfold P; field).
    apply (Rle_trans _ ((bpow radix2 49 + bpow radix2 49) * bpow radix2 (2 - prec) / 2)).
    { apply Rmult_le_compat_r; [ lra | ]. apply Rmult_le_compat_r; [ lra | ]. lra. }
    replace ((bpow radix2 49 + bpow radix2 49) * bpow radix2 (2 - prec) / 2)%R
      with (bpow radix2 49 * bpow radix2 (2 - prec))%R by field.
    rewrite <- bpow_plus.
    replace (49 + (2 - prec))%Z with (-2)%Z by (unfold prec; lia).
    apply Rle_refl. }
  (* gap: 1/P <= |u - v|, so 1 <= |u-v| * P *)
  assert (Hcross : (na * db <> nb * da)%Z).
  { intro Hc. apply Hne. rewrite Hu, Hv.
    field_simplify_eq; [ | split; assumption ].
    rewrite <- !mult_IZR. f_equal. lia. }
  pose proof (rational_gap na da nb db Hda Hdb Hcross) as Hgap.
  rewrite <- Hu, <- Hv in Hgap. fold P in Hgap.
  assert (HgapP : (1 <= Rabs (u - v) * P)%R).
  { apply (Rle_trans _ ((1 / P) * P)).
    - replace ((1 / P) * P)%R with 1%R by (field; apply Rgt_not_eq; exact HPpos).
      apply Rle_refl.
    - apply Rmult_le_compat_r; [ lra | exact Hgap ]. }
  (* finish: band*P <= 1/4 < 1 <= gap*P, and P > 0 *)
  assert (Hquarter : (bpow radix2 (-2) = / 4)%R) by (simpl; lra).
  apply (Rmult_lt_reg_r P); [ exact HPpos | ]. lra.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 16: the value-0 edge case of gap-beats-band.

   Slice 15 handles two NONZERO grid ratios.  The one remaining binding shape is
   when one clip bound is exactly 0 (e.g. tmin_e = Rmax 0 (...) = 0 with the
   other bound strictly on the far side).  Then the gap is just |v| and the band
   is `1/2 ulp(round 0) + 1/2 ulp(round v)`; with `ulp(round 0) = ulp(0) =
   bpow emin` (a subnormal floor, ~2^-1074) and the relative bound on the nonzero
   side, the band is far below |v| for any |v| >= 2^-24.  No ratio structure is
   needed -- only `|v| >= 2^-24`.  Together with Slice 15 this makes the
   gap-beats-band family TOTAL over the binding pairs.
   ---------------------------------------------------------------------------- *)
Lemma zero_vs_ratio_gap_exceeds_ulp_band :
  forall v : R,
    (bpow radix2 (-24) <= Rabs v)%R ->
    (b64_ulp (b64_round 0) / 2 + b64_ulp (b64_round v) / 2 < Rabs (0 - v))%R.
Proof.
  intros v Hv.
  assert (Hr0 : b64_round 0 = 0%R) by (apply (round_0 radix2 b64_fexp (round_mode mode_b64))).
  rewrite Hr0, b64_ulp_FLT_0.
  pose proof (b64_ulp_round_le_rel v Hv) as Hrv.
  assert (Hb2 : (bpow radix2 (2 - prec) < 1)%R).
  { replace 1%R with (bpow radix2 0) by reflexivity. apply bpow_lt. unfold prec; lia. }
  assert (Hemin : (bpow radix2 b64_emin <= Rabs v)%R).
  { apply (Rle_trans _ (bpow radix2 (-24))); [ apply bpow_le; unfold emax, prec; lia | exact Hv ]. }
  assert (Hv0 : (0 < Rabs v)%R).
  { apply (Rlt_le_trans _ (bpow radix2 (-24))); [ apply bpow_gt_0 | exact Hv ]. }
  rewrite Rabs_minus_sym, Rminus_0_r.
  nra.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 17: the `gridbound` abstraction -- the structural glue.

   A real is `gridbound` iff it is 0 or a bounded nonzero grid ratio
   (numerator <= 2^25, denominator <= 2^24, magnitude >= 2^-24).  This is closed
   under Rmax / Rmin (each selects one argument), so every exact clip bound
   tmin_e = Rmax 0 (Rmax tlo_x tlo_y) and tmax_e = Rmin 1 (Rmin thi_x thi_y) is
   gridbound once the per-axis t-bounds are.  And on gridbound inputs the
   gap-beats-band family is TOTAL (Slices 15 + 16) -- `gap_beats_band_of_gridbound`
   is exactly `clip_separated`'s right disjunct for any binding pair.
   ---------------------------------------------------------------------------- *)
Definition gridbound (x : R) : Prop :=
  x = 0%R \/
  (exists na da : Z,
     x = (IZR na / IZR da)%R /\ (da <> 0)%Z /\
     (Z.abs na <= 2 ^ 25)%Z /\ (Z.abs da <= 2 ^ 24)%Z /\
     (bpow radix2 (-24) <= Rabs x)%R).

Lemma gridbound_0 : gridbound 0.
Proof. left. reflexivity. Qed.

Lemma gridbound_1 : gridbound 1.
Proof.
  right. exists 1%Z, 1%Z.
  repeat split; try (simpl; lra); try lia.
  rewrite Rabs_R1. apply Rlt_le. replace 1%R with (bpow radix2 0) by reflexivity.
  apply bpow_lt. lia.
Qed.

Lemma gridbound_Rmax : forall a b, gridbound a -> gridbound b -> gridbound (Rmax a b).
Proof.
  intros a b Ha Hb. destruct (Rle_dec a b) as [H | H].
  - rewrite (Rmax_right a b H). exact Hb.
  - rewrite (Rmax_left a b ltac:(lra)). exact Ha.
Qed.

Lemma gridbound_Rmin : forall a b, gridbound a -> gridbound b -> gridbound (Rmin a b).
Proof.
  intros a b Ha Hb. destruct (Rle_dec a b) as [H | H].
  - rewrite (Rmin_left a b H). exact Ha.
  - rewrite (Rmin_right a b ltac:(lra)). exact Hb.
Qed.

(* gap beats band for any two distinct gridbound values -- the right disjunct of
   `clip_separated`.  Composes Slice 16 (one value 0) and Slice 15 (both nonzero). *)
Lemma gap_beats_band_of_gridbound :
  forall u v : R,
    gridbound u -> gridbound v -> u <> v ->
    (b64_ulp (b64_round u) / 2 + b64_ulp (b64_round v) / 2 < Rabs (u - v))%R.
Proof.
  intros u v Hu Hv Hne.
  destruct Hu as [Hu0 | (na & da & Hu & Hda & HnaB & HdaB & Hu24)];
  destruct Hv as [Hv0 | (nb & db & Hv & Hdb & HnbB & HdbB & Hv24)].
  - exfalso. apply Hne. rewrite Hu0, Hv0. reflexivity.
  - rewrite Hu0. apply zero_vs_ratio_gap_exceeds_ulp_band. exact Hv24.
  - rewrite Hv0.
    pose proof (zero_vs_ratio_gap_exceeds_ulp_band u Hu24) as H.
    rewrite (Rabs_minus_sym u 0). lra.
  - apply (grid_ratio_gap_exceeds_ulp_band_rel u v na da nb db);
      assumption.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 18: the t-bounds are `gridbound` -- the last structural fact, and the
   unconditional on-grid soundness close (tight regime |n| <= 2^22).
   ---------------------------------------------------------------------------- *)

(* bpow(-24) = / bpow 24 (the `-24` numeral does not match `bpow_opp`'s `Z.opp`). *)
Lemma bpow_neg24_eq : bpow radix2 (-24) = (/ bpow radix2 24)%R.
Proof.
  apply (Rmult_eq_reg_r (bpow radix2 24)); [ | apply Rgt_not_eq, bpow_gt_0 ].
  rewrite <- bpow_plus. rewrite Rinv_l by (apply Rgt_not_eq, bpow_gt_0).
  replace (-24 + 24)%Z with 0%Z by lia. reflexivity.
Qed.

(* A nonzero ratio with denominator bounded by 2^24 has magnitude >= 2^-24. *)
Lemma ratio_abs_ge_bpow_neg24 :
  forall (na da : Z), (na <> 0)%Z -> (da <> 0)%Z -> (Z.abs da <= 2 ^ 24)%Z ->
    (bpow radix2 (-24) <= Rabs (IZR na / IZR da))%R.
Proof.
  intros na da Hna Hda HdaB.
  assert (Hdane : IZR da <> 0%R) by (apply IZR_neq; exact Hda).
  rewrite bpow_neg24_eq. unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
  assert (Hna1 : (1 <= Rabs (IZR na))%R).
  { rewrite <- abs_IZR. replace 1%R with (IZR 1) by reflexivity. apply IZR_le. lia. }
  assert (HdaR : (Rabs (IZR da) <= bpow radix2 24)%R).
  { rewrite <- abs_IZR, <- (IZR_Zpower radix2 24) by lia. apply IZR_le. exact HdaB. }
  assert (Hdapos : (0 < Rabs (IZR da))%R) by (apply Rabs_pos_lt; exact Hdane).
  apply (Rle_trans _ (1 * / Rabs (IZR da))%R).
  - rewrite Rmult_1_l. apply Rinv_le_contravar; [ exact Hdapos | exact HdaR ].
  - apply Rmult_le_compat_r; [ apply Rlt_le, Rinv_0_lt_compat; exact Hdapos | exact Hna1 ].
Qed.

(* A grid Liang-Barsky quotient with a half-integer numerator IZR m / 2 (the
   pixel half-edge cc +/- 1/2 minus an integer endpoint) over an integer run is
   `gridbound`, in the tight regime. *)
Lemma gridbound_half_quotient :
  forall (m n0 n1 : Z),
    (n1 <> n0)%Z ->
    (Z.abs m <= 2 ^ 24)%Z -> (Z.abs n0 <= 2 ^ 22)%Z -> (Z.abs n1 <= 2 ^ 22)%Z ->
    gridbound ((IZR m / 2 - IZR n0) / (IZR n1 - IZR n0)).
Proof.
  intros m n0 n1 Hne Hm Hn0 Hn1.
  assert (Hd : (IZR n1 - IZR n0)%R <> 0%R).
  { intro H. apply Hne. apply eq_IZR. lra. }
  assert (Hq : ((IZR m / 2 - IZR n0) / (IZR n1 - IZR n0))%R
                = (IZR (m - 2 * n0)%Z / IZR (2 * (n1 - n0))%Z)%R).
  { rewrite minus_IZR, !mult_IZR, minus_IZR. field. exact Hd. }
  rewrite Hq.
  destruct (Z.eq_dec (m - 2 * n0) 0) as [Hna0 | Hna0].
  - left. rewrite Hna0. change (IZR 0) with 0%R. unfold Rdiv. apply Rmult_0_l.
  - right. exists (m - 2 * n0)%Z, (2 * (n1 - n0))%Z.
    split; [ reflexivity | ].
    split; [ lia | ].
    split; [ lia | ].
    split; [ lia | ].
    apply ratio_abs_ge_bpow_neg24; [ exact Hna0 | lia | lia ].
Qed.

(* The tight integer-grid regime |n| <= 2^22 -- where the t-bound numerators
   (<= 2^24) and runs (denominator <= 2^24) fit the gridbound bounds.  It
   implies the |n| <= 2^25 `coord_int_safe` regime the rest of C1 runs in. *)
Definition coord_int_tight (x : binary64) : Prop :=
  Binary.is_finite prec emax x = true /\
  exists n : Z, Binary.B2R prec emax x = IZR n /\ (Z.abs n <= 2 ^ 22)%Z.

Lemma coord_int_tight_safe : forall x, coord_int_tight x -> coord_int_safe x.
Proof. intros x (F & n & HR & Hb). split; [ exact F | exists n; split; [ exact HR | lia ] ]. Qed.

Definition bpoint_int_tight (P : BPoint) : Prop :=
  coord_int_tight (bx P) /\ coord_int_tight (by_ P).

Lemma bpoint_int_tight_safe : forall P, bpoint_int_tight P -> bpoint_int_safe P.
Proof. intros P (Hx & Hy). split; apply coord_int_tight_safe; assumption. Qed.

(* Each exact per-axis t-bound is gridbound on the tight grid.  Degenerate axis:
   lb_tlo = 0 (gridbound_0).  Non-degenerate: Rmin of the two half-edge
   quotients, each gridbound (gridbound_half_quotient). *)
Lemma gridbound_tlo :
  forall c0 c1 cc : binary64,
    coord_int_tight c0 -> coord_int_tight c1 -> coord_int_tight cc ->
    gridbound (lb_tlo (Binary.B2R prec emax c0) (Binary.B2R prec emax c1)
                      (Binary.B2R prec emax cc - / 2) (Binary.B2R prec emax cc + / 2)).
Proof.
  intros c0 c1 cc (Fc0 & n0 & H0R & H0b) (Fc1 & n1 & H1R & H1b) (Fcc & ncc & HccR & Hccb).
  unfold lb_tlo.
  destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0)) as [Heq | Hne].
  - apply gridbound_0.
  - assert (Hn : (n1 <> n0)%Z) by (intro Hz; apply Hne; rewrite H1R, H0R, Hz; reflexivity).
    rewrite H0R, H1R, HccR.
    apply gridbound_Rmin.
    + replace (IZR ncc - / 2 - IZR n0)%R with (IZR (2 * ncc - 1)%Z / 2 - IZR n0)%R
        by (rewrite minus_IZR, mult_IZR; lra).
      apply gridbound_half_quotient; [ exact Hn | lia | lia | lia ].
    + replace (IZR ncc + / 2 - IZR n0)%R with (IZR (2 * ncc + 1)%Z / 2 - IZR n0)%R
        by (rewrite plus_IZR, mult_IZR; lra).
      apply gridbound_half_quotient; [ exact Hn | lia | lia | lia ].
Qed.

Lemma gridbound_thi :
  forall c0 c1 cc : binary64,
    coord_int_tight c0 -> coord_int_tight c1 -> coord_int_tight cc ->
    gridbound (lb_thi (Binary.B2R prec emax c0) (Binary.B2R prec emax c1)
                      (Binary.B2R prec emax cc - / 2) (Binary.B2R prec emax cc + / 2)).
Proof.
  intros c0 c1 cc (Fc0 & n0 & H0R & H0b) (Fc1 & n1 & H1R & H1b) (Fcc & ncc & HccR & Hccb).
  unfold lb_thi.
  destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0)) as [Heq | Hne].
  - apply gridbound_1.
  - assert (Hn : (n1 <> n0)%Z) by (intro Hz; apply Hne; rewrite H1R, H0R, Hz; reflexivity).
    rewrite H0R, H1R, HccR.
    apply gridbound_Rmax.
    + replace (IZR ncc - / 2 - IZR n0)%R with (IZR (2 * ncc - 1)%Z / 2 - IZR n0)%R
        by (rewrite minus_IZR, mult_IZR; lra).
      apply gridbound_half_quotient; [ exact Hn | lia | lia | lia ].
    + replace (IZR ncc + / 2 - IZR n0)%R with (IZR (2 * ncc + 1)%Z / 2 - IZR n0)%R
        by (rewrite plus_IZR, mult_IZR; lra).
      apply gridbound_half_quotient; [ exact Hn | lia | lia | lia ].
Qed.

(* The exact clip bounds are gridbound (gridbound closed under Rmax/Rmin, with
   the constants 0/1 and the per-axis t-bounds gridbound). *)
Lemma gridbound_tmin_exact :
  forall P0 P1 C : BPoint,
    bpoint_int_tight P0 -> bpoint_int_tight P1 -> bpoint_int_tight C ->
    gridbound (tmin_exact P0 P1 C).
Proof.
  intros P0 P1 C (Hx0 & Hy0) (Hx1 & Hy1) (Hcx & Hcy).
  unfold tmin_exact.
  apply gridbound_Rmax; [ apply gridbound_0 | ].
  apply gridbound_Rmax; apply gridbound_tlo; assumption.
Qed.

Lemma gridbound_tmax_exact :
  forall P0 P1 C : BPoint,
    bpoint_int_tight P0 -> bpoint_int_tight P1 -> bpoint_int_tight C ->
    gridbound (tmax_exact P0 P1 C).
Proof.
  intros P0 P1 C (Hx0 & Hy0) (Hx1 & Hy1) (Hcx & Hcy).
  unfold tmax_exact.
  apply gridbound_Rmin; [ apply gridbound_1 | ].
  apply gridbound_Rmin; apply gridbound_thi; assumption.
Qed.

(* `clip_separated` holds UNCONDITIONALLY on the tight grid: either the exact
   clip interval is nonempty, or (both bounds gridbound) the gap beats the band
   by Slice 17. *)
Lemma clip_separated_tight :
  forall P0 P1 C : BPoint,
    bpoint_int_tight P0 -> bpoint_int_tight P1 -> bpoint_int_tight C ->
    clip_separated P0 P1 C.
Proof.
  intros P0 P1 C HP0 HP1 HC. unfold clip_separated.
  destruct (Rle_dec (tmin_exact P0 P1 C) (tmax_exact P0 P1 C)) as [Hle | Hgt].
  - left. exact Hle.
  - right.
    pose proof (gap_beats_band_of_gridbound (tmin_exact P0 P1 C) (tmax_exact P0 P1 C)
                  (gridbound_tmin_exact P0 P1 C HP0 HP1 HC)
                  (gridbound_tmax_exact P0 P1 C HP0 HP1 HC) ltac:(lra)) as H.
    rewrite Rabs_right in H by lra. exact H.
Qed.

(* ============================================================================
   C1 ON-GRID SOUNDNESS, UNCONDITIONAL on the tight integer grid (|n| <= 2^22).
   The compute filter only ever OVER-accepts off the grid (the machine-checked
   RED, PassesThrough_b64_compute_unsound.v); here, in the regime a snap-rounding
   noder actually runs (integer/grid-aligned coordinates), it is SOUND -- and,
   with Slice 9's completeness, the rounded compute filter EQUALS the exact
   R-spec.  No hypotheses beyond the tight integer grid; no Admitted.
   ============================================================================ *)
Theorem b64_passes_through_sound_on_grid :
  forall P0 P1 C : BPoint,
    bpoint_int_tight P0 -> bpoint_int_tight P1 -> bpoint_int_tight C ->
    b64_passes_through_hot_pixel_compute P0 P1 C = true ->
    b64_passes_through_hot_pixel P0 P1 C = true.
Proof.
  intros P0 P1 C HP0 HP1 HC.
  apply (b64_passes_through_sound_on_grid_sep P0 P1 C
           (bpoint_int_tight_safe P0 HP0) (bpoint_int_tight_safe P1 HP1)
           (bpoint_int_tight_safe C HC) (clip_separated_tight P0 P1 C HP0 HP1 HC)).
Qed.

(* Full C1 grid-exactness, UNCONDITIONAL on the tight grid: the rounded compute
   filter EQUALS the exact R-spec (soundness here + Slice 9 completeness). *)
Theorem b64_passes_through_grid_exact :
  forall P0 P1 C : BPoint,
    bpoint_int_tight P0 -> bpoint_int_tight P1 -> bpoint_int_tight C ->
    b64_passes_through_hot_pixel_compute P0 P1 C = b64_passes_through_hot_pixel P0 P1 C.
Proof.
  intros P0 P1 C HP0 HP1 HC.
  apply (b64_passes_through_grid_exact_sep P0 P1 C
           (bpoint_int_tight_safe P0 HP0) (bpoint_int_tight_safe P1 HP1)
           (bpoint_int_tight_safe C HC) (clip_separated_tight P0 P1 C HP0 HP1 HC)).
Qed.

(* ----------------------------------------------------------------------------
   CLOSED.  C1 (on-grid grid-exactness) is now UNCONDITIONAL on |n| <= 2^22:
   completeness (Slice 9) + soundness (Slices 10-18) = `compute = spec` on the
   grid, Qed, no named hypotheses.  The remaining open items are the WIDTH
   extension to the full coord_int_safe regime |n| <= 2^25 (needs the exact
   integer-determinant comparison, not a forward-error bound -- see
   docs/audit-rgr-comparison.md) and the general-binary64 C2.
   ---------------------------------------------------------------------------- *)

(* ----------------------------------------------------------------------------
   REMAINING OBLIGATIONS (after C1's unconditional close on |n| <= 2^22).

   C1 -- on-grid `compute = spec` -- is now CLOSED on the tight integer grid
   (`b64_passes_through_grid_exact`, Qed, no named hypotheses).  Two items
   remain, both honestly out of scope of this file:

   1. WIDTH EXTENSION to the full coord_int_safe regime |n| <= 2^25.
      The binding gap is >= 1/(4|d_a d_b|) and the rounding band is <= 2^-52 at
      the clip boundary (Slices 12-17).  Gap > band iff |d_a d_b| < 2^50:
        - at |n| <= 2^22 (used here; |d_a d_b| <= 2^48) the gap wins -- CLOSED;
        - at the full width |n| <= 2^25 it is *borderline* (|d_a d_b| can reach
          ~2^52, gap ~2^-54 < ulp), so a full-width close is NOT a pure
          forward-error argument -- it needs the EXACT integer-determinant
          comparison (no rounding in the decision), not a tightened band.
      See docs/audit-rgr-comparison.md "Execution" notes for the analysis.

   2. The general-binary64 completeness C2 (`spec => compute` off the grid),
      strongly evidenced but blocked -- see docs/oracle-soundness-finding.md.

   No `Admitted` / `Axiom` / `Parameter` anywhere in this file.
   ---------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)
Print Assumptions b64_snap_on_grid.
Print Assumptions b64_passes_through_collapses_on_grid.
Print Assumptions b64_passes_through_compute_collapses_on_grid.
Print Assumptions b64_passes_through_grid_exact_iff_touch.
Print Assumptions coord_int_safe_snap_id.
Print Assumptions bpoint_int_safe_on_grid.
Print Assumptions b64_passes_through_grid_exact_iff_touch_int.
Print Assumptions b64_eqb_true_iff_B2R.
Print Assumptions b64_le_eq_Rle_bool.
Print Assumptions slab_guard_bridge.
Print Assumptions generic_format_half_prec.
Print Assumptions b64_minus_half_exact.
Print Assumptions is_finite_b64_max.
Print Assumptions is_finite_b64_min.
Print Assumptions b64_max_B2R.
Print Assumptions b64_min_B2R.
Print Assumptions b64_div_round_half_over_int.
Print Assumptions grid_numerator_facts.
Print Assumptions b64_lb_tlo_eq_rounded_quotients_grid.
Print Assumptions b64_lb_thi_eq_rounded_quotients_grid.
Print Assumptions B2R_b64_zero.
Print Assumptions is_finite_b64_zero.
Print Assumptions b64_round_1.
Print Assumptions round_Rmin.
Print Assumptions round_Rmax.
Print Assumptions round_clip_max0.
Print Assumptions round_clip_min1.
Print Assumptions b64_div_edge_grid_finite.
Print Assumptions b64_lb_tlo_finite_grid.
Print Assumptions b64_lb_thi_finite_grid.
Print Assumptions b64_lb_tlo_eq_round_exact_grid.
Print Assumptions b64_lb_thi_eq_round_exact_grid.
Print Assumptions b64_tmin_eq_round_exact_grid.
Print Assumptions b64_tmax_eq_round_exact_grid.
Print Assumptions slab_closed_grid_eq.
Print Assumptions b64_liang_barsky_touches_complete_on_grid.
Print Assumptions b64_passes_through_complete_on_grid.
Print Assumptions b64_liang_barsky_grid_exact_cond.
Print Assumptions b64_passes_through_grid_exact_cond.
Print Assumptions b64_passes_through_sound_on_grid_cond.
Print Assumptions round_diff_le_of_round_le.
Print Assumptions round_reflects_le_of_sep.
Print Assumptions clip_separated_reflects.
Print Assumptions b64_passes_through_grid_exact_sep.
Print Assumptions b64_passes_through_sound_on_grid_sep.
Print Assumptions IZR_abs_ge_1.
Print Assumptions rational_gap.
Print Assumptions grid_quotient_ratio.
Print Assumptions b64_ulp_round_le_bpow.
Print Assumptions b64_ulp_round_le_unit.
Print Assumptions grid_ratio_gap_exceeds_ulp_band.
Print Assumptions b64_ulp_round_le_rel.
Print Assumptions grid_ratio_gap_exceeds_ulp_band_rel.
Print Assumptions zero_vs_ratio_gap_exceeds_ulp_band.
Print Assumptions gridbound_0.
Print Assumptions gridbound_1.
Print Assumptions gridbound_Rmax.
Print Assumptions gridbound_Rmin.
Print Assumptions gap_beats_band_of_gridbound.
Print Assumptions bpow_neg24_eq.
Print Assumptions ratio_abs_ge_bpow_neg24.
Print Assumptions gridbound_half_quotient.
Print Assumptions coord_int_tight_safe.
Print Assumptions bpoint_int_tight_safe.
Print Assumptions gridbound_tlo.
Print Assumptions gridbound_thi.
Print Assumptions gridbound_tmin_exact.
Print Assumptions gridbound_tmax_exact.
Print Assumptions clip_separated_tight.
Print Assumptions b64_passes_through_sound_on_grid.
Print Assumptions b64_passes_through_grid_exact.
