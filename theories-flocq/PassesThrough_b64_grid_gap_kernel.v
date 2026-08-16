(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_grid_gap_kernel
   ----------------------------------------------------------------------------
   SLICES 12-13: the gap kernel (meso-audit B4 extraction).

   Slices 12-13, extracted per meso-audit B4 (user-directed 2026-08-15 --
   the explicit BDFL ack the docs/category-c-policy.md SS10 pause asks
   for): the rational-gap kernel (two distinct integer ratios differ by at
   least 1/(|da||db|); each grid Liang-Barsky t-bound is exactly such a
   ratio) and the ulp UPPER bound (|x| <= 2^e => ulp(round x) <=
   2^(e+1-prec), unit instance 2^-52).

   CORRECTION (2026-08-16 categorisation pass): B4's "3-axiom [exact]
   throughout, off audit-exceptions.txt" claim was WRONG for slice 13.
   The ulp lemmas' statements mention `b64_round` (= Generic_fmt.round at
   the binary64 format), whose closure carries `Classical_Prop.classic`
   -- Category C1, type-level, per docs/category-c-policy.md SS3.  Only
   the slice-12 rational-gap lemmas (IZR_abs_ge_1, rational_gap,
   grid_quotient_ratio) are classic-free (machine-verified 2-axiom).
   The miss happened because this module had no Print Assumptions footer
   of its own; the audit footprint below closes that hole, and the file
   is back on docs/audit-exceptions.txt until a per-theorem registry
   (policy Option 2) lets the clean half stand alone.

   Split out of the former 1896-line PassesThrough_b64_grid_exact.v
   monolith (issue #66 C1; topic: binary64, claimId: 66-c1, witness:
   grid-unit); PassesThrough_b64_grid_exact.v remains as the Require
   Export umbrella, so reverse dependencies import unchanged.  Slice
   text, declarations, and Print Assumptions footers carried over
   verbatim.  No Admitted, no Axiom, no Parameter.
   ============================================================================ *)

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

(* ----------------------------------------------------------------------------
   SLICE 12: the rational-gap kernel -- the integer-determinant half of
   `clip_separated`.

   Two DISTINCT rationals with integer numerator/denominator differ by at least
   1 / (|d_a| |d_b|): their difference is `(na db - nb da) / (da db)`, an integer
   over `da db`, and a nonzero integer has absolute value >= 1.  On the grid
   every Liang-Barsky t-bound is exactly such a ratio (numerator a doubled
   half-integer, denominator 2 (c1 - c0)), so this is the lower bound on the
   `tmin_e - tmax_e` gap that the `clip_separated` discharge needs -- the
   "when the determinant is nonzero it is >= 1" fact, made precise and
   reusable.  Pairing it with a ulp UPPER bound (the other half) closes
   `clip_separated` in the bounded coordinate regime (see the OBLIGATION note).
   No grid hypotheses here: it is pure integer/rational arithmetic.
   ---------------------------------------------------------------------------- *)

(* A nonzero integer has |.| >= 1, as a real. *)
Lemma IZR_abs_ge_1 :
  forall n : Z, (n <> 0)%Z -> (1 <= Rabs (IZR n))%R.
Proof.
  intros n Hn. rewrite <- abs_IZR.
  replace 1%R with (IZR 1) by reflexivity.
  apply IZR_le. lia.
Qed.

Lemma rational_gap :
  forall (na da nb db : Z),
    (da <> 0)%Z -> (db <> 0)%Z ->
    (na * db <> nb * da)%Z ->
    (1 / (Rabs (IZR da) * Rabs (IZR db))
       <= Rabs (IZR na / IZR da - IZR nb / IZR db))%R.
Proof.
  intros na da nb db Hda Hdb Hne.
  assert (Hda_r : IZR da <> 0%R) by (apply IZR_neq; exact Hda).
  assert (Hdb_r : IZR db <> 0%R) by (apply IZR_neq; exact Hdb).
  assert (Hden_pos : (0 < Rabs (IZR da) * Rabs (IZR db))%R)
    by (apply Rmult_lt_0_compat; apply Rabs_pos_lt; assumption).
  (* combine into a single fraction over (da*db) *)
  assert (Heq : (IZR na / IZR da - IZR nb / IZR db)%R
                = (IZR (na * db - nb * da) / (IZR da * IZR db))%R)
    by (rewrite minus_IZR, !mult_IZR; field; split; assumption).
  rewrite Heq. unfold Rdiv.
  rewrite Rabs_mult, Rabs_inv, Rabs_mult.
  (* both sides are (_) * / (|da|*|db|); compare numerators 1 <= |num| *)
  apply Rmult_le_compat_r.
  - apply Rlt_le, Rinv_0_lt_compat. exact Hden_pos.
  - apply IZR_abs_ge_1. lia.
Qed.

(* A single grid Liang-Barsky quotient `(edge - c0)/(c1 - c0)`, with edge a
   half-integer `IZR m / 2` and c0, c1 integers, IS the integer ratio
   `IZR (m - 2 n0) / IZR (2 (n1 - n0))`.  This is the shape `rational_gap`
   consumes: two such quotients (the binding pair behind `tmin_e > tmax_e`)
   differ by at least `1 / (|2(x1-x0)| * |2(y1-y0)|)` when distinct. *)
Lemma grid_quotient_ratio :
  forall (c0 c1 e : binary64) (m n0 n1 : Z),
    Binary.B2R prec emax e = (IZR m / 2)%R ->
    Binary.B2R prec emax c0 = IZR n0 ->
    Binary.B2R prec emax c1 = IZR n1 ->
    (n1 <> n0)%Z ->
    ((Binary.B2R prec emax e - Binary.B2R prec emax c0)
       / (Binary.B2R prec emax c1 - Binary.B2R prec emax c0))%R
      = (IZR (m - 2 * n0) / IZR (2 * (n1 - n0)))%R.
Proof.
  intros c0 c1 e m n0 n1 HeR H0R H1R Hne.
  rewrite HeR, H0R, H1R.
  rewrite minus_IZR, !mult_IZR, minus_IZR.
  assert (Hd : (IZR n1 - IZR n0)%R <> 0%R).
  { apply Rminus_eq_contra. intro He. apply Hne. apply eq_IZR. exact He. }
  field. exact Hd.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 13: the ulp UPPER bound -- the other half of `clip_separated`.

   `round x` never exceeds the binade of x, so its ulp is bounded by the binade:
   `|x| <= 2^e  =>  ulp(round x) <= 2^(e+1-prec)`.  Pairing this with Slice 12's
   gap lower bound gives `clip_separated` in the bounded coordinate regime: at
   the tight boundary the clip forces both bounds into [0,1] (ulp <= 2^-52),
   while the determinant keeps the gap >= 2^-(2K+2); for |n| <= 2^23 the gap
   wins.  Reusable; tied to Flocq's `ulp_le` (monotonicity) + `ulp_bpow`.
   ---------------------------------------------------------------------------- *)

Lemma b64_ulp_round_le_bpow :
  forall (x : R) (e : Z),
    (3 - emax <= e + 1)%Z ->
    (Rabs x <= bpow radix2 e)%R ->
    (b64_ulp (b64_round x) <= bpow radix2 (e + 1 - prec))%R.
Proof.
  intros x e He Hx.
  pose proof (b64_round_abs_le_bpow x e He Hx) as Hrx.
  apply (Rle_trans _ (b64_ulp (bpow radix2 e))).
  - apply (ulp_le radix2 b64_fexp).
    rewrite (Rabs_pos_eq (bpow radix2 e)) by (apply Rlt_le, bpow_gt_0).
    exact Hrx.
  - rewrite (ulp_bpow radix2 b64_fexp e).
    apply Req_le. f_equal.
    unfold b64_fexp, SpecFloat.fexp.
    apply Z.max_l. unfold SpecFloat.emin, emax, prec in *. lia.
Qed.

(* The [0,1] instance the clip boundary needs: ulp(round x) <= 2^(1-prec). *)
Lemma b64_ulp_round_le_unit :
  forall x : R, (Rabs x <= 1)%R ->
    (b64_ulp (b64_round x) <= bpow radix2 (1 - prec))%R.
Proof.
  intros x Hx.
  apply (b64_ulp_round_le_bpow x 0).
  - unfold emax. lia.
  - replace (bpow radix2 0) with 1%R by (simpl; lra). exact Hx.
Qed.


(* -------------------------------------------------------------------------- *)
(* Audit footprint.  Added by the 2026-08-16 categorisation pass: this      *)
(* module previously had NO Print Assumptions footer of its own (its         *)
(* lemmas were printed only from the sibling separation module), which is    *)
(* exactly why the meso-audit B4 exit missed that the slice-13 ulp lemmas    *)
(* mention `b64_round` in their statements and therefore carry               *)
(* `Classical_Prop.classic` (Category C1).  The slice-12 rational-gap        *)
(* lemmas remain classic-free.  Every module prints its own leaves so the    *)
(* per-file audit sees them.                                                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions IZR_abs_ge_1.
Print Assumptions rational_gap.
Print Assumptions grid_quotient_ratio.
Print Assumptions b64_ulp_round_le_bpow.
Print Assumptions b64_ulp_round_le_unit.
