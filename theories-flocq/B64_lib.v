(* ============================================================================
   NetTopologySuite.Proofs.Flocq.B64_lib
   ----------------------------------------------------------------------------
   Wrapper module minimising the seam between Flocq's abstract format
   machinery and concrete binary64 work.

   Accumulated during the Stage D engagement.  Provides:

     - Module-level notations: `b64_fexp`, `b64_round`, `b64_ulp`,
       `b64_format`, `b64_emin`.  Eliminates the `Local Notation` boilerplate
       repeated in five files (B64_bridge, Orient_b64_exact, HotPixel_b64,
       Intersect_b64_exact, B64_Pff_bridge).

     - Typeclass instances: `b64_prec_gt_0`, `b64_fexp_valid`,
       `b64_fexp_monotone`.  Eliminates the explicit
       `@error_le_half_ulp_round radix2 (SpecFloat.fexp prec emax)
         (fexp_correct prec emax prec_gt_0_b64) (fexp_monotone prec emax)
         (fun z => negb (Z.even z))` mouthful at every call site.

     - Pre-instantiated Flocq lemmas: `b64_ulp_le_abs`, `b64_ulp_FLT_0`,
       `b64_error_le_half_ulp_round`, `b64_format_B2R`,
       `b64_generic_format_round`.  Same theorems, no parameter threading.

     - Recurring helpers from Stage D: `b64_round_minus_swap`,
       `b64_round_eq_R_eq` (`f_equal` for the round function).

     - Payload Bcompare reflection (`b64_compare_payload`): finite B2R
       is ± IZR m * bpow e.  Classic-free replacement for
       `Bcompare_correct` / `Rcompare`.

   This file is a forward-looking convenience.  Existing files continue
   to compile with their `Local Notation b64_*` boilerplate; new work
   imports B64_lib and gets the clean API.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude (Opus-4.7)
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import B64_bridge.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Module-level notations (non-Local, accessible to importers).               *)
(* -------------------------------------------------------------------------- *)

Notation b64_fexp   := (SpecFloat.fexp prec emax).
Notation b64_round  := (round radix2 b64_fexp (round_mode mode_b64)).
Notation b64_ulp    := (ulp radix2 b64_fexp).
Notation b64_format := (generic_format radix2 b64_fexp).
Notation b64_emin   := (3 - emax - prec)%Z.

(* -------------------------------------------------------------------------- *)
(* Typeclass instances pre-resolved for binary64.                             *)
(*                                                                            *)
(* Without these, every call to a Flocq theorem like `ulp_le_abs` or         *)
(* `error_le_half_ulp_round` requires explicit instance threading:           *)
(*                                                                            *)
(*   @error_le_half_ulp_round radix2 (SpecFloat.fexp prec emax)              *)
(*     (fexp_correct prec emax prec_gt_0_b64)                                *)
(*     (fexp_monotone prec emax)                                              *)
(*     (fun z => negb (Z.even z)) x                                          *)
(*                                                                            *)
(* With the instances below, Coq's typeclass resolution finds them           *)
(* automatically.  Call sites shrink to:                                     *)
(*                                                                            *)
(*   error_le_half_ulp_round (fun z => negb (Z.even z)) x                    *)
(* -------------------------------------------------------------------------- *)

#[export] Existing Instance prec_gt_0_b64.

#[export] Instance b64_fexp_valid : Valid_exp b64_fexp :=
  fexp_correct prec emax _.

#[export] Instance b64_fexp_monotone : Monotone_exp b64_fexp :=
  fexp_monotone prec emax.

(* -------------------------------------------------------------------------- *)
(* Format witness for binary64 values: B2R is always in `b64_format`.        *)
(* -------------------------------------------------------------------------- *)

Lemma b64_format_B2R :
  forall x : binary64, b64_format (Binary.B2R prec emax x).
Proof. exact (Binary.generic_format_B2R prec emax). Qed.

(* -------------------------------------------------------------------------- *)
(* ulp-related lemmas pre-instantiated for binary64.                          *)
(* -------------------------------------------------------------------------- *)

Lemma b64_ulp_le_abs :
  forall x : R,
    x <> 0 ->
    b64_format x ->
    b64_ulp x <= Rabs x.
Proof. intros; apply ulp_le_abs; assumption. Qed.

Lemma b64_ulp_FLT_0 : b64_ulp 0 = bpow radix2 b64_emin.
Proof.
  apply (@ulp_FLT_0 radix2 b64_emin prec _).
Qed.

(* -------------------------------------------------------------------------- *)
(* Rounding error bound at b64 precision (the workhorse for nonoverlap       *)
(* proofs on TwoSum / Dekker output).                                         *)
(* -------------------------------------------------------------------------- *)

Lemma b64_error_le_half_ulp_round :
  forall x : R,
    Rabs (b64_round x - x) <= b64_ulp (b64_round x) / 2.
Proof.
  intros x.
  pose proof (@error_le_half_ulp_round radix2 b64_fexp
                _ _ (fun z => negb (Z.even z)) x) as H.
  change (Znearest (fun z => negb (Z.even z)))
    with (round_mode mode_b64) in H.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* `b64_round` is identity on values in the binary64 format.                  *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_generic :
  forall x : R, b64_format x -> b64_round x = x.
Proof. intros; apply round_generic; auto with typeclass_instances. Qed.

(* -------------------------------------------------------------------------- *)
(* Helper accumulated from Dekker: rounding a `(a - b)` form equals rounding *)
(* a `(- b + a)` form.  Used to bridge Pff's `-r + x1y1` order with our      *)
(* natural `b64_minus x1y1 r` form.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_minus_swap :
  forall a b : R, b64_round (a - b) = b64_round (- b + a).
Proof. intros; f_equal; ring. Qed.

(* -------------------------------------------------------------------------- *)
(* Congruence lemma for `b64_round`: equal inputs give equal outputs.        *)
(* Useful as a `rewrite` target when arguments are ring-equal but            *)
(* syntactically different.                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_eq_R_eq :
  forall a b : R, a = b -> b64_round a = b64_round b.
Proof. intros a b ->; reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Tactic helpers for the recurring tangent patterns documented in           *)
(* docs/stage-d-feasibility.md.                                              *)
(* -------------------------------------------------------------------------- *)

(* Align `FLT_exp (3 - emax - prec) prec` ↔ `SpecFloat.fexp prec emax` and  *)
(* `Znearest (fun z => negb (Z.even z))` ↔ `round_mode mode_b64` in both    *)
(* goal and all hypotheses.  These are def-equal but syntactically          *)
(* different and trip up Coq's `rewrite` and `reflexivity`.                 *)
Ltac b64_align_forms :=
  repeat first
    [ change (FLT_exp b64_emin prec) with b64_fexp in *
    | change (Znearest (fun z => negb (Z.even z)))
        with (round_mode mode_b64) in *
    | change (bpow radix2 (prec - Z.div2 prec)) with (bpow radix2 27) in * ].

(* -------------------------------------------------------------------------- *)
(* Sanity test: re-prove a Stage D nonoverlap-style lemma using ONLY the    *)
(* wrapper API (no manual instance threading, no `Local Notation`).         *)
(*                                                                            *)
(* This is the SAME shape of proof as `b64_TwoSum_nonoverlap` in            *)
(* `B64_Pff_bridge.v`, but for the rounding-error of a single binary64      *)
(* operation.  If you can read this and understand it, the wrapper has      *)
(* succeeded in minimizing the seam.                                         *)
(* -------------------------------------------------------------------------- *)

Lemma b64_round_error_bounded_by_ulp :
  forall x : R,
    Rabs (x - b64_round x) <= b64_ulp (b64_round x) / 2.
Proof.
  intros x.
  pose proof (b64_error_le_half_ulp_round x) as H.
  rewrite Rabs_minus_sym in H.
  exact H.
Qed.

(* The contrast with the pre-wrapper version (from B64_Pff_bridge.v):       *)
(*                                                                            *)
(*   pose proof (@error_le_half_ulp_round radix2 (SpecFloat.fexp prec emax) *)
(*                 (fexp_correct prec emax prec_gt_0_b64)                    *)
(*                 (fexp_monotone prec emax)                                  *)
(*                 (fun z => negb (Z.even z)) x) as H.                       *)
(*   change (Znearest (fun z => negb (Z.even z)))                            *)
(*     with (round_mode mode_b64) in H.                                      *)
(*                                                                            *)
(* Both forms are now equally easy to write; the wrapper version is        *)
(* readable.                                                                *)

(* -------------------------------------------------------------------------- *)
(* Payload Bcompare: finite B2R is ± IZR m * bpow e.  Bcompare itself is     *)
(* computational; Bcompare_correct / Rcompare are the C2 leak.  Used by      *)
(* HotPixel_b64's four comparison lemmas.  No new module.                    *)
(* -------------------------------------------------------------------------- *)

Lemma B2R_zero :
  forall s, Binary.B2R prec emax (Binary.B754_zero prec emax s) = 0.
Proof. intros. reflexivity. Qed.

Lemma B2R_finite_unsigned :
  forall m e (H : SpecFloat.bounded prec emax m e = true),
    Binary.B2R prec emax (Binary.B754_finite prec emax false m e H)
    = IZR (Z.pos m) * bpow radix2 e.
Proof. intros. reflexivity. Qed.

Lemma B2R_finite_signed :
  forall m e (H : SpecFloat.bounded prec emax m e = true),
    Binary.B2R prec emax (Binary.B754_finite prec emax true m e H)
    = - (IZR (Z.pos m) * bpow radix2 e).
Proof.
  intros.
  change (F2R (Float radix2 (Z.neg m) e) = - F2R (Float radix2 (Z.pos m) e)).
  rewrite <- F2R_Zopp. reflexivity.
Qed.

Lemma F2R_pos_gt_0 :
  forall m e, 0 < F2R (Float radix2 (Z.pos m) e).
Proof.
  intros. apply F2R_gt_0. apply Pos2Z.is_pos.
Qed.

Lemma F2R_neg_lt_0 :
  forall m e, F2R (Float radix2 (Z.neg m) e) < 0.
Proof.
  intros. apply F2R_lt_0. apply Zlt_neg_0.
Qed.

Lemma IZR_pos_bpow_bounds :
  forall m : positive,
    bpow radix2 (Z.pos (digits2_pos m) - 1) <= IZR (Z.pos m) <
    bpow radix2 (Z.pos (digits2_pos m)).
Proof.
  intros m.
  pose proof (Zdigits_correct radix2 (Z.pos m)) as [Hlo Hhi].
  rewrite Z.abs_eq in Hlo, Hhi by apply Pos2Z.is_nonneg.
  rewrite <- Zpos_digits2_pos in Hlo, Hhi.
  assert (Hd : (1 <= Z.pos (digits2_pos m))%Z) by lia.
  split.
  - apply IZR_le in Hlo.
    rewrite (@IZR_Zpower radix2 (Z.pos (digits2_pos m) - 1)) in Hlo by lia.
    exact Hlo.
  - apply IZR_lt in Hhi.
    rewrite (@IZR_Zpower radix2 (Z.pos (digits2_pos m))) in Hhi by lia.
    exact Hhi.
Qed.

Lemma bounded_digits_exp :
  forall m e,
    SpecFloat.bounded prec emax m e = true ->
    ((Z.pos (digits2_pos m) = prec)%Z
     \/ (e = SpecFloat.emin prec emax
         /\ (Z.pos (digits2_pos m) < prec)%Z))
    /\ (SpecFloat.emin prec emax <= e)%Z.
Proof.
  intros m e Hb.
  unfold SpecFloat.bounded, SpecFloat.canonical_mantissa in Hb.
  apply andb_prop in Hb.
  destruct Hb as [Hc _He].
  apply Z.eqb_eq in Hc.
  unfold SpecFloat.fexp, SpecFloat.emin, prec, emax in Hc.
  set (d := Z.pos (digits2_pos m)) in Hc.
  assert (Hmax : Z.max (d + e - 53)%Z (-1074)%Z = e) by (exact Hc).
  split.
  - destruct (Z.max_spec (d + e - 53)%Z (-1074)%Z) as [[Hlt Heq]|[Hge Heq]].
    + right. split.
      * unfold SpecFloat.emin, prec, emax. lia.
      * unfold prec. lia.
    + left. unfold prec. lia.
  - unfold SpecFloat.emin, prec, emax. lia.
Qed.

Lemma bounded_digits_sum_lt :
  forall m1 e1 m2 e2,
    SpecFloat.bounded prec emax m1 e1 = true ->
    SpecFloat.bounded prec emax m2 e2 = true ->
    (e1 < e2)%Z ->
    (Z.pos (digits2_pos m1) + e1 < Z.pos (digits2_pos m2) + e2)%Z.
Proof.
  intros m1 e1 m2 e2 B1 B2 He.
  destruct (bounded_digits_exp m1 e1 B1) as [[Hd1|[_ Hd1]] He1min].
  - destruct (bounded_digits_exp m2 e2 B2) as [[Hd2| [He2 _]] _].
    + lia.
    + lia.
  - destruct (bounded_digits_exp m2 e2 B2) as [[Hd2| [He2 _]] _].
    + lia.
    + lia.
Qed.

Lemma bounded_F2R_exp_lt :
  forall m1 e1 m2 e2,
    SpecFloat.bounded prec emax m1 e1 = true ->
    SpecFloat.bounded prec emax m2 e2 = true ->
    (e1 < e2)%Z ->
    F2R (Float radix2 (Z.pos m1) e1) < F2R (Float radix2 (Z.pos m2) e2).
Proof.
  intros m1 e1 m2 e2 B1 B2 He.
  unfold F2R. simpl.
  pose proof (IZR_pos_bpow_bounds m1) as [H1lo H1hi].
  pose proof (IZR_pos_bpow_bounds m2) as [H2lo H2hi].
  pose proof (bounded_digits_sum_lt m1 e1 m2 e2 B1 B2 He) as Hd.
  set (d1 := Z.pos (digits2_pos m1)) in *.
  set (d2 := Z.pos (digits2_pos m2)) in *.
  apply Rlt_le_trans with (bpow radix2 (d1 + e1)).
  - rewrite bpow_plus.
    apply Rmult_lt_compat_r; [apply bpow_gt_0 | exact H1hi].
  - apply Rle_trans with (bpow radix2 (d2 + e2 - 1)).
    + apply bpow_le. lia.
    + replace (d2 + e2 - 1)%Z with ((d2 - 1) + e2)%Z by lia.
      rewrite bpow_plus.
      apply Rmult_le_compat_r; [apply bpow_ge_0 | exact H2lo].
Qed.

Lemma F2R_pos_eq_same_exp :
  forall m1 m2 e,
    m1 = m2 ->
    F2R (Float radix2 (Z.pos m1) e) = F2R (Float radix2 (Z.pos m2) e).
Proof. intros. subst. reflexivity. Qed.

Lemma F2R_pos_lt_same_exp :
  forall m1 m2 e,
    (m1 < m2)%positive ->
    F2R (Float radix2 (Z.pos m1) e) < F2R (Float radix2 (Z.pos m2) e).
Proof.
  intros. apply F2R_lt. lia.
Qed.

Lemma Bcompare_zero_zero :
  forall sa sb,
    Binary.Bcompare prec emax
      (Binary.B754_zero prec emax sa)
      (Binary.B754_zero prec emax sb) = Some Eq.
Proof. intros. reflexivity. Qed.

Lemma Bcompare_zero_finite :
  forall sa sb m e H,
    Binary.Bcompare prec emax
      (Binary.B754_zero prec emax sa)
      (Binary.B754_finite prec emax sb m e H)
    = Some (if sb then Gt else Lt).
Proof. intros. destruct sb; reflexivity. Qed.

Lemma Bcompare_finite_zero :
  forall sa m e H sb,
    Binary.Bcompare prec emax
      (Binary.B754_finite prec emax sa m e H)
      (Binary.B754_zero prec emax sb)
    = Some (if sa then Lt else Gt).
Proof. intros. destruct sa; reflexivity. Qed.

Lemma Bcompare_finite_finite :
  forall sa ma ea Ha sb mb eb Hb,
    Binary.Bcompare prec emax
      (Binary.B754_finite prec emax sa ma ea Ha)
      (Binary.B754_finite prec emax sb mb eb Hb)
    = Some
        match sa, sb with
        | true, false => Lt
        | false, true => Gt
        | false, false =>
          match Z.compare ea eb with
          | Lt => Lt
          | Gt => Gt
          | Eq => Pos.compare_cont Eq ma mb
          end
        | true, true =>
          match Z.compare ea eb with
          | Lt => Gt
          | Gt => Lt
          | Eq => CompOpp (Pos.compare_cont Eq ma mb)
          end
        end.
Proof. intros. destruct sa, sb; reflexivity. Qed.

Lemma pos_compare_spec' :
  forall m1 m2,
    match Pos.compare m1 m2 with
    | Eq => m1 = m2
    | Lt => (m1 < m2)%positive
    | Gt => (m2 < m1)%positive
    end.
Proof.
  intros m1 m2.
  destruct (Pos.compare_spec m1 m2); assumption.
Qed.

Lemma pos_compare_cont_Eq :
  forall m1 m2, Pos.compare_cont Eq m1 m2 = Pos.compare m1 m2.
Proof. intros. reflexivity. Qed.

Lemma same_sign_mag :
  forall ma ea (Ha : SpecFloat.bounded prec emax ma ea = true)
         mb eb (Hb : SpecFloat.bounded prec emax mb eb = true)
         (c : comparison),
    match Z.compare ea eb with
    | Lt => Lt
    | Gt => Gt
    | Eq => Pos.compare_cont Eq ma mb
    end = c ->
    match c with
    | Lt =>
      F2R (Float radix2 (Z.pos ma) ea) < F2R (Float radix2 (Z.pos mb) eb)
    | Eq =>
      F2R (Float radix2 (Z.pos ma) ea) = F2R (Float radix2 (Z.pos mb) eb)
    | Gt =>
      F2R (Float radix2 (Z.pos mb) eb) < F2R (Float radix2 (Z.pos ma) ea)
    end.
Proof.
  intros ma ea Ha mb eb Hb c Hc.
  destruct (Z.compare_spec ea eb) as [He|He|He].
  - rewrite pos_compare_cont_Eq in Hc.
    pose proof (pos_compare_spec' ma mb) as Hm.
    destruct (Pos.compare ma mb); subst c.
    + rewrite He. apply F2R_pos_eq_same_exp. exact Hm.
    + rewrite He. apply F2R_pos_lt_same_exp. exact Hm.
    + rewrite He. apply F2R_pos_lt_same_exp. exact Hm.
  - subst c.
    apply (bounded_F2R_exp_lt ma ea mb eb Ha Hb He).
  - subst c.
    apply (bounded_F2R_exp_lt mb eb ma ea Hb Ha He).
Qed.

Lemma B2R_finite_pos :
  forall s m e H,
    Binary.B2R prec emax (Binary.B754_finite prec emax s m e H)
    = cond_Ropp s (F2R (Float radix2 (Z.pos m) e)).
Proof.
  intros s m e H.
  unfold Binary.B2R. simpl.
  apply F2R_cond_Zopp.
Qed.

Lemma cond_Ropp_lt_zero :
  forall m e, cond_Ropp true (F2R (Float radix2 (Z.pos m) e)) < 0.
Proof.
  intros. unfold cond_Ropp.
  rewrite <- F2R_Zopp. apply F2R_neg_lt_0.
Qed.

Lemma cond_Ropp_gt_zero :
  forall m e, 0 < cond_Ropp false (F2R (Float radix2 (Z.pos m) e)).
Proof.
  intros. unfold cond_Ropp. apply F2R_pos_gt_0.
Qed.

(* Bcompare constructors vs B2R, without Rcompare. *)
Lemma b64_compare_payload :
  forall a b : binary64,
    Binary.is_finite prec emax a = true ->
    Binary.is_finite prec emax b = true ->
    match Binary.Bcompare prec emax a b with
    | Some Lt => Binary.B2R prec emax a < Binary.B2R prec emax b
    | Some Eq => Binary.B2R prec emax a = Binary.B2R prec emax b
    | Some Gt => Binary.B2R prec emax b < Binary.B2R prec emax a
    | None => False
    end.
Proof.
  intros a b Fa Fb.
  destruct a as [sa | sa | sa pla Hpla | sa ma ea Hea]; try discriminate Fa.
  - destruct b as [sb | sb | sb plb Hplb | sb mb eb Heb]; try discriminate Fb.
    + rewrite Bcompare_zero_zero, !B2R_zero. reflexivity.
    + rewrite Bcompare_zero_finite, B2R_zero, B2R_finite_pos.
      destruct sb; simpl.
      * apply cond_Ropp_lt_zero.
      * apply cond_Ropp_gt_zero.
  - destruct b as [sb | sb | sb plb Hplb | sb mb eb Heb]; try discriminate Fb.
    + rewrite Bcompare_finite_zero, B2R_zero, B2R_finite_pos.
      destruct sa; simpl.
      * apply cond_Ropp_lt_zero.
      * apply cond_Ropp_gt_zero.
    + rewrite Bcompare_finite_finite, !B2R_finite_pos.
      destruct sa as [|], sb as [|]; simpl.
      * set (c0 := match Z.compare ea eb with
                   | Lt => Lt
                   | Gt => Gt
                   | Eq => Pos.compare_cont Eq ma mb
                   end).
        pose proof (same_sign_mag ma ea Hea mb eb Heb c0 eq_refl) as Hmag.
        destruct (Z.compare ea eb); subst c0; unfold cond_Ropp.
        -- rewrite pos_compare_cont_Eq in Hmag |- *.
           destruct (Pos.compare ma mb); simpl.
           ++ f_equal. exact Hmag.
           ++ lra.
           ++ lra.
        -- lra.
        -- lra.
      * apply Rlt_trans with 0.
        -- apply cond_Ropp_lt_zero.
        -- apply cond_Ropp_gt_zero.
      * apply Rlt_trans with 0.
        -- apply cond_Ropp_lt_zero.
        -- apply cond_Ropp_gt_zero.
      * set (c0 := match Z.compare ea eb with
                   | Lt => Lt
                   | Gt => Gt
                   | Eq => Pos.compare_cont Eq ma mb
                   end).
        pose proof (same_sign_mag ma ea Hea mb eb Heb c0 eq_refl) as Hmag.
        destruct c0; exact Hmag.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_format_B2R.
Print Assumptions b64_ulp_le_abs.
Print Assumptions b64_ulp_FLT_0.
Print Assumptions b64_error_le_half_ulp_round.
Print Assumptions b64_round_generic.
Print Assumptions b64_round_minus_swap.
Print Assumptions b64_round_eq_R_eq.
Print Assumptions b64_round_error_bounded_by_ulp.
