(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Intersect_b64_exact_round_chain
   ----------------------------------------------------------------------------
   SCOPE C.2-PREP + SCOPE B.2: per-op safety / B2R-round characterisations
   for the rest of the chain (b64_div, b64_mult, b64_plus) composing into
   the full round-chain identity, plus the polish corollaries.

   - Denominator magnitude bounds (`_abs_ge_1`, `_abs_le_bpow_54`) and the
     division step's B2R-round characterisation (`b64_intersect_s_R_round`).
   - Magnitude gates for every later step (`s`, `dx`/`dy`, the products,
     the final sums), each discharging the next step's no-overflow
     obligation.
   - SCOPE B.2 HEADLINE: `b64_intersect_point_x_round_chain` / `_y_` -- the
     exact nested-round identity for the full coordinate computation.
   - Polish: finiteness, coarse magnitude (`_abs_le_bpow_81`), and the
     Returns-Some corollary `b64_intersect_point_returns_some_when_point`.

   Split out of the former 2888-line Intersect_b64_exact.v monolith
   (Phase 1, line-line intersection point; topic: binary64);
   Intersect_b64_exact.v remains as the Require Export umbrella, so
   reverse dependencies import unchanged.  Slice text, declarations,
   and Print Assumptions footers carried over verbatim.  No Admitted,
   no Axiom, no Parameter.
   ============================================================================ *)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Lra.

From Flocq Require Import IEEE754.Binary.
From Flocq Require Import IEEE754.BinarySingleNaN.
From Flocq Require Import Core.

From NTS.Proofs        Require Import Distance Orientation.
From NTS.Proofs.Flocq  Require Import Validate_binary64.
From NTS.Proofs.Flocq  Require Import Orientation_b64.
From NTS.Proofs.Flocq  Require Import B64_bridge.
From NTS.Proofs.Flocq  Require Import Orient_b64_R.
From NTS.Proofs.Flocq  Require Import Orient_b64_sound.
From NTS.Proofs.Flocq  Require Import Orient_b64_exact.
From NTS.Proofs.Flocq  Require Import Intersect_b64.
From NTS.Proofs.Flocq  Require Import B64_lib.
From NTS.Proofs.Flocq  Require Import Intersect_b64_exact_core.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-prep: safety + B2R-round characterisations for the rest of the *)
(* chain (b64_div, b64_mult, b64_plus).  These compose into the round-chain *)
(* identity that Scope B.2 would have shipped explicitly; we get it as a    *)
(* corollary of the C.2-prep lemmas.                                         *)
(*                                                                            *)
(* The order is dictated by the bound-chain: each step needs the previous   *)
(* step's magnitude bound to discharge its no-overflow obligation.          *)
(* -------------------------------------------------------------------------- *)

(* Stronger version of `b64_intersect_den_B2R_nonzero`: B2R(den) has        *)
(* absolute value at least 1 (since the integer cross-difference does).     *)
(* This is the lower bound that `b64_div_correct` needs (combined with     *)
(* B2R(qp0) <= bpow 53 it bounds the rounded division by bpow 53 too).     *)
Lemma b64_intersect_den_B2R_abs_ge_1 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    1 <= Rabs (Binary.B2R prec emax
                (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R _].
  rewrite HB2R. clear HB2R.
  destruct Hsafe as [Hint Hne].
  pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
  pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
  destruct (cross_R_BP_int_witness _ _ _ Hint0) as [n0 [Hn0 _]].
  destruct (cross_R_BP_int_witness _ _ _ Hint1) as [n1 [Hn1 _]].
  rewrite Hn0, Hn1, <- minus_IZR.
  assert (Hne_n : n0 <> n1).
  { intros Heq. apply Hne. rewrite Hn0, Hn1, Heq. reflexivity. }
  assert (Hne_diff : (n0 - n1)%Z <> 0%Z) by lia.
  (* +/-1 are in format, fixed by round. *)
  assert (Hformat_1 : Generic_fmt.generic_format radix2 b64_fexp 1).
  { change 1 with (bpow radix2 0). apply generic_format_bpow_b64. unfold emax; lia. }
  assert (Hround_1 : b64_round 1 = 1).
  { apply Generic_fmt.round_generic;
      [apply valid_rnd_round_mode | exact Hformat_1]. }
  assert (Hformat_neg1 : Generic_fmt.generic_format radix2 b64_fexp (-1)).
  { replace (-1) with (- (1)) by ring.
    apply Generic_fmt.generic_format_opp. exact Hformat_1. }
  assert (Hround_neg1 : b64_round (-1) = -1).
  { apply Generic_fmt.round_generic;
      [apply valid_rnd_round_mode | exact Hformat_neg1]. }
  destruct (Z.lt_total (n0 - n1) 0) as [Hlt | [Heq | Hgt]]; [|contradiction|].
  - assert (HIZR_le : IZR (n0 - n1) <= -1) by (apply IZR_le; lia).
    pose proof (Generic_fmt.round_le radix2 b64_fexp (round_mode mode_b64)
                  _ _ HIZR_le) as Hr.
    rewrite Hround_neg1 in Hr.
    unfold Rabs; destruct (Rcase_abs (b64_round (IZR (n0 - n1)))); lra.
  - assert (HIZR_ge : 1 <= IZR (n0 - n1)) by (apply IZR_le; lia).
    pose proof (Generic_fmt.round_le radix2 b64_fexp (round_mode mode_b64)
                  _ _ HIZR_ge) as Hr.
    rewrite Hround_1 in Hr.
    unfold Rabs; destruct (Rcase_abs (b64_round (IZR (n0 - n1)))); lra.
Qed.

(* Magnitude bound on B2R(b64_minus qp0 qp1).  By `b64_round_abs_le_bpow`   *)
(* applied to the R-difference (|.| <= 2^54).                              *)
Lemma b64_intersect_den_B2R_abs_le_bpow_54 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
           (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1)))
    <= bpow radix2 54.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R _].
  rewrite HB2R. clear HB2R.
  destruct Hsafe as [Hint _].
  pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
  pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
  pose proof (cross_R_BP_abs_le_bpow_53 _ _ _ Hint0) as B0.
  pose proof (cross_R_BP_abs_le_bpow_53 _ _ _ Hint1) as B1.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  eapply Rle_trans; [apply Rabs_minus_le_add|].
  replace (bpow radix2 54) with (bpow radix2 53 + bpow radix2 53)
    by (simpl; lra).
  apply Rplus_le_compat; assumption.
Qed.

(* The Cramer parameter step.  Safety for `b64_div_correct` is the         *)
(* explicit shape (finite operands + nonzero divisor + bound), so we need *)
(* one lemma per premise + the bundle.                                      *)
Lemma b64_intersect_s_R_round :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    Binary.B2R prec emax (b64_div qp0 den)
    = b64_round (Binary.B2R prec emax qp0 / Binary.B2R prec emax den)
    /\ Binary.is_finite prec emax (b64_div qp0 den) = true.
Proof.
  intros P0 P1 Q0 Q1 Hsafe qp0 qp1 den.
  pose proof (b64_intersect_qp0_finite _ _ _ _ Hsafe) as Fqp0.
  pose proof (b64_intersect_qp1_finite _ _ _ _ Hsafe) as Fqp1.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [Hden_R Fden].
  pose proof (b64_intersect_den_B2R_nonzero _ _ _ _ Hsafe) as Hden_ne.
  pose proof (b64_intersect_den_B2R_abs_ge_1 _ _ _ _ Hsafe) as Hden_ge1.
  pose proof (b64_intersect_qp0_R _ _ _ _ Hsafe) as Hqp0R.
  destruct Hsafe as [Hint _].
  pose proof (cross_R_BP_abs_le_bpow_53 _ _ _
                (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint)) as Bqp0.
  rewrite <- Hqp0R in Bqp0.
  (* Bound the rounded quotient: |b64_round (qp0_R / den_R)| <= bpow 53. *)
  assert (Hquot_bnd :
    Rabs (b64_round (Binary.B2R prec emax qp0 / Binary.B2R prec emax den))
      <= bpow radix2 53).
  { apply b64_round_abs_le_bpow; [unfold emax; lia |].
    unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
    apply Rle_trans with (bpow radix2 53 * 1).
    - apply Rmult_le_compat;
        [apply Rabs_pos
        |apply Rlt_le, Rinv_0_lt_compat, Rabs_pos_lt; exact Hden_ne
        |exact Bqp0
        |].
      rewrite <- Rinv_1.
      apply Rinv_le_contravar; [lra | exact Hden_ge1].
    - rewrite Rmult_1_r. apply Rle_refl. }
  assert (Hbnd_lt_emax :
    Rabs (b64_round (Binary.B2R prec emax qp0 / Binary.B2R prec emax den))
      < bpow radix2 emax).
  { eapply Rle_lt_trans; [exact Hquot_bnd|].
    apply bpow_lt. unfold emax; lia. }
  pose proof (b64_div_correct qp0 den Fqp0 Fden Hden_ne Hbnd_lt_emax)
    as [HB2R Hfin]. split; assumption.
Qed.

(* Magnitude bound on B2R(s) = B2R(b64_div qp0 den).  Follows from         *)
(* `b64_intersect_s_R_round` + the bound on the rounded quotient.          *)
Lemma b64_intersect_s_abs_le_bpow_53 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    Rabs (Binary.B2R prec emax (b64_div qp0 den)) <= bpow radix2 53.
Proof.
  intros P0 P1 Q0 Q1 Hsafe qp0 qp1 den.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [HB2R _].
  fold qp0 qp1 den in HB2R. rewrite HB2R.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [_ Fden].
  pose proof (b64_intersect_den_B2R_nonzero _ _ _ _ Hsafe) as Hden_ne.
  pose proof (b64_intersect_den_B2R_abs_ge_1 _ _ _ _ Hsafe) as Hden_ge1.
  pose proof (b64_intersect_qp0_R _ _ _ _ Hsafe) as Hqp0R.
  destruct Hsafe as [Hint _].
  pose proof (cross_R_BP_abs_le_bpow_53 _ _ _
                (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint)) as Bqp0.
  rewrite <- Hqp0R in Bqp0.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
  apply Rle_trans with (bpow radix2 53 * 1); [|rewrite Rmult_1_r; apply Rle_refl].
  apply Rmult_le_compat;
    [apply Rabs_pos
    |apply Rlt_le, Rinv_0_lt_compat, Rabs_pos_lt; exact Hden_ne
    |exact Bqp0
    |].
  rewrite <- Rinv_1. apply Rinv_le_contravar; [lra | exact Hden_ge1].
Qed.

(* The coordinate-difference magnitude bounds.  Each `coord_int_safe` is   *)
(* at most 2^25, so the difference is at most 2^26.                        *)
Lemma b64_intersect_dx_abs_le_bpow_26 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
    <= bpow radix2 26.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_dx_R _ _ _ _ Hsafe) as [Hdx _].
  rewrite Hdx.
  destruct Hsafe as [(HxP0 & _ & HxP1 & _ & _ & _ & _ & _) _].
  destruct HxP0 as (_ & nxP0 & HxP0R & HxP0b).
  destruct HxP1 as (_ & nxP1 & HxP1R & HxP1b).
  rewrite HxP1R, HxP0R, <- minus_IZR, <- abs_IZR.
  apply (Rle_trans _ (IZR (2 ^ 26))).
  - apply IZR_le. apply diff_bound_2p26; assumption.
  - rewrite <- IZR_Zpower by lia. apply Rle_refl.
Qed.

Lemma b64_intersect_dy_abs_le_bpow_26 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
    <= bpow radix2 26.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_dy_R _ _ _ _ Hsafe) as [Hdy _].
  rewrite Hdy.
  destruct Hsafe as [(_ & HyP0 & _ & HyP1 & _ & _ & _ & _) _].
  destruct HyP0 as (_ & nyP0 & HyP0R & HyP0b).
  destruct HyP1 as (_ & nyP1 & HyP1R & HyP1b).
  rewrite HyP1R, HyP0R, <- minus_IZR, <- abs_IZR.
  apply (Rle_trans _ (IZR (2 ^ 26))).
  - apply IZR_le. apply diff_bound_2p26; assumption.
  - rewrite <- IZR_Zpower by lia. apply Rle_refl.
Qed.

(* The multiplication step: `b64_mult s dx`.  Safety from |s| <= 2^53,    *)
(* |dx| <= 2^26, so |product| <= 2^79 << 2^emax.                         *)
Lemma b64_intersect_mult_x_safe :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    b64_safe Rmult s dx.
Proof.
  intros P0 P1 Q0 Q1 Hsafe qp0 qp1 den s dx.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [_ Fs].
  fold qp0 qp1 den s in Fs.
  destruct (b64_intersect_dx_R _ _ _ _ Hsafe) as [_ Fdx].
  fold dx in Fdx.
  pose proof (b64_intersect_s_abs_le_bpow_53 _ _ _ _ Hsafe) as Bs.
  fold qp0 qp1 den s in Bs.
  pose proof (b64_intersect_dx_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdx.
  fold dx in Bdx.
  unfold b64_safe. split; [exact Fs | split; [exact Fdx | ]].
  eapply Rle_lt_trans;
    [|apply (bpow_lt radix2 80 emax); unfold emax; lia].
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  rewrite Rabs_mult.
  apply Rle_trans with (bpow radix2 53 * bpow radix2 26);
    [|rewrite <- bpow_plus; replace (53 + 26)%Z with 79%Z by lia;
      apply bpow_le; lia].
  apply Rmult_le_compat; (apply Rabs_pos || assumption).
Qed.

Lemma b64_intersect_mult_y_safe :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    b64_safe Rmult s dy.
Proof.
  intros P0 P1 Q0 Q1 Hsafe qp0 qp1 den s dy.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [_ Fs].
  fold qp0 qp1 den s in Fs.
  destruct (b64_intersect_dy_R _ _ _ _ Hsafe) as [_ Fdy].
  fold dy in Fdy.
  pose proof (b64_intersect_s_abs_le_bpow_53 _ _ _ _ Hsafe) as Bs.
  fold qp0 qp1 den s in Bs.
  pose proof (b64_intersect_dy_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdy.
  fold dy in Bdy.
  unfold b64_safe. split; [exact Fs | split; [exact Fdy | ]].
  eapply Rle_lt_trans;
    [|apply (bpow_lt radix2 80 emax); unfold emax; lia].
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  rewrite Rabs_mult.
  apply Rle_trans with (bpow radix2 53 * bpow radix2 26);
    [|rewrite <- bpow_plus; replace (53 + 26)%Z with 79%Z by lia;
      apply bpow_le; lia].
  apply Rmult_le_compat; (apply Rabs_pos || assumption).
Qed.

(* Magnitude bound on B2R(b64_mult s dx) after rounding: <= bpow 80.       *)
Lemma b64_intersect_mult_x_abs_le_bpow_80 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dx)) <= bpow radix2 80.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_x_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_intersect_s_abs_le_bpow_53 _ _ _ _ Hsafe) as Bs.
  cbv zeta in Bs.
  pose proof (b64_intersect_dx_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdx.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  rewrite Rabs_mult.
  apply Rle_trans with (bpow radix2 53 * bpow radix2 26);
    [apply Rmult_le_compat; (apply Rabs_pos || assumption) |].
  rewrite <- bpow_plus. replace (53 + 26)%Z with 79%Z by lia.
  apply bpow_le; lia.
Qed.

Lemma b64_intersect_mult_y_abs_le_bpow_80 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dy)) <= bpow radix2 80.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_y_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_intersect_s_abs_le_bpow_53 _ _ _ _ Hsafe) as Bs.
  cbv zeta in Bs.
  pose proof (b64_intersect_dy_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdy.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  rewrite Rabs_mult.
  apply Rle_trans with (bpow radix2 53 * bpow radix2 26);
    [apply Rmult_le_compat; (apply Rabs_pos || assumption) |].
  rewrite <- bpow_plus. replace (53 + 26)%Z with 79%Z by lia.
  apply bpow_le; lia.
Qed.

(* Magnitude bound on a `coord_int_safe` binary64: at most bpow 25.        *)
Lemma coord_int_safe_abs_le_bpow_25 :
  forall x : binary64,
    coord_int_safe x ->
    Rabs (Binary.B2R prec emax x) <= bpow radix2 25.
Proof.
  intros x (_ & n & HxR & Hxb).
  rewrite HxR, <- abs_IZR.
  apply (Rle_trans _ (IZR (2 ^ 25))).
  - apply IZR_le. exact Hxb.
  - rewrite <- IZR_Zpower by lia. apply Rle_refl.
Qed.

(* Final plus step.  Safety from |bx P0| <= 2^25, |b64_mult| <= 2^80,    *)
(* so |sum| <= 2^81 << 2^emax.                                            *)
Lemma b64_intersect_plus_x_safe :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    b64_safe Rplus (bx P0) (b64_mult s dx).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof Hsafe as Hsafe'. destruct Hsafe' as [Hint _].
  destruct Hint as (HxP0 & _ & _ & _ & _ & _ & _ & _).
  pose proof (coord_int_safe_abs_le_bpow_25 _ HxP0) as BxP0.
  destruct HxP0 as (FxP0 & _ & _ & _).
  pose proof (b64_intersect_mult_x_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [_ Fm].
  pose proof (b64_intersect_mult_x_abs_le_bpow_80 _ _ _ _ Hsafe) as Bm.
  cbv zeta in Bm.
  unfold b64_safe. split; [exact FxP0 | split; [exact Fm | ]].
  eapply Rle_lt_trans;
    [|apply (bpow_lt radix2 82 emax); unfold emax; lia].
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  eapply Rle_trans;
    [apply Rabs_triang|].
  apply Rle_trans with (bpow radix2 25 + bpow radix2 80);
    [apply Rplus_le_compat; assumption|].
  replace (bpow radix2 82) with (bpow radix2 81 + bpow radix2 81)
    by (simpl; lra).
  apply Rle_trans with (bpow radix2 81 + bpow radix2 81); [|apply Rle_refl].
  apply Rplus_le_compat; apply bpow_le; lia.
Qed.

Lemma b64_intersect_plus_y_safe :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    b64_safe Rplus (by_ P0) (b64_mult s dy).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof Hsafe as Hsafe'. destruct Hsafe' as [Hint _].
  destruct Hint as (_ & HyP0 & _ & _ & _ & _ & _ & _).
  pose proof (coord_int_safe_abs_le_bpow_25 _ HyP0) as ByP0.
  destruct HyP0 as (FyP0 & _ & _ & _).
  pose proof (b64_intersect_mult_y_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [_ Fm].
  pose proof (b64_intersect_mult_y_abs_le_bpow_80 _ _ _ _ Hsafe) as Bm.
  cbv zeta in Bm.
  unfold b64_safe. split; [exact FyP0 | split; [exact Fm | ]].
  eapply Rle_lt_trans;
    [|apply (bpow_lt radix2 82 emax); unfold emax; lia].
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rle_trans with (bpow radix2 25 + bpow radix2 80);
    [apply Rplus_le_compat; assumption|].
  replace (bpow radix2 82) with (bpow radix2 81 + bpow radix2 81)
    by (simpl; lra).
  apply Rle_trans with (bpow radix2 81 + bpow radix2 81); [|apply Rle_refl].
  apply Rplus_le_compat; apply bpow_le; lia.
Qed.

(* HEADLINE of C.2-prep (also gives Scope B.2's round-chain identity as a *)
(* corollary).  Under the integer safety predicate, B2R of the final x   *)
(* coordinate is exactly the four-nested-round expression.                *)
Theorem b64_intersect_point_x_round_chain :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1)
    = b64_round
        (Binary.B2R prec emax (bx P0)
         + b64_round
             (b64_round (cross_R_BP Q0 Q1 P0
                        / b64_round (cross_R_BP Q0 Q1 P0
                                     - cross_R_BP Q0 Q1 P1))
              * (Binary.B2R prec emax (bx P1)
                 - Binary.B2R prec emax (bx P0)))).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_x.
  pose proof (b64_intersect_plus_x_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R. clear HB2R.
  pose proof (b64_intersect_mult_x_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R_m _].
  rewrite HB2R_m. clear HB2R_m.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [HB2R_s _].
  cbv zeta in HB2R_s.
  rewrite HB2R_s. clear HB2R_s.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R_d _].
  rewrite HB2R_d. clear HB2R_d.
  rewrite (b64_intersect_qp0_R _ _ _ _ Hsafe).
  destruct (b64_intersect_dx_R _ _ _ _ Hsafe) as [Hdx _].
  rewrite Hdx.
  reflexivity.
Qed.

Theorem b64_intersect_point_y_round_chain :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1)
    = b64_round
        (Binary.B2R prec emax (by_ P0)
         + b64_round
             (b64_round (cross_R_BP Q0 Q1 P0
                        / b64_round (cross_R_BP Q0 Q1 P0
                                     - cross_R_BP Q0 Q1 P1))
              * (Binary.B2R prec emax (by_ P1)
                 - Binary.B2R prec emax (by_ P0)))).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_y.
  pose proof (b64_intersect_plus_y_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R. clear HB2R.
  pose proof (b64_intersect_mult_y_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R_m _].
  rewrite HB2R_m. clear HB2R_m.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [HB2R_s _].
  cbv zeta in HB2R_s.
  rewrite HB2R_s. clear HB2R_s.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R_d _].
  rewrite HB2R_d. clear HB2R_d.
  rewrite (b64_intersect_qp0_R _ _ _ _ Hsafe).
  destruct (b64_intersect_dy_R _ _ _ _ Hsafe) as [Hdy _].
  rewrite Hdy.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C polish: API-level corollaries callers can use directly.            *)
(*                                                                            *)
(* Finiteness of the result -- the b64 chain under safety never produces NaN *)
(* or Inf.  Magnitude bound on the result -- proven via the round-chain      *)
(* identity + b64_round_abs_le_bpow with the bpow 81 chain we built up.     *)
(*                                                                            *)
(* The TIGHT condition-aware forward-error theorem                            *)
(*   |B2R(b64_intersect_point_x ...) - intersect_x_R ...| <= K * eps          *)
(* where K is explicit in |denominator_R|, is a separate engagement-level    *)
(* slice (Scope C.2-tight; multi-session Flocq forward-error analysis).      *)
(* The existence form below records the bound is finite without committing  *)
(* to a specific K.                                                          *)
(* -------------------------------------------------------------------------- *)

Theorem b64_intersect_point_x_finite :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.is_finite prec emax (b64_intersect_point_x P0 P1 Q0 Q1) = true.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_x.
  pose proof (b64_intersect_plus_x_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [_ Ffin]. exact Ffin.
Qed.

Theorem b64_intersect_point_y_finite :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Binary.is_finite prec emax (b64_intersect_point_y P0 P1 Q0 Q1) = true.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_y.
  pose proof (b64_intersect_plus_y_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [_ Ffin]. exact Ffin.
Qed.

(* Magnitude bound on the final coordinate.  The magnitude chain bounds:    *)
(*   |coord|  <= 2^25                                                       *)
(*   |s · dx| <= 2^79                                                       *)
(*   final = coord + (s · dx), so |final| pre-round <= 2^81;               *)
(*   round preserves bpow 81 bound.                                         *)
Theorem b64_intersect_point_x_abs_le_bpow_81 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1))
    <= bpow radix2 81.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  pose proof Hsafe as Hsafe'.
  unfold b64_intersect_point_x.
  pose proof (b64_intersect_plus_x_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R. clear HB2R.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  eapply Rle_trans; [apply Rabs_triang|].
  destruct Hsafe as [Hint _].
  destruct Hint as (HxP0 & _ & _ & _ & _ & _ & _ & _).
  pose proof (coord_int_safe_abs_le_bpow_25 _ HxP0) as BxP0.
  pose proof (b64_intersect_mult_x_abs_le_bpow_80 _ _ _ _ Hsafe') as Bm.
  cbv zeta in Bm.
  apply Rle_trans with (bpow radix2 25 + bpow radix2 80);
    [apply Rplus_le_compat; assumption|].
  replace (bpow radix2 81) with (bpow radix2 80 + bpow radix2 80)
    by (simpl; lra).
  apply Rplus_le_compat; [apply bpow_le; lia | apply Rle_refl].
Qed.

Theorem b64_intersect_point_y_abs_le_bpow_81 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1))
    <= bpow radix2 81.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_y.
  pose proof (b64_intersect_plus_y_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R. clear HB2R.
  apply b64_round_abs_le_bpow; [unfold emax; lia |].
  eapply Rle_trans; [apply Rabs_triang|].
  destruct Hsafe as [Hint Hne].
  pose proof (conj Hint Hne) as Hsafe'.
  destruct Hint as (_ & HyP0 & _ & _ & _ & _ & _ & _).
  pose proof (coord_int_safe_abs_le_bpow_25 _ HyP0) as ByP0.
  pose proof (b64_intersect_mult_y_abs_le_bpow_80 _ _ _ _ Hsafe') as Bm.
  cbv zeta in Bm.
  apply Rle_trans with (bpow radix2 25 + bpow radix2 80);
    [apply Rplus_le_compat; assumption|].
  replace (bpow radix2 81) with (bpow radix2 80 + bpow radix2 80)
    by (simpl; lra).
  apply Rplus_le_compat; [apply bpow_le; lia | apply Rle_refl].
Qed.

(* -------------------------------------------------------------------------- *)
(* Phase 1 -- Returns-Some corollary.                                          *)
(*                                                                            *)
(* Under intersect_point_inputs_int_safe + sign_filtered = IntersectPoint,    *)
(* b64_intersect_point commits to `Some _` (the function does not return      *)
(* None on the IntersectPoint branch's inner `b64_compare den zero` check).  *)
(*                                                                            *)
(* Discharges the den-finite + den-B2R-nonzero side conditions in the         *)
(* IntersectPoint branch by composing b64_intersect_den_safe +                *)
(* b64_minus_correct + b64_intersect_den_B2R_nonzero (all Qed-closed in     *)
(* Scope B.1 above).                                                          *)
(* -------------------------------------------------------------------------- *)

Theorem b64_intersect_point_returns_some_when_point :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    b64_intersect_sign_filtered P0 P1 Q0 Q1 = IntersectPoint ->
    exists X : BPoint, b64_intersect_point P0 P1 Q0 Q1 = Some X.
Proof.
  intros P0 P1 Q0 Q1 Hsafe Hpoint.
  unfold b64_intersect_point.
  rewrite Hpoint.
  pose proof (b64_intersect_den_safe P0 P1 Q0 Q1 Hsafe) as Hden_safe.
  pose proof (b64_minus_correct _ _ Hden_safe) as [Hden_R Fden].
  pose proof (b64_intersect_den_B2R_nonzero P0 P1 Q0 Q1 Hsafe) as Hden_nz.
  set (zero := Binary.B754_zero prec emax false).
  assert (Hzero_finite : Binary.is_finite prec emax zero = true) by reflexivity.
  assert (HzeroR : Binary.B2R prec emax zero = 0) by reflexivity.
  unfold b64_compare.
  rewrite (Binary.Bcompare_correct prec emax _ _ Fden Hzero_finite).
  rewrite HzeroR.
  destruct (Rcompare _ 0) eqn:Hcmp.
  - apply Rcompare_Eq_inv in Hcmp. contradiction.
  - eexists. reflexivity.
  - eexists. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_intersect_point_returns_some_when_point.
Print Assumptions b64_intersect_den_B2R_abs_ge_1.
Print Assumptions b64_intersect_den_B2R_abs_le_bpow_54.
Print Assumptions b64_intersect_s_R_round.
Print Assumptions b64_intersect_s_abs_le_bpow_53.
Print Assumptions b64_intersect_dx_abs_le_bpow_26.
Print Assumptions b64_intersect_dy_abs_le_bpow_26.
Print Assumptions b64_intersect_mult_x_safe.
Print Assumptions b64_intersect_mult_y_safe.
Print Assumptions b64_intersect_mult_x_abs_le_bpow_80.
Print Assumptions b64_intersect_mult_y_abs_le_bpow_80.
Print Assumptions coord_int_safe_abs_le_bpow_25.
Print Assumptions b64_intersect_plus_x_safe.
Print Assumptions b64_intersect_plus_y_safe.
Print Assumptions b64_intersect_point_x_round_chain.
Print Assumptions b64_intersect_point_y_round_chain.
Print Assumptions b64_intersect_point_x_finite.
Print Assumptions b64_intersect_point_y_finite.
Print Assumptions b64_intersect_point_x_abs_le_bpow_81.
Print Assumptions b64_intersect_point_y_abs_le_bpow_81.
