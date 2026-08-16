(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Intersect_b64_exact_forward_error
   ----------------------------------------------------------------------------
   SCOPE C.2-TIGHT SESSIONS 1-5 (+ the y mirror): the four-layer
   forward-error cascade for the intersection coordinates.

     Layer 1 (den):   `b64_intersect_den_forward_error`   <= bpow 1
     Layer 2 (s):     `b64_intersect_s_forward_error`
                      <= 1 + bpow 54 / |qp0_R - qp1_R|
     Layer 3 (s*d_):  `b64_intersect_mult_{x,y}_forward_error`
                      <= bpow 27 + bpow 26 + bpow 80 / |qp0_R - qp1_R|
     Layer 4 (final): `b64_intersect_point_{x,y}_forward_error`
                      <= bpow 29 + bpow 80 / |qp0_R - qp1_R|

   Shared auxiliary `b64_ulp_le_at_magnitude_uniform` (uniform ulp bound
   at arbitrary magnitude) plus the per-layer round/carry decompositions,
   and the foundation `b64_intersect_den_error_le_1` cited by the parallel
   tight chain (Intersect_b64_exact_tight.v).

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
From NTS.Proofs.Flocq  Require Import Intersect_b64_exact_round_chain.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-tight Session 1 -- forward-error bound for layer 1 (denominator).*)
(*                                                                            *)
(* The b64 intersection chain has four nested rounds (from the                *)
(* `b64_intersect_point_x_round_chain` identity):                             *)
(*                                                                            *)
(*   layer 1 -- den   = b64_round (qp0_R - qp1_R)                             *)
(*   layer 2 -- s     = b64_round (qp0_R / den)                               *)
(*   layer 3 -- s*dx  = b64_round (s * (B2R(bx P1) - B2R(bx P0)))             *)
(*   layer 4 -- final = b64_round (B2R(bx P0) + s*dx)                         *)
(*                                                                            *)
(* The Scope C.2-tight goal is the propagated forward-error theorem           *)
(*    |B2R(b64_intersect_point_x ...) - intersect_x_R (BP2P P0) ...|         *)
(*     <= K * eps                                                              *)
(* where `K` is explicit in the input magnitude and the denominator           *)
(* separation.                                                                *)
(*                                                                            *)
(* This session lands LAYER 1: the absolute forward-error bound on the        *)
(* denominator's round.  `qp0_R - qp1_R` is an integer of magnitude <= 2^54,  *)
(* so the round error is bounded by ulp/2 = 2^54 * 2^-52 / 2 = bpow 1.        *)
(* The bound is sharp at the bottom bit: one half-ulp of a maximum-magnitude  *)
(* denominator equals 2 = bpow 1.                                             *)
(* -------------------------------------------------------------------------- *)

(* Shared auxiliary for the Scope C.2-tight cascade: uniform ulp bound at    *)
(* arbitrary magnitude.  Used at n=54 (layer 1), n=53 (layer 2), n=80        *)
(* (layer 3), and n=81 (layer 4).  Subsumes earlier specialised versions     *)
(* introduced during Sessions 1 and 3; subnormal/zero case via ulp_FLT_small,*)
(* normal case via ulp_FLT_le.                                                *)
Lemma b64_ulp_le_at_magnitude_uniform :
  forall (x : R) (n : Z),
    (0 <= n)%Z ->
    Rabs x <= bpow radix2 n ->
    b64_ulp x <= bpow radix2 (n - prec + 1).
Proof.
  intros x n Hn Hle.
  destruct (Rlt_le_dec (Rabs x) (bpow radix2 (b64_emin + prec))) as [Hsmall|Hbig].
  - assert (Hulp_small : b64_ulp x = bpow radix2 b64_emin)
      by (apply (@ulp_FLT_small radix2 b64_emin prec _ x Hsmall)).
    rewrite Hulp_small.
    apply bpow_le. unfold b64_emin, emax, prec; lia.
  - pose proof (ulp_FLT_le radix2 b64_emin prec x) as Hulp.
    assert (Hpre : bpow radix2 (b64_emin + prec - 1) <= Rabs x).
    { apply Rle_trans with (bpow radix2 (b64_emin + prec)); [|exact Hbig].
      apply bpow_le; lia. }
    specialize (Hulp Hpre).
    apply Rle_trans with (Rabs x * bpow radix2 (1 - prec)); [exact Hulp|].
    replace (bpow radix2 (n - prec + 1))
      with (bpow radix2 n * bpow radix2 (1 - prec)).
    + apply Rmult_le_compat_r; [apply bpow_ge_0|exact Hle].
    + rewrite <- bpow_plus. apply f_equal. lia.
Qed.

(* Layer 1 forward-error bound: B2R of the denominator deviates from the     *)
(* exact R-side integer difference by at most bpow 1 = 2.                    *)
Theorem b64_intersect_den_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
            (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))
          - (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= bpow radix2 1.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_error_le_half_ulp_round
                (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)) as Herr.
  eapply Rle_trans; [exact Herr|].
  pose proof (b64_intersect_den_B2R_abs_le_bpow_54 _ _ _ _ Hsafe) as Bden.
  rewrite HB2R in Bden.
  pose proof (b64_ulp_le_at_magnitude_uniform _ 54 ltac:(lia) Bden) as Hulp_le.
  apply Rle_trans
    with (bpow radix2 2 / 2); [|simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra|exact Hulp_le].
Qed.

(* -------------------------------------------------------------------------- *)
(* Tight integer-regime variant of Layer 1.                                   *)
(*                                                                            *)
(* `b64_intersect_den_forward_error` above bounds the denominator rounding   *)
(* error by `bpow 1 = 2` -- derived via output-form half-ulp on a denominator *)
(* with `|den_R| <= bpow 54`, yielding ulp/2 <= bpow 2 / 2 = 2.                *)
(*                                                                            *)
(* The tight integer-regime fact: `qp0_R - qp1_R` is an INTEGER (each         *)
(* cross_R_BP is an integer in the integer regime, per `cross_R_BP_int_witness`),*)
(* with `|.| <= 2^(prec+1) = 2^54`.  Rounding such an integer in binary64    *)
(* introduces an error of at most 1 (exact for |.| <= 2^prec; half-ulp = 1   *)
(* in the strict mid-band; exact at the boundary 2^(prec+1) which is a power *)
(* of 2).  This is 2x tighter than the bpow-1 form above.                    *)
(*                                                                            *)
(* Foundation: `b64_round_IZR_error_le_1` in Orient_b64_exact.v.              *)
(*                                                                            *)
(* The parallel chain below (`_s_carry_error_tight`,                          *)
(* `_mult_x_carry_error_tight`, ..., `_point_x_forward_error_tight`) cites    *)
(* this lemma instead of `b64_intersect_den_forward_error` and propagates    *)
(* the 2x tightening through Layers 2-4 to a tighter headline K constant in  *)
(* the final `_vs_intersect_x_R` corollary.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma b64_intersect_den_error_le_1 :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
            (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))
          - (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= 1.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_den_R_round _ _ _ _ Hsafe) as [HB2R _].
  rewrite HB2R. clear HB2R.
  destruct Hsafe as [Hint _].
  pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
  pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
  destruct (cross_R_BP_int_witness _ _ _ Hint0) as [n0 [Hn0_eq Hn0_bnd]].
  destruct (cross_R_BP_int_witness _ _ _ Hint1) as [n1 [Hn1_eq Hn1_bnd]].
  rewrite Hn0_eq, Hn1_eq, <- minus_IZR.
  apply b64_round_IZR_error_le_1.
  apply Z.abs_le in Hn0_bnd.
  apply Z.abs_le in Hn1_bnd.
  apply Z.abs_le.
  unfold prec in *. simpl in *. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-tight Session 2 -- denominator-carryover bound for layer 2.      *)
(*                                                                            *)
(* Layer 2 of the b64 intersection chain rounds the EXACT-numerator over     *)
(* ROUNDED-denominator quotient:                                              *)
(*    B2R(s) = b64_round (qp0_R / B2R(den))                                    *)
(*    s_exact = qp0_R / (qp0_R - qp1_R)                                        *)
(*                                                                            *)
(* The full layer-2 forward error decomposes algebraically:                   *)
(*    B2R(s) - s_exact                                                         *)
(*  = (b64_round(qp0_R/den_R) - qp0_R/den_R)              [Delta_round]       *)
(*  + (qp0_R/den_R - qp0_R/den_exact)                      [Delta_carry]       *)
(*                                                                            *)
(* This session lands Delta_carry only -- the pure-R perturbation of the      *)
(* quotient under denominator rounding.  Session 3 lands Delta_round (which   *)
(* needs subnormal-range ulp bookkeeping for b64_round of the division) and  *)
(* composes both into the full layer-2 bound.                                *)
(*                                                                            *)
(* Algebraic identity:                                                        *)
(*    qp0_R / den_R - qp0_R / den_exact                                       *)
(*  = qp0_R * (den_exact - den_R) / (den_R * den_exact)                       *)
(* Bound chain:                                                               *)
(*    |Delta_carry|                                                            *)
(*  <= |qp0_R| * (Session 1 bound) / (|den_R| * |den_exact|)                  *)
(*  <= bpow 53 * bpow 1 / (1 * |den_exact|)                                    *)
(*  =  bpow 54 / |den_exact|.                                                  *)
(*                                                                            *)
(* The 1/|den_exact| factor exposes the classical condition number for the    *)
(* Cramer division step.                                                      *)
(* -------------------------------------------------------------------------- *)

Theorem b64_intersect_s_carry_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (cross_R_BP Q0 Q1 P0
            / Binary.B2R prec emax
                (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= bpow radix2 54
       / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  set (qp0_R := cross_R_BP Q0 Q1 P0).
  set (qp1_R := cross_R_BP Q0 Q1 P1).
  set (den_R := Binary.B2R prec emax
                  (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))).
  set (den_exact := qp0_R - qp1_R).
  (* Step 1: facts about den_R and den_exact. *)
  assert (Hden_exact_ne : den_exact <> 0).
  { unfold den_exact, qp0_R, qp1_R. destruct Hsafe as [_ Hne]. lra. }
  assert (Hden_R_ne : den_R <> 0).
  { unfold den_R. apply (b64_intersect_den_B2R_nonzero _ _ _ _ Hsafe). }
  assert (Hden_R_ge1 : 1 <= Rabs den_R).
  { unfold den_R. apply (b64_intersect_den_B2R_abs_ge_1 _ _ _ _ Hsafe). }
  assert (Hden_exact_ge1 : 1 <= Rabs den_exact).
  { unfold den_exact, qp0_R, qp1_R.
    destruct Hsafe as [Hint Hne].
    pose proof (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint) as Hint0.
    pose proof (intersect_inputs_int_safe_Q0Q1P1 _ _ _ _ Hint) as Hint1.
    destruct (cross_R_BP_int_witness _ _ _ Hint0) as [n0 [Hn0 _]].
    destruct (cross_R_BP_int_witness _ _ _ Hint1) as [n1 [Hn1 _]].
    rewrite Hn0, Hn1, <- minus_IZR, <- abs_IZR.
    apply IZR_le.
    assert (Hne_n : n0 <> n1).
    { intros Heq. apply Hne. rewrite Hn0, Hn1, Heq. reflexivity. }
    lia. }
  assert (Hqp0_R_bnd : Rabs qp0_R <= bpow radix2 53).
  { unfold qp0_R.
    destruct Hsafe as [Hint _].
    apply (cross_R_BP_abs_le_bpow_53 _ _ _
             (intersect_inputs_int_safe_Q0Q1P0 _ _ _ _ Hint)). }
  assert (Hden_err : Rabs (den_R - den_exact) <= bpow radix2 1).
  { unfold den_R, den_exact, qp0_R, qp1_R.
    apply (b64_intersect_den_forward_error _ _ _ _ Hsafe). }
  (* Step 2: algebraic identity for the perturbation. *)
  assert (Hpos_R : 0 < Rabs den_R) by (apply Rabs_pos_lt; exact Hden_R_ne).
  assert (Hpos_exact : 0 < Rabs den_exact)
    by (apply Rabs_pos_lt; exact Hden_exact_ne).
  replace (qp0_R / den_R - qp0_R / den_exact)
    with (qp0_R * (den_exact - den_R) / (den_R * den_exact))
    by (field; split; assumption).
  (* Step 3: factor Rabs through the division and bound. *)
  unfold Rdiv at 1.
  rewrite Rabs_mult.
  rewrite Rabs_inv.
  rewrite (Rabs_mult qp0_R (den_exact - den_R)).
  rewrite (Rabs_mult den_R den_exact).
  (* Now: |qp0_R| * |den_exact - den_R| / (|den_R| * |den_exact|)               *)
  (*    <= bpow 54 / |den_exact|.                                                *)
  apply Rle_trans
    with ((bpow radix2 53 * bpow radix2 1) / (1 * Rabs den_exact)).
  - apply Rmult_le_compat;
      [ apply Rmult_le_pos; apply Rabs_pos
      | apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; assumption
      |
      | ].
    + (* Numerator: |qp0_R| * |den_exact - den_R| <= bpow 53 * bpow 1. *)
      apply Rmult_le_compat;
        [apply Rabs_pos|apply Rabs_pos|exact Hqp0_R_bnd|].
      replace (Rabs (den_exact - den_R)) with (Rabs (den_R - den_exact))
        by (rewrite <- Rabs_Ropp; f_equal; ring).
      exact Hden_err.
    + (* Denominator inverse: 1/(|den_R| * |den_exact|) <= 1/(1 * |den_exact|). *)
      apply Rinv_le_contravar.
      * rewrite Rmult_1_l. exact Hpos_exact.
      * apply Rmult_le_compat_r; [apply Rlt_le; exact Hpos_exact|exact Hden_R_ge1].
  - (* Simplify constants: bpow 53 * bpow 1 = bpow 54, divide by 1. *)
    rewrite Rmult_1_l.
    apply Rmult_le_compat_r;
      [apply Rlt_le, Rinv_0_lt_compat; exact Hpos_exact|].
    rewrite <- bpow_plus. simpl. apply Rle_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-tight Session 3 -- layer 2 forward-error closure.                *)
(*                                                                            *)
(* Lands Delta_round (the b64_round error on the quotient) and composes it    *)
(* with Session 2's Delta_carry into the full layer-2 forward-error bound.    *)
(*                                                                            *)
(* The Delta_round bound is |b64_round (qp0_R/den_R) - qp0_R/den_R| <= 1.     *)
(* Proof: half-ulp at magnitude <= bpow 53.  Uniform across normal/subnormal  *)
(* /zero regimes via `ulp_FLT_small` (constant ulp = bpow emin in subnormal   *)
(* range and at zero) + `ulp_FLT_le` (relative bound in normal range).        *)
(*                                                                            *)
(* Composition: B2R(b64_div ...) - qp0_R/(qp0_R - qp1_R)                      *)
(*            = Delta_round + Delta_carry                                      *)
(* with |total| <= 1 + bpow 54 / |qp0_R - qp1_R|.                              *)
(* -------------------------------------------------------------------------- *)

(* Delta_round: the b64_round error on the layer-2 quotient.                  *)
Lemma b64_intersect_s_round_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
            (b64_div (b64_orient2d Q0 Q1 P0)
                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                (b64_orient2d Q0 Q1 P1)))
          - cross_R_BP Q0 Q1 P0
            / Binary.B2R prec emax
                (b64_minus (b64_orient2d Q0 Q1 P0)
                           (b64_orient2d Q0 Q1 P1)))
    <= 1.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [HB2R _].
  cbv zeta in HB2R. rewrite HB2R.
  pose proof (b64_intersect_qp0_R _ _ _ _ Hsafe) as Hqp0R.
  rewrite Hqp0R.
  set (qp0_R := cross_R_BP Q0 Q1 P0).
  set (den_R := Binary.B2R prec emax
                  (b64_minus (b64_orient2d Q0 Q1 P0)
                             (b64_orient2d Q0 Q1 P1))).
  pose proof (b64_error_le_half_ulp_round (qp0_R / den_R)) as Herr.
  eapply Rle_trans; [exact Herr|].
  assert (Hbnd : Rabs (b64_round (qp0_R / den_R)) <= bpow radix2 53).
  { pose proof (b64_intersect_s_abs_le_bpow_53 _ _ _ _ Hsafe) as Bs.
    cbv zeta in Bs.
    destruct (b64_intersect_s_R_round _ _ _ _ Hsafe) as [HB2R2 _].
    cbv zeta in HB2R2.
    rewrite HB2R2 in Bs.
    rewrite (b64_intersect_qp0_R _ _ _ _ Hsafe) in Bs.
    exact Bs. }
  pose proof (b64_ulp_le_at_magnitude_uniform _ 53 ltac:(lia) Hbnd) as Hulp.
  apply Rle_trans with (bpow radix2 1 / 2); [|simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra | exact Hulp].
Qed.

(* Layer 2 full forward-error bound: composition of Delta_round (Session 3)  *)
(* and Delta_carry (Session 2).                                              *)
Theorem b64_intersect_s_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
            (b64_div (b64_orient2d Q0 Q1 P0)
                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                (b64_orient2d Q0 Q1 P1)))
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= 1 + bpow radix2 54
            / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  set (qp0_R := cross_R_BP Q0 Q1 P0).
  set (qp1_R := cross_R_BP Q0 Q1 P1).
  set (den_R := Binary.B2R prec emax
                  (b64_minus (b64_orient2d Q0 Q1 P0)
                             (b64_orient2d Q0 Q1 P1))).
  set (s_R := Binary.B2R prec emax
                (b64_div (b64_orient2d Q0 Q1 P0)
                         (b64_minus (b64_orient2d Q0 Q1 P0)
                                    (b64_orient2d Q0 Q1 P1)))).
  replace (s_R - qp0_R / (qp0_R - qp1_R))
    with ((s_R - qp0_R / den_R) + (qp0_R / den_R - qp0_R / (qp0_R - qp1_R)))
    by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rplus_le_compat.
  - apply (b64_intersect_s_round_error _ _ _ _ Hsafe).
  - apply (b64_intersect_s_carry_error _ _ _ _ Hsafe).
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-tight Session 4 -- layer 3 (s * dx) forward error.               *)
(*                                                                            *)
(* Layer 3 of the b64 intersection chain:                                     *)
(*    B2R(b64_mult s dx) = b64_round (B2R(s) * B2R(dx))                       *)
(*                       = b64_round (s_R * dx_R)                              *)
(* where dx_R = B2R(b64_minus (bx P1) (bx P0)) = B2R(bx P1) - B2R(bx P0)      *)
(* (bit-exact under int-safe via `b64_intersect_dx_R`).                       *)
(*                                                                            *)
(* Reference: intersect_param_s * (px P1 - px P0) = s_exact * dx_R            *)
(*    (since px (BP2P P) = B2R(bx P), the same dx_R appears on both sides).   *)
(*                                                                            *)
(* The forward error decomposes:                                              *)
(*    b64_round(s_R * dx_R) - s_exact * dx_R                                  *)
(*  = [b64_round(s_R * dx_R) - s_R * dx_R]              [Delta_round_mul]     *)
(*  + dx_R * (s_R - s_exact)                            [Delta_carry_mul]     *)
(*                                                                            *)
(* Delta_round_mul: half-ulp at magnitude <= bpow 80, so <= bpow 27.          *)
(* Delta_carry_mul: |dx_R| <= bpow 26; Session 3's s_forward_error bound      *)
(*    folds in to give bpow 26 + bpow 80 / |den_exact|.                       *)
(*                                                                            *)
(* Combined: bpow 27 + bpow 26 + bpow 80 / |den_exact|                        *)
(*         <= bpow 28 + bpow 80 / |den_exact|.                                 *)
(* -------------------------------------------------------------------------- *)

(* Delta_round_mul: b64_round error on the layer-3 multiplication. *)
Lemma b64_intersect_mult_x_round_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dx)
          - Binary.B2R prec emax s * Binary.B2R prec emax dx)
    <= bpow radix2 27.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_x_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_error_le_half_ulp_round
                (Binary.B2R prec emax
                   (b64_div (b64_orient2d Q0 Q1 P0)
                            (b64_minus (b64_orient2d Q0 Q1 P0)
                                       (b64_orient2d Q0 Q1 P1)))
                 * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))) as Herr.
  eapply Rle_trans; [exact Herr|].
  assert (Hbnd : Rabs (b64_round
                        (Binary.B2R prec emax
                          (b64_div (b64_orient2d Q0 Q1 P0)
                                   (b64_minus (b64_orient2d Q0 Q1 P0)
                                              (b64_orient2d Q0 Q1 P1)))
                         * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
                 <= bpow radix2 80).
  { pose proof (b64_intersect_mult_x_abs_le_bpow_80 _ _ _ _ Hsafe) as Bm.
    cbv zeta in Bm.
    rewrite HB2R in Bm. exact Bm. }
  pose proof (b64_ulp_le_at_magnitude_uniform _ 80 ltac:(lia) Hbnd) as Hulp.
  apply Rle_trans with (bpow radix2 (80 - prec + 1) / 2);
    [|unfold prec; simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra|exact Hulp].
Qed.

(* Delta_carry_mul: the s-error carried through dx. *)
Lemma b64_intersect_mult_x_carry_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax s * Binary.B2R prec emax dx
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dx)
    <= bpow radix2 26
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  replace (Binary.B2R prec emax
             (b64_div (b64_orient2d Q0 Q1 P0)
                      (b64_minus (b64_orient2d Q0 Q1 P0)
                                 (b64_orient2d Q0 Q1 P1)))
           * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
    with (Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
          * (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
    by ring.
  rewrite Rabs_mult.
  pose proof (b64_intersect_dx_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdx.
  pose proof (b64_intersect_s_forward_error _ _ _ _ Hsafe) as Bs.
  apply Rle_trans
    with (bpow radix2 26
          * (1 + bpow radix2 54
                 / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Bdx|exact Bs].
  - rewrite Rmult_plus_distr_l, Rmult_1_r.
    apply Rplus_le_compat_l.
    unfold Rdiv.
    rewrite <- Rmult_assoc.
    rewrite <- bpow_plus.
    replace (26 + 54)%Z with 80%Z by lia.
    apply Rle_refl.
Qed.

(* Layer 3 full forward error: composition of Delta_round_mul and             *)
(* Delta_carry_mul, vs the exact reference s_exact * (B2R(bx P1) - B2R(bx P0)).*)
Theorem b64_intersect_mult_x_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dx)
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dx)
    <= bpow radix2 27 + bpow radix2 26
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_x_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_x_carry_error _ _ _ _ Hsafe) as Hcarry.
  cbv zeta in Hcarry.
  replace (Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (bx P1) (bx P0)))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
    with ((Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (bx P1) (bx P0)))
           - Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))
          + (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (bx P1) (bx P0)))) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rplus_assoc.
  apply Rplus_le_compat; [exact Hround | exact Hcarry].
Qed.

(* -------------------------------------------------------------------------- *)
(* Scope C.2-tight Session 5 -- layer 4 (final coordinate) + headline.        *)
(*                                                                            *)
(* Layer 4 of the b64 intersection chain:                                     *)
(*    B2R(b64_intersect_point_x) = b64_round (B2R(bx P0) + B2R(b64_mult s dx)) *)
(*                                                                            *)
(* Reference (the "exact x-coordinate of the intersection point" under        *)
(* int-safe inputs, where px(BP2P P) = B2R(bx P)):                            *)
(*    x_exact := B2R(bx P0) + s_exact * dx_R                                  *)
(* where dx_R = B2R(b64_minus (bx P1) (bx P0)) = B2R(bx P1) - B2R(bx P0).     *)
(*                                                                            *)
(* This equals `intersect_x_R (BP2P P0) ... (BP2P Q1)` up to the bit-exact    *)
(* dx step (Session 6 will link).                                              *)
(*                                                                            *)
(* Decomposition:                                                              *)
(*    B2R(b64_intersect_point_x) - x_exact                                    *)
(*  = b64_round(B2R(bx P0) + mul_R) - (B2R(bx P0) + s_exact * dx_R)           *)
(*  = [b64_round(...) - (B2R(bx P0) + mul_R)]         [Delta_round_plus]      *)
(*  + [mul_R - s_exact * dx_R]                         [Delta_layer3]          *)
(*                                                                            *)
(* Delta_round_plus: half-ulp at magnitude <= bpow 81, so <= bpow 28.         *)
(* Delta_layer3: <= bpow 27 + bpow 26 + bpow 80 / |den_exact|  (Session 4)    *)
(*                                                                            *)
(* Combined: bpow 28 + bpow 27 + bpow 26 + bpow 80 / |den_exact|              *)
(*         <= bpow 29 + bpow 80 / |den_exact|.                                 *)
(*                                                                            *)
(* In K * eps form (eps = bpow(-53)):                                          *)
(*    K(|den_exact|) = bpow 82 + bpow 133 / |den_exact|                       *)
(* deferred to Session 6 (the K * eps restatement + HasIntersect_sound).     *)
(* -------------------------------------------------------------------------- *)

(* Delta_round_plus: b64_round error on the final addition. *)
Lemma b64_intersect_plus_x_round_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dx  := b64_minus (bx P1) (bx P0) in
    Rabs (Binary.B2R prec emax (b64_plus (bx P0) (b64_mult s dx))
          - (Binary.B2R prec emax (bx P0)
             + Binary.B2R prec emax (b64_mult s dx)))
    <= bpow radix2 28.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_plus_x_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_error_le_half_ulp_round
                (Binary.B2R prec emax (bx P0)
                 + Binary.B2R prec emax
                     (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                                   (b64_orient2d Q0 Q1 P1)))
                               (b64_minus (bx P1) (bx P0))))) as Herr.
  eapply Rle_trans; [exact Herr|].
  assert (Hbnd : Rabs (b64_round
                        (Binary.B2R prec emax (bx P0)
                         + Binary.B2R prec emax
                             (b64_mult
                                (b64_div (b64_orient2d Q0 Q1 P0)
                                         (b64_minus (b64_orient2d Q0 Q1 P0)
                                                    (b64_orient2d Q0 Q1 P1)))
                                (b64_minus (bx P1) (bx P0)))))
                 <= bpow radix2 81).
  { pose proof (b64_intersect_point_x_abs_le_bpow_81 _ _ _ _ Hsafe) as Bp.
    unfold b64_intersect_point_x in Bp.
    cbv zeta in Bp.
    rewrite HB2R in Bp. exact Bp. }
  pose proof (b64_ulp_le_at_magnitude_uniform _ 81 ltac:(lia) Hbnd) as Hulp.
  apply Rle_trans with (bpow radix2 (81 - prec + 1) / 2);
    [|unfold prec; simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra|exact Hulp].
Qed.

(* Layer 4 + composition: the headline forward error against the exact       *)
(* reference x_exact = B2R(bx P0) + s_exact * dx_R.                           *)
Theorem b64_intersect_point_x_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1)
          - (Binary.B2R prec emax (bx P0)
             + cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
    <= bpow radix2 29
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_x.
  cbv zeta.
  pose proof (b64_intersect_plus_x_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_x_forward_error _ _ _ _ Hsafe) as Hlayer3.
  cbv zeta in Hlayer3.
  (* Decomposition: result - x_exact = Δ_round_plus + Δ_layer3. *)
  replace (Binary.B2R prec emax
             (b64_plus (bx P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (bx P1) (bx P0))))
           - (Binary.B2R prec emax (bx P0)
              + cross_R_BP Q0 Q1 P0
                / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
                * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
    with ((Binary.B2R prec emax
             (b64_plus (bx P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (bx P1) (bx P0))))
           - (Binary.B2R prec emax (bx P0)
              + Binary.B2R prec emax
                  (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                                (b64_orient2d Q0 Q1 P1)))
                            (b64_minus (bx P1) (bx P0)))))
          + (Binary.B2R prec emax
               (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                  (b64_minus (b64_orient2d Q0 Q1 P0)
                                             (b64_orient2d Q0 Q1 P1)))
                         (b64_minus (bx P1) (bx P0)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
    by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  (* RHS: bpow 29 + bpow 80 / |...| = bpow 28 + (bpow 28 + bpow 80 / |...|). *)
  apply Rle_trans
    with (bpow radix2 28
          + (bpow radix2 27 + bpow radix2 26
             + bpow radix2 80
               / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rplus_le_compat; [exact Hround | exact Hlayer3].
  - (* bpow 28 + bpow 27 + bpow 26 <= bpow 29 *)
    replace (bpow radix2 28
             + (bpow radix2 27 + bpow radix2 26
                + bpow radix2 80
                  / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
      with ((bpow radix2 28 + bpow radix2 27 + bpow radix2 26)
            + bpow radix2 80
              / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
      by ring.
    apply Rplus_le_compat_r.
    simpl; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Y-coordinate mirror of the Scope C.2-tight cascade.                        *)
(*                                                                            *)
(* Layers 1 (den) and 2 (s) are shared with the x cascade -- the denominator *)
(* and Cramer parameter don't depend on whether we're evaluating x or y.     *)
(* Layers 3 (s * dy) and 4 (B2R(by_ P0) + s * dy) mirror the x layers with   *)
(* by_ substituted for bx, reusing the existing _y_safe / _y_abs_le_bpow_*   *)
(* lemmas.                                                                    *)
(* -------------------------------------------------------------------------- *)

(* Delta_round_mul, y: b64_round error on the layer-3 multiplication. *)
Lemma b64_intersect_mult_y_round_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dy)
          - Binary.B2R prec emax s * Binary.B2R prec emax dy)
    <= bpow radix2 27.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_y_safe _ _ _ _ Hsafe) as Hms.
  cbv zeta in Hms.
  pose proof (b64_mult_correct _ _ Hms) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_error_le_half_ulp_round
                (Binary.B2R prec emax
                   (b64_div (b64_orient2d Q0 Q1 P0)
                            (b64_minus (b64_orient2d Q0 Q1 P0)
                                       (b64_orient2d Q0 Q1 P1)))
                 * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))) as Herr.
  eapply Rle_trans; [exact Herr|].
  assert (Hbnd : Rabs (b64_round
                        (Binary.B2R prec emax
                          (b64_div (b64_orient2d Q0 Q1 P0)
                                   (b64_minus (b64_orient2d Q0 Q1 P0)
                                              (b64_orient2d Q0 Q1 P1)))
                         * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
                 <= bpow radix2 80).
  { pose proof (b64_intersect_mult_y_abs_le_bpow_80 _ _ _ _ Hsafe) as Bm.
    cbv zeta in Bm.
    rewrite HB2R in Bm. exact Bm. }
  pose proof (b64_ulp_le_at_magnitude_uniform _ 80 ltac:(lia) Hbnd) as Hulp.
  apply Rle_trans with (bpow radix2 (80 - prec + 1) / 2);
    [|unfold prec; simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra|exact Hulp].
Qed.

(* Delta_carry_mul, y: the s-error carried through dy. *)
Lemma b64_intersect_mult_y_carry_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax s * Binary.B2R prec emax dy
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dy)
    <= bpow radix2 26
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  replace (Binary.B2R prec emax
             (b64_div (b64_orient2d Q0 Q1 P0)
                      (b64_minus (b64_orient2d Q0 Q1 P0)
                                 (b64_orient2d Q0 Q1 P1)))
           * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
    with (Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
          * (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
    by ring.
  rewrite Rabs_mult.
  pose proof (b64_intersect_dy_abs_le_bpow_26 _ _ _ _ Hsafe) as Bdy.
  pose proof (b64_intersect_s_forward_error _ _ _ _ Hsafe) as Bs.
  apply Rle_trans
    with (bpow radix2 26
          * (1 + bpow radix2 54
                 / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Bdy|exact Bs].
  - rewrite Rmult_plus_distr_l, Rmult_1_r.
    apply Rplus_le_compat_l.
    unfold Rdiv.
    rewrite <- Rmult_assoc.
    rewrite <- bpow_plus.
    replace (26 + 54)%Z with 80%Z by lia.
    apply Rle_refl.
Qed.

(* Layer 3 full forward error, y. *)
Theorem b64_intersect_mult_y_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax (b64_mult s dy)
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
            * Binary.B2R prec emax dy)
    <= bpow radix2 27 + bpow radix2 26
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_y_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_y_carry_error _ _ _ _ Hsafe) as Hcarry.
  cbv zeta in Hcarry.
  replace (Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (by_ P1) (by_ P0)))
           - cross_R_BP Q0 Q1 P0
             / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
    with ((Binary.B2R prec emax
             (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                (b64_minus (b64_orient2d Q0 Q1 P0)
                                           (b64_orient2d Q0 Q1 P1)))
                       (b64_minus (by_ P1) (by_ P0)))
           - Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))
          + (Binary.B2R prec emax
               (b64_div (b64_orient2d Q0 Q1 P0)
                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                   (b64_orient2d Q0 Q1 P1)))
             * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0)))) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rplus_assoc.
  apply Rplus_le_compat; [exact Hround | exact Hcarry].
Qed.

(* Delta_round_plus, y: b64_round error on the final addition. *)
Lemma b64_intersect_plus_y_round_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    let qp0 := b64_orient2d Q0 Q1 P0 in
    let qp1 := b64_orient2d Q0 Q1 P1 in
    let den := b64_minus qp0 qp1 in
    let s   := b64_div qp0 den in
    let dy  := b64_minus (by_ P1) (by_ P0) in
    Rabs (Binary.B2R prec emax (b64_plus (by_ P0) (b64_mult s dy))
          - (Binary.B2R prec emax (by_ P0)
             + Binary.B2R prec emax (b64_mult s dy)))
    <= bpow radix2 28.
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_plus_y_safe _ _ _ _ Hsafe) as Hps.
  cbv zeta in Hps.
  pose proof (b64_plus_correct _ _ Hps) as [HB2R _].
  rewrite HB2R.
  pose proof (b64_error_le_half_ulp_round
                (Binary.B2R prec emax (by_ P0)
                 + Binary.B2R prec emax
                     (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                        (b64_minus (b64_orient2d Q0 Q1 P0)
                                                   (b64_orient2d Q0 Q1 P1)))
                               (b64_minus (by_ P1) (by_ P0))))) as Herr.
  eapply Rle_trans; [exact Herr|].
  assert (Hbnd : Rabs (b64_round
                        (Binary.B2R prec emax (by_ P0)
                         + Binary.B2R prec emax
                             (b64_mult
                                (b64_div (b64_orient2d Q0 Q1 P0)
                                         (b64_minus (b64_orient2d Q0 Q1 P0)
                                                    (b64_orient2d Q0 Q1 P1)))
                                (b64_minus (by_ P1) (by_ P0)))))
                 <= bpow radix2 81).
  { pose proof (b64_intersect_point_y_abs_le_bpow_81 _ _ _ _ Hsafe) as Bp.
    unfold b64_intersect_point_y in Bp.
    cbv zeta in Bp.
    rewrite HB2R in Bp. exact Bp. }
  pose proof (b64_ulp_le_at_magnitude_uniform _ 81 ltac:(lia) Hbnd) as Hulp.
  apply Rle_trans with (bpow radix2 (81 - prec + 1) / 2);
    [|unfold prec; simpl; lra].
  unfold Rdiv.
  apply Rmult_le_compat_r; [lra|exact Hulp].
Qed.

(* Headline forward-error theorem, y coordinate. *)
Theorem b64_intersect_point_y_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1)
          - (Binary.B2R prec emax (by_ P0)
             + cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
    <= bpow radix2 29
       + bpow radix2 80
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_y.
  cbv zeta.
  pose proof (b64_intersect_plus_y_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_y_forward_error _ _ _ _ Hsafe) as Hlayer3.
  cbv zeta in Hlayer3.
  replace (Binary.B2R prec emax
             (b64_plus (by_ P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (by_ P1) (by_ P0))))
           - (Binary.B2R prec emax (by_ P0)
              + cross_R_BP Q0 Q1 P0
                / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
                * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
    with ((Binary.B2R prec emax
             (b64_plus (by_ P0)
                       (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                          (b64_minus (b64_orient2d Q0 Q1 P0)
                                                     (b64_orient2d Q0 Q1 P1)))
                                 (b64_minus (by_ P1) (by_ P0))))
           - (Binary.B2R prec emax (by_ P0)
              + Binary.B2R prec emax
                  (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                                (b64_orient2d Q0 Q1 P1)))
                            (b64_minus (by_ P1) (by_ P0)))))
          + (Binary.B2R prec emax
               (b64_mult (b64_div (b64_orient2d Q0 Q1 P0)
                                  (b64_minus (b64_orient2d Q0 Q1 P0)
                                             (b64_orient2d Q0 Q1 P1)))
                         (b64_minus (by_ P1) (by_ P0)))
             - cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
    by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  apply Rle_trans
    with (bpow radix2 28
          + (bpow radix2 27 + bpow radix2 26
             + bpow radix2 80
               / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rplus_le_compat; [exact Hround | exact Hlayer3].
  - replace (bpow radix2 28
             + (bpow radix2 27 + bpow radix2 26
                + bpow radix2 80
                  / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
      with ((bpow radix2 28 + bpow radix2 27 + bpow radix2 26)
            + bpow radix2 80
              / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
      by ring.
    apply Rplus_le_compat_r.
    simpl; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_intersect_den_forward_error.
Print Assumptions b64_intersect_s_carry_error.
Print Assumptions b64_intersect_s_round_error.
Print Assumptions b64_intersect_s_forward_error.
Print Assumptions b64_ulp_le_at_magnitude_uniform.
Print Assumptions b64_intersect_mult_x_round_error.
Print Assumptions b64_intersect_mult_x_carry_error.
Print Assumptions b64_intersect_mult_x_forward_error.
Print Assumptions b64_intersect_plus_x_round_error.
Print Assumptions b64_intersect_point_x_forward_error.
Print Assumptions b64_intersect_mult_y_round_error.
Print Assumptions b64_intersect_mult_y_carry_error.
Print Assumptions b64_intersect_mult_y_forward_error.
Print Assumptions b64_intersect_plus_y_round_error.
Print Assumptions b64_intersect_point_y_forward_error.
Print Assumptions b64_intersect_den_error_le_1.
