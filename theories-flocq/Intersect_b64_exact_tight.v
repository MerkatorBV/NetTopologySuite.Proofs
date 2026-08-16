(* ============================================================================
   NetTopologySuite.Proofs.Flocq.Intersect_b64_exact_tight
   ----------------------------------------------------------------------------
   PARALLEL TIGHT CHAIN (Scope C.2-tight alternative): Layers 2-4 + the
   reference bridge, re-derived with the foundation
   `b64_intersect_den_error_le_1` (|den error| <= 1) in place of the
   Session-1 `<= bpow 1` bound, halving the condition-number-dependent
   term at every layer:

     Layer 2:  <= 1 + bpow 53 / |qp0_R - qp1_R|      (was bpow 54)
     Layer 3:  <= bpow 27 + bpow 26 + bpow 79 / |.|  (was bpow 80)
     Layer 4:  <= bpow 29 + bpow 79 / |.|            (was bpow 80)

   The constant term bpow 29 is unchanged -- it carries the round-to-
   nearest half-ulps, not the denominator carry.  Round-error lemmas are
   shared with the primary chain; only the carry lemmas fork.

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
From NTS.Proofs.Flocq  Require Import Intersect_b64_exact_forward_error.
From NTS.Proofs.Flocq  Require Import Intersect_b64_exact_bridge.

Local Open Scope R_scope.

(* ============================================================================
   Parallel tight chain (Scope C.2-tight alternative).
   ----------------------------------------------------------------------------
   The chain above (Layers 1-4 + reference bridge) uses
   `b64_intersect_den_forward_error`'s loose `<= bpow 1 = 2` Step 1 bound.
   The lemmas below mirror Layers 2-4 + the reference bridge with the
   tight `b64_intersect_den_error_le_1` (`<= 1`) substituted at the
   Step 1 cite site.  The tightening propagates through the `bpow 53 * |e1|`
   carryover terms in Layers 2-3 and the final additive composition in
   Layer 4, yielding a 2x reduction in the condition-number-dependent term
   of the K_intersect bound:

       Loose:  K_intersect = bpow 29 + bpow 80 / |den_R|
       Tight:  K_intersect = bpow 29 + bpow 79 / |den_R|.

   The constant term `bpow 29` is unchanged -- it carries the round-to-
   nearest errors of the inner mult and plus steps, which are independent
   of the Step 1 bound.  Only the carryover term (the dominant one when
   `|den_R|` is well-separated from zero is small) tightens.

   Each tight theorem cites the foundation `b64_intersect_den_error_le_1`
   exactly once -- Layer 2 carry.  Downstream tight theorems compose
   inductively through `_s_forward_error_tight` and the y-mirror.

   Round-error lemmas (`_s_round_error`, `_mult_x/y_round_error`,
   `_plus_x/y_round_error`) are reused from main's chain unchanged --
   they don't depend on the Step 1 bound.
   ============================================================================ *)

(* Layer 2 tight: Delta_carry with the tight Step 1 bound. *)
Theorem b64_intersect_s_carry_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (cross_R_BP Q0 Q1 P0
            / Binary.B2R prec emax
                (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= bpow radix2 53
       / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  set (qp0_R := cross_R_BP Q0 Q1 P0).
  set (qp1_R := cross_R_BP Q0 Q1 P1).
  set (den_R := Binary.B2R prec emax
                  (b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))).
  set (den_exact := qp0_R - qp1_R).
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
  (* Tight substitution: use _le_1 instead of _forward_error for the Step 1 cite. *)
  assert (Hden_err : Rabs (den_R - den_exact) <= 1).
  { unfold den_R, den_exact, qp0_R, qp1_R.
    apply (b64_intersect_den_error_le_1 _ _ _ _ Hsafe). }
  assert (Hpos_R : 0 < Rabs den_R) by (apply Rabs_pos_lt; exact Hden_R_ne).
  assert (Hpos_exact : 0 < Rabs den_exact)
    by (apply Rabs_pos_lt; exact Hden_exact_ne).
  replace (qp0_R / den_R - qp0_R / den_exact)
    with (qp0_R * (den_exact - den_R) / (den_R * den_exact))
    by (field; split; assumption).
  unfold Rdiv at 1.
  rewrite Rabs_mult.
  rewrite Rabs_inv.
  rewrite (Rabs_mult qp0_R (den_exact - den_R)).
  rewrite (Rabs_mult den_R den_exact).
  apply Rle_trans
    with ((bpow radix2 53 * 1) / (1 * Rabs den_exact)).
  - apply Rmult_le_compat;
      [ apply Rmult_le_pos; apply Rabs_pos
      | apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; assumption
      |
      | ].
    + apply Rmult_le_compat;
        [apply Rabs_pos|apply Rabs_pos|exact Hqp0_R_bnd|].
      replace (Rabs (den_exact - den_R)) with (Rabs (den_R - den_exact))
        by (rewrite <- Rabs_Ropp; f_equal; ring).
      exact Hden_err.
    + apply Rinv_le_contravar.
      * rewrite Rmult_1_l. exact Hpos_exact.
      * apply Rmult_le_compat_r; [apply Rlt_le; exact Hpos_exact|exact Hden_R_ge1].
  - rewrite Rmult_1_l, Rmult_1_r. apply Rle_refl.
Qed.

(* Layer 2 tight full forward-error: composition of Delta_round (unchanged)
   with the tight Delta_carry above. *)
Theorem b64_intersect_s_forward_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax
            (b64_div (b64_orient2d Q0 Q1 P0)
                     (b64_minus (b64_orient2d Q0 Q1 P0)
                                (b64_orient2d Q0 Q1 P1)))
          - cross_R_BP Q0 Q1 P0
            / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= 1 + bpow radix2 53
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
  - apply (b64_intersect_s_carry_error_tight _ _ _ _ Hsafe).
Qed.

(* Layer 3 tight x: Delta_carry_mul with the tight layer-2 forward error. *)
Lemma b64_intersect_mult_x_carry_error_tight :
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
       + bpow radix2 79
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
  pose proof (b64_intersect_s_forward_error_tight _ _ _ _ Hsafe) as Bs.
  apply Rle_trans
    with (bpow radix2 26
          * (1 + bpow radix2 53
                 / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Bdx|exact Bs].
  - rewrite Rmult_plus_distr_l, Rmult_1_r.
    apply Rplus_le_compat_l.
    unfold Rdiv.
    rewrite <- Rmult_assoc.
    rewrite <- bpow_plus.
    replace (26 + 53)%Z with 79%Z by lia.
    apply Rle_refl.
Qed.

(* Layer 3 tight x forward error: composition of mult_x_round_error (unchanged)
   with the tight Delta_carry_mul. *)
Theorem b64_intersect_mult_x_forward_error_tight :
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
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_x_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_x_carry_error_tight _ _ _ _ Hsafe) as Hcarry.
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

(* Layer 3 tight y: same shape as x with by_ substituted. *)
Lemma b64_intersect_mult_y_carry_error_tight :
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
       + bpow radix2 79
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
  pose proof (b64_intersect_s_forward_error_tight _ _ _ _ Hsafe) as Bs.
  apply Rle_trans
    with (bpow radix2 26
          * (1 + bpow radix2 53
                 / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rmult_le_compat; [apply Rabs_pos|apply Rabs_pos|exact Bdy|exact Bs].
  - rewrite Rmult_plus_distr_l, Rmult_1_r.
    apply Rplus_le_compat_l.
    unfold Rdiv.
    rewrite <- Rmult_assoc.
    rewrite <- bpow_plus.
    replace (26 + 53)%Z with 79%Z by lia.
    apply Rle_refl.
Qed.

Theorem b64_intersect_mult_y_forward_error_tight :
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
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  cbv zeta.
  pose proof (b64_intersect_mult_y_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_y_carry_error_tight _ _ _ _ Hsafe) as Hcarry.
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

(* Layer 4 tight x: composition of plus_x_round_error (unchanged) with the
   tight Layer 3 x forward error. *)
Theorem b64_intersect_point_x_forward_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1)
          - (Binary.B2R prec emax (bx P0)
             + cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (bx P1) (bx P0))))
    <= bpow radix2 29
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_x.
  cbv zeta.
  pose proof (b64_intersect_plus_x_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_x_forward_error_tight _ _ _ _ Hsafe) as Hlayer3.
  cbv zeta in Hlayer3.
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
  apply Rle_trans
    with (bpow radix2 28
          + (bpow radix2 27 + bpow radix2 26
             + bpow radix2 79
               / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rplus_le_compat; [exact Hround | exact Hlayer3].
  - replace (bpow radix2 28
             + (bpow radix2 27 + bpow radix2 26
                + bpow radix2 79
                  / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
      with ((bpow radix2 28 + bpow radix2 27 + bpow radix2 26)
            + bpow radix2 79
              / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
      by ring.
    apply Rplus_le_compat_r.
    simpl; lra.
Qed.

(* Layer 4 tight y: mirror of x with by_ substituted. *)
Theorem b64_intersect_point_y_forward_error_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1)
          - (Binary.B2R prec emax (by_ P0)
             + cross_R_BP Q0 Q1 P0
               / (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)
               * Binary.B2R prec emax (b64_minus (by_ P1) (by_ P0))))
    <= bpow radix2 29
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  unfold b64_intersect_point_y.
  cbv zeta.
  pose proof (b64_intersect_plus_y_round_error _ _ _ _ Hsafe) as Hround.
  cbv zeta in Hround.
  pose proof (b64_intersect_mult_y_forward_error_tight _ _ _ _ Hsafe) as Hlayer3.
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
             + bpow radix2 79
               / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))).
  - apply Rplus_le_compat; [exact Hround | exact Hlayer3].
  - replace (bpow radix2 28
             + (bpow radix2 27 + bpow radix2 26
                + bpow radix2 79
                  / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1)))
      with ((bpow radix2 28 + bpow radix2 27 + bpow radix2 26)
            + bpow radix2 79
              / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
      by ring.
    apply Rplus_le_compat_r.
    simpl; lra.
Qed.

(* Reference-bridge restatements against the canonical intersect_x_R /
   intersect_y_R references.  Reuses main's c2tight_ref_x/y_eq_intersect_x/y_R
   bridge lemmas (which don't depend on the Step 1 bound). *)
Theorem b64_intersect_point_x_forward_error_vs_intersect_x_R_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_x P0 P1 Q0 Q1)
          - intersect_x_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1))
    <= bpow radix2 29
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  rewrite <- (c2tight_ref_x_eq_intersect_x_R _ _ _ _ Hsafe).
  apply (b64_intersect_point_x_forward_error_tight _ _ _ _ Hsafe).
Qed.

Theorem b64_intersect_point_y_forward_error_vs_intersect_y_R_tight :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (Binary.B2R prec emax (b64_intersect_point_y P0 P1 Q0 Q1)
          - intersect_y_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1))
    <= bpow radix2 29
       + bpow radix2 79
         / Rabs (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1).
Proof.
  intros P0 P1 Q0 Q1 Hsafe.
  rewrite <- (c2tight_ref_y_eq_intersect_y_R _ _ _ _ Hsafe).
  apply (b64_intersect_point_y_forward_error_tight _ _ _ _ Hsafe).
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions b64_intersect_s_carry_error_tight.
Print Assumptions b64_intersect_s_forward_error_tight.
Print Assumptions b64_intersect_mult_x_carry_error_tight.
Print Assumptions b64_intersect_mult_x_forward_error_tight.
Print Assumptions b64_intersect_mult_y_carry_error_tight.
Print Assumptions b64_intersect_mult_y_forward_error_tight.
Print Assumptions b64_intersect_point_x_forward_error_tight.
Print Assumptions b64_intersect_point_y_forward_error_tight.
Print Assumptions b64_intersect_point_x_forward_error_vs_intersect_x_R_tight.
Print Assumptions b64_intersect_point_y_forward_error_vs_intersect_y_R_tight.
