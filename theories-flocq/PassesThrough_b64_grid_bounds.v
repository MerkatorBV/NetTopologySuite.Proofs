(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_grid_bounds
   ----------------------------------------------------------------------------
   SLICES 6-8: the division bridge and the correctly-rounded t-bounds.

   Slices 6-8: the division bridge (the LAST exactness layer before the
   core -- b64_div rounds exactly once past exact operands); the t-bounds
   are the CORRECTLY-ROUNDED exact t-bounds on the grid; the clipped
   tmin/tmax are the correctly-rounded exact ones.

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

(* ----------------------------------------------------------------------------
   SLICE 6: the division bridge -- the LAST exactness layer before the core.

   The t-bounds are the only place `b64_div` (which ROUNDS) enters.  This slice
   discharges the division's `b64_div_correct` preconditions on the grid and
   rewrites each per-axis compute t-bound as the spec t-bound with each exact
   quotient INDIVIDUALLY ROUNDED:

       b64_lb_tlo c0 c1 (cc-1/2) (cc+1/2)
         = Rmin (round ((lo - c0)/(c1 - c0))) (round ((hi - c0)/(c1 - c0)))   (Qed)

   (and the Rmax analogue for b64_lb_thi).  Combined with Slices 4-5 (operand
   exactness + max/min bridge), the rounded compute filter now differs from the
   exact spec ONLY by the `round` wrapped around each individual quotient: the
   division is the single, fully-localised residual.  No division-safety obligation
   remains open -- it is discharged here (|num/den| <= |num| <= 2^27 on the grid).
   ---------------------------------------------------------------------------- *)

(* One quotient.  A half-integer numerator over a NONZERO INTEGER denominator
   divides bit-correctly to the rounded exact quotient.  The `b64_div_correct`
   safety bound is discharged from the grid magnitudes: |num/den| <= |num|
   (since |den| >= 1) <= 2^27 < 2^emax. *)
Lemma b64_div_round_half_over_int :
  forall (num den : binary64) (a d : Z),
    Binary.is_finite prec emax num = true ->
    Binary.is_finite prec emax den = true ->
    Binary.B2R prec emax num = (IZR a / 2)%R ->
    Binary.B2R prec emax den = IZR d ->
    (d <> 0)%Z ->
    (Z.abs a < 2 ^ 28)%Z ->
    Binary.B2R prec emax (b64_div num den)
      = b64_round (Binary.B2R prec emax num / Binary.B2R prec emax den)
    /\ Binary.is_finite prec emax (b64_div num den) = true.
Proof.
  intros num den a d Fnum Fden HnumR HdenR Hd Ha.
  assert (Hden_ne : Binary.B2R prec emax den <> 0%R).
  { rewrite HdenR. apply IZR_neq. exact Hd. }
  (* |den| = IZR |d| >= 1 *)
  assert (Hden_ge1 : (1 <= Rabs (Binary.B2R prec emax den))%R).
  { rewrite HdenR, <- abs_IZR.
    replace 1%R with (IZR 1) by (simpl; reflexivity).
    apply IZR_le. lia. }
  (* |num| = IZR |a| / 2 <= bpow 27 *)
  assert (Hnum_le : (Rabs (Binary.B2R prec emax num) <= bpow radix2 28)%R).
  { rewrite HnumR. unfold Rdiv. rewrite Rabs_mult, (Rabs_right (/ 2)%R) by lra.
    rewrite <- abs_IZR.
    assert (Ha28 : (IZR (Z.abs a) < bpow radix2 28)%R).
    { rewrite <- (IZR_Zpower radix2 28) by lia. apply IZR_lt. exact Ha. }
    pose proof (bpow_gt_0 radix2 28). lra. }
  assert (Hbnd : (Rabs (b64_round (Binary.B2R prec emax num
                                    / Binary.B2R prec emax den))
                   < bpow radix2 emax)%R).
  { apply (Rle_lt_trans _ (bpow radix2 28)).
    - apply b64_round_abs_le_bpow; [ unfold emax; lia | ].
      (* Rabs (num/den) = Rabs num / Rabs den <= Rabs num <= bpow 27 *)
      unfold Rdiv. rewrite Rabs_mult, Rabs_inv.
      apply (Rle_trans _ (Rabs (Binary.B2R prec emax num))); [ | exact Hnum_le ].
      rewrite <- (Rmult_1_r (Rabs (Binary.B2R prec emax num))) at 2.
      apply Rmult_le_compat_l; [ apply Rabs_pos | ].
      rewrite <- Rinv_1.
      apply Rinv_le_contravar; [ lra | exact Hden_ge1 ].
    - apply bpow_lt. unfold emax; lia. }
  exact (b64_div_correct num den Fnum Fden Hden_ne Hbnd).
Qed.

(* Operand facts for one (edge, endpoint) pair on the integer grid: the
   numerator `edge - c0` is a half-integer with mantissa < 2^27, computed
   bit-exactly. *)
Lemma grid_numerator_facts :
  forall (edge c0 : binary64) (m n0 : Z),
    Binary.is_finite prec emax edge = true ->
    Binary.is_finite prec emax c0 = true ->
    Binary.B2R prec emax edge = (IZR m / 2)%R ->
    Binary.B2R prec emax c0 = IZR n0 ->
    (Z.abs m < 2 ^ 27)%Z ->
    (Z.abs n0 <= 2 ^ 25)%Z ->
    Binary.B2R prec emax (b64_minus edge c0)
      = (IZR (m - 2 * n0)%Z / 2)%R
    /\ Binary.is_finite prec emax (b64_minus edge c0) = true
    /\ (Z.abs (m - 2 * n0) < 2 ^ 28)%Z
    /\ Binary.B2R prec emax (b64_minus edge c0)
         = (Binary.B2R prec emax edge - Binary.B2R prec emax c0)%R.
Proof.
  intros edge c0 m n0 Fe F0 HeR H0R Hm Hn0.
  assert (H0half : Binary.B2R prec emax c0 = (IZR (2 * n0)%Z / 2)%R).
  { rewrite H0R, mult_IZR. lra. }
  pose proof (b64_minus_half_exact edge c0 m (2 * n0)%Z Fe F0 HeR H0half
                ltac:(unfold prec; lia)) as [HsubR Hsubfin].
  repeat split.
  - rewrite HsubR, HeR, H0half. rewrite minus_IZR, mult_IZR. lra.
  - exact Hsubfin.
  - lia.
  - exact HsubR.
Qed.

(* tlo (lower) per-axis bridge: the compute lower t-bound on the grid is the
   Rmin of the two rounded exact quotients the spec uses. *)
Theorem b64_lb_tlo_eq_rounded_quotients_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.B2R prec emax c1 <> Binary.B2R prec emax c0 ->
    Binary.B2R prec emax
        (b64_lb_tlo c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half))
      = Rmin
          (b64_round ((Binary.B2R prec emax (b64_minus cc b64_half)
                        - Binary.B2R prec emax c0)
                      / (Binary.B2R prec emax c1 - Binary.B2R prec emax c0)))
          (b64_round ((Binary.B2R prec emax (b64_plus cc b64_half)
                        - Binary.B2R prec emax c0)
                      / (Binary.B2R prec emax c1 - Binary.B2R prec emax c0))).
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc Hne.
  pose proof Hc0 as (Fc0 & n0 & H0R & H0b).
  pose proof Hc1 as (Fc1 & n1 & H1R & H1b).
  pose proof Hcc as (Fcc & ncc & HccR & Hccb).
  (* the two pixel edges and their exact half-integer images *)
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR Flo].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR Fhi].
  assert (HloHalf : Binary.B2R prec emax (b64_minus cc b64_half)
                    = (IZR (2 * ncc - 1)%Z / 2)%R).
  { rewrite HloR, HccR. rewrite minus_IZR, mult_IZR. lra. }
  assert (HhiHalf : Binary.B2R prec emax (b64_plus cc b64_half)
                    = (IZR (2 * ncc + 1)%Z / 2)%R).
  { rewrite HhiR, HccR. rewrite plus_IZR, mult_IZR. lra. }
  (* non-degenerate: b64_eqb c1 c0 = false *)
  assert (Heqb : b64_eqb c1 c0 = false).
  { destruct (b64_eqb c1 c0) eqn:E; [ | reflexivity ].
    apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0) in E. contradiction. }
  (* numerator facts *)
  pose proof (grid_numerator_facts (b64_minus cc b64_half) c0 (2*ncc-1) n0
                Flo Fc0 HloHalf H0R ltac:(lia) ltac:(lia))
    as (HnumLoR & HnumLoFin & HnumLoB & HnumLoDiff).
  pose proof (grid_numerator_facts (b64_plus cc b64_half) c0 (2*ncc+1) n0
                Fhi Fc0 HhiHalf H0R ltac:(lia) ltac:(lia))
    as (HnumHiR & HnumHiFin & HnumHiB & HnumHiDiff).
  (* denominator facts: c1 - c0 = IZR (n1 - n0) (and the difference form), nonzero *)
  assert (H1half : Binary.B2R prec emax c1 = (IZR (2 * n1)%Z / 2)%R)
    by (rewrite H1R, mult_IZR; lra).
  assert (H0half : Binary.B2R prec emax c0 = (IZR (2 * n0)%Z / 2)%R)
    by (rewrite H0R, mult_IZR; lra).
  pose proof (b64_minus_half_exact c1 c0 (2*n1) (2*n0) Fc1 Fc0 H1half H0half
                ltac:(unfold prec; lia)) as [HdenDiff HdenFin].
  assert (HdenRv : Binary.B2R prec emax (b64_minus c1 c0) = IZR (n1 - n0)%Z)
    by (rewrite HdenDiff, H1R, H0R, minus_IZR; lra).
  assert (Hdne : (n1 - n0 <> 0)%Z).
  { intro Hz. apply Hne. rewrite H1R, H0R. apply f_equal. lia. }
  (* divide each numerator by the denominator, bit-correctly *)
  pose proof (b64_div_round_half_over_int (b64_minus (b64_minus cc b64_half) c0)
                (b64_minus c1 c0) (2*ncc-1 - 2*n0) (n1 - n0)
                HnumLoFin HdenFin HnumLoR HdenRv Hdne ltac:(lia))
    as [HdivLoR HdivLoFin].
  pose proof (b64_div_round_half_over_int (b64_minus (b64_plus cc b64_half) c0)
                (b64_minus c1 c0) (2*ncc+1 - 2*n0) (n1 - n0)
                HnumHiFin HdenFin HnumHiR HdenRv Hdne ltac:(lia))
    as [HdivHiR HdivHiFin].
  (* assemble: b64_lb_tlo in the non-degenerate branch is b64_min of the divs *)
  unfold b64_lb_tlo. rewrite Heqb.
  rewrite (b64_min_B2R _ _ HdivLoFin HdivHiFin).
  rewrite HdivLoR, HdivHiR.
  rewrite HnumLoDiff, HnumHiDiff, HdenDiff.
  reflexivity.
Qed.

(* thi (upper) per-axis bridge: the compute upper t-bound on the grid is the
   Rmax of the two rounded exact quotients.  Same proof shape as tlo, with
   b64_max / Rmax. *)
Theorem b64_lb_thi_eq_rounded_quotients_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.B2R prec emax c1 <> Binary.B2R prec emax c0 ->
    Binary.B2R prec emax
        (b64_lb_thi c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half))
      = Rmax
          (b64_round ((Binary.B2R prec emax (b64_minus cc b64_half)
                        - Binary.B2R prec emax c0)
                      / (Binary.B2R prec emax c1 - Binary.B2R prec emax c0)))
          (b64_round ((Binary.B2R prec emax (b64_plus cc b64_half)
                        - Binary.B2R prec emax c0)
                      / (Binary.B2R prec emax c1 - Binary.B2R prec emax c0))).
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc Hne.
  pose proof Hc0 as (Fc0 & n0 & H0R & H0b).
  pose proof Hc1 as (Fc1 & n1 & H1R & H1b).
  pose proof Hcc as (Fcc & ncc & HccR & Hccb).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR Flo].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR Fhi].
  assert (HloHalf : Binary.B2R prec emax (b64_minus cc b64_half)
                    = (IZR (2 * ncc - 1)%Z / 2)%R)
    by (rewrite HloR, HccR, minus_IZR, mult_IZR; lra).
  assert (HhiHalf : Binary.B2R prec emax (b64_plus cc b64_half)
                    = (IZR (2 * ncc + 1)%Z / 2)%R)
    by (rewrite HhiR, HccR, plus_IZR, mult_IZR; lra).
  assert (Heqb : b64_eqb c1 c0 = false).
  { destruct (b64_eqb c1 c0) eqn:E; [ | reflexivity ].
    apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0) in E. contradiction. }
  pose proof (grid_numerator_facts (b64_minus cc b64_half) c0 (2*ncc-1) n0
                Flo Fc0 HloHalf H0R ltac:(lia) ltac:(lia))
    as (HnumLoR & HnumLoFin & HnumLoB & HnumLoDiff).
  pose proof (grid_numerator_facts (b64_plus cc b64_half) c0 (2*ncc+1) n0
                Fhi Fc0 HhiHalf H0R ltac:(lia) ltac:(lia))
    as (HnumHiR & HnumHiFin & HnumHiB & HnumHiDiff).
  assert (H1half : Binary.B2R prec emax c1 = (IZR (2 * n1)%Z / 2)%R)
    by (rewrite H1R, mult_IZR; lra).
  assert (H0half : Binary.B2R prec emax c0 = (IZR (2 * n0)%Z / 2)%R)
    by (rewrite H0R, mult_IZR; lra).
  pose proof (b64_minus_half_exact c1 c0 (2*n1) (2*n0) Fc1 Fc0 H1half H0half
                ltac:(unfold prec; lia)) as [HdenDiff HdenFin].
  assert (HdenRv : Binary.B2R prec emax (b64_minus c1 c0) = IZR (n1 - n0)%Z)
    by (rewrite HdenDiff, H1R, H0R, minus_IZR; lra).
  assert (Hdne : (n1 - n0 <> 0)%Z).
  { intro Hz. apply Hne. rewrite H1R, H0R. apply f_equal. lia. }
  pose proof (b64_div_round_half_over_int (b64_minus (b64_minus cc b64_half) c0)
                (b64_minus c1 c0) (2*ncc-1 - 2*n0) (n1 - n0)
                HnumLoFin HdenFin HnumLoR HdenRv Hdne ltac:(lia))
    as [HdivLoR HdivLoFin].
  pose proof (b64_div_round_half_over_int (b64_minus (b64_plus cc b64_half) c0)
                (b64_minus c1 c0) (2*ncc+1 - 2*n0) (n1 - n0)
                HnumHiFin HdenFin HnumHiR HdenRv Hdne ltac:(lia))
    as [HdivHiR HdivHiFin].
  unfold b64_lb_thi. rewrite Heqb.
  rewrite (b64_max_B2R _ _ HdivLoFin HdivHiFin).
  rewrite HdivLoR, HdivHiR.
  rewrite HnumLoDiff, HnumHiDiff, HdenDiff.
  reflexivity.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 7: the t-bounds are the CORRECTLY-ROUNDED exact t-bounds on the grid.

   Rounding is monotone, so Rmin (round a) (round b) = round (Rmin a b) (dually
   for Rmax).  Composing this with Slice 6 collapses each per-axis compute
   t-bound -- an Rmin/Rmax of two ROUNDED quotients -- into a single `b64_round`
   of the exact spec t-bound.  The degenerate (axis-parallel) branch matches
   trivially (0 = round 0, 1 = round 1), so the bridge is UNCONDITIONAL.
   ---------------------------------------------------------------------------- *)

(* b64_zero facts (b64_one's are in HotPixel_b64). *)
Lemma B2R_b64_zero : Binary.B2R prec emax b64_zero = 0%R.
Proof. reflexivity. Qed.

Lemma is_finite_b64_zero : Binary.is_finite prec emax b64_zero = true.
Proof. reflexivity. Qed.

Lemma b64_round_1 : b64_round 1 = 1%R.
Proof.
  apply b64_round_generic.
  assert (H1 : (1)%R = F2R (Float radix2 2 (-1))) by (unfold F2R; simpl; lra).
  rewrite H1. apply generic_format_half_prec. unfold prec; lia.
Qed.

(* Rounding commutes with Rmin / Rmax (monotonicity of round-to-nearest). *)
Lemma round_Rmin :
  forall a b : R, Rmin (b64_round a) (b64_round b) = b64_round (Rmin a b).
Proof.
  intros a b. destruct (Rle_dec a b) as [H | H].
  - rewrite (Rmin_left a b H). apply Rmin_left.
    apply (round_le radix2 b64_fexp (round_mode mode_b64)); exact H.
  - assert (Hb : (b <= a)%R) by lra.
    rewrite (Rmin_right a b Hb). apply Rmin_right.
    apply (round_le radix2 b64_fexp (round_mode mode_b64)); exact Hb.
Qed.

Lemma round_Rmax :
  forall a b : R, Rmax (b64_round a) (b64_round b) = b64_round (Rmax a b).
Proof.
  intros a b. destruct (Rle_dec a b) as [H | H].
  - rewrite (Rmax_right a b H). apply Rmax_right.
    apply (round_le radix2 b64_fexp (round_mode mode_b64)); exact H.
  - assert (Hb : (b <= a)%R) by lra.
    rewrite (Rmax_left a b Hb). apply Rmax_left.
    apply (round_le radix2 b64_fexp (round_mode mode_b64)); exact Hb.
Qed.

(* Clip composition: rounding commutes past the outer max-with-0 / min-with-1. *)
Lemma round_clip_max0 :
  forall a : R, Rmax 0 (b64_round a) = b64_round (Rmax 0 a).
Proof.
  intros a. rewrite <- round_Rmax, (round_0 radix2 b64_fexp (round_mode mode_b64)).
  reflexivity.
Qed.

Lemma round_clip_min1 :
  forall a : R, Rmin 1 (b64_round a) = b64_round (Rmin 1 a).
Proof. intros a. rewrite <- round_Rmin, b64_round_1. reflexivity. Qed.

(* Division finiteness on the grid: one t-bound quotient (half-integer
   numerator over a nonzero integer run) is finite.  Reuses Slice 6's pieces. *)
Lemma b64_div_edge_grid_finite :
  forall (edge c0 c1 : binary64) (m n0 n1 : Z),
    Binary.is_finite prec emax edge = true ->
    Binary.is_finite prec emax c0 = true ->
    Binary.is_finite prec emax c1 = true ->
    Binary.B2R prec emax edge = (IZR m / 2)%R ->
    Binary.B2R prec emax c0 = IZR n0 ->
    Binary.B2R prec emax c1 = IZR n1 ->
    (Z.abs m < 2 ^ 27)%Z ->
    (Z.abs n0 <= 2 ^ 25)%Z ->
    (Z.abs n1 <= 2 ^ 25)%Z ->
    (n1 <> n0)%Z ->
    Binary.is_finite prec emax
      (b64_div (b64_minus edge c0) (b64_minus c1 c0)) = true.
Proof.
  intros edge c0 c1 m n0 n1 Fe F0 F1 HeR H0R H1R Hm Hn0 Hn1 Hne.
  pose proof (grid_numerator_facts edge c0 m n0 Fe F0 HeR H0R Hm Hn0)
    as (HnumR & HnumFin & HnumB & _).
  assert (H0half : Binary.B2R prec emax c0 = (IZR (2 * n0)%Z / 2)%R)
    by (rewrite H0R, mult_IZR; lra).
  assert (H1half : Binary.B2R prec emax c1 = (IZR (2 * n1)%Z / 2)%R)
    by (rewrite H1R, mult_IZR; lra).
  pose proof (b64_minus_half_exact c1 c0 (2*n1) (2*n0) F1 F0 H1half H0half
                ltac:(unfold prec; lia)) as [HdenR HdenFin].
  assert (HdenRv : Binary.B2R prec emax (b64_minus c1 c0) = IZR (n1 - n0)%Z)
    by (rewrite HdenR, H1R, H0R, minus_IZR; lra).
  exact (proj2 (b64_div_round_half_over_int (b64_minus edge c0) (b64_minus c1 c0)
                  (m - 2*n0) (n1 - n0) HnumFin HdenFin HnumR HdenRv
                  ltac:(lia) ltac:(lia))).
Qed.

Lemma b64_lb_tlo_finite_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.is_finite prec emax
      (b64_lb_tlo c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half)) = true.
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc.
  pose proof Hc0 as (Fc0 & n0 & H0R & H0b).
  pose proof Hc1 as (Fc1 & n1 & H1R & H1b).
  pose proof Hcc as (Fcc & ncc & HccR & Hccb).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR Flo].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR Fhi].
  assert (HloHalf : Binary.B2R prec emax (b64_minus cc b64_half) = (IZR (2*ncc-1)%Z / 2)%R)
    by (rewrite HloR, HccR, minus_IZR, mult_IZR; lra).
  assert (HhiHalf : Binary.B2R prec emax (b64_plus cc b64_half) = (IZR (2*ncc+1)%Z / 2)%R)
    by (rewrite HhiR, HccR, plus_IZR, mult_IZR; lra).
  unfold b64_lb_tlo.
  destruct (b64_eqb c1 c0) eqn:Heqb.
  - exact is_finite_b64_zero.
  - assert (Hne : (n1 <> n0)%Z).
    { intro He. assert (Heq : Binary.B2R prec emax c1 = Binary.B2R prec emax c0)
        by (rewrite H1R, H0R, He; reflexivity).
      assert (Ht : b64_eqb c1 c0 = true)
        by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact Heq). congruence. }
    apply is_finite_b64_min.
    + exact (b64_div_edge_grid_finite (b64_minus cc b64_half) c0 c1 (2*ncc-1) n0 n1
               Flo Fc0 Fc1 HloHalf H0R H1R ltac:(lia) ltac:(lia) ltac:(lia) Hne).
    + exact (b64_div_edge_grid_finite (b64_plus cc b64_half) c0 c1 (2*ncc+1) n0 n1
               Fhi Fc0 Fc1 HhiHalf H0R H1R ltac:(lia) ltac:(lia) ltac:(lia) Hne).
Qed.

Lemma b64_lb_thi_finite_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.is_finite prec emax
      (b64_lb_thi c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half)) = true.
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc.
  pose proof Hc0 as (Fc0 & n0 & H0R & H0b).
  pose proof Hc1 as (Fc1 & n1 & H1R & H1b).
  pose proof Hcc as (Fcc & ncc & HccR & Hccb).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR Flo].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR Fhi].
  assert (HloHalf : Binary.B2R prec emax (b64_minus cc b64_half) = (IZR (2*ncc-1)%Z / 2)%R)
    by (rewrite HloR, HccR, minus_IZR, mult_IZR; lra).
  assert (HhiHalf : Binary.B2R prec emax (b64_plus cc b64_half) = (IZR (2*ncc+1)%Z / 2)%R)
    by (rewrite HhiR, HccR, plus_IZR, mult_IZR; lra).
  unfold b64_lb_thi.
  destruct (b64_eqb c1 c0) eqn:Heqb.
  - exact is_finite_b64_one.
  - assert (Hne : (n1 <> n0)%Z).
    { intro He. assert (Heq : Binary.B2R prec emax c1 = Binary.B2R prec emax c0)
        by (rewrite H1R, H0R, He; reflexivity).
      assert (Ht : b64_eqb c1 c0 = true)
        by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact Heq). congruence. }
    apply is_finite_b64_max.
    + exact (b64_div_edge_grid_finite (b64_minus cc b64_half) c0 c1 (2*ncc-1) n0 n1
               Flo Fc0 Fc1 HloHalf H0R H1R ltac:(lia) ltac:(lia) ltac:(lia) Hne).
    + exact (b64_div_edge_grid_finite (b64_plus cc b64_half) c0 c1 (2*ncc+1) n0 n1
               Fhi Fc0 Fc1 HhiHalf H0R H1R ltac:(lia) ltac:(lia) ltac:(lia) Hne).
Qed.

(* tlo: the compute lower t-bound = b64_round of the exact spec t-bound. *)
Theorem b64_lb_tlo_eq_round_exact_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.B2R prec emax (b64_lb_tlo c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half))
      = b64_round (lb_tlo (Binary.B2R prec emax c0) (Binary.B2R prec emax c1)
                          (Binary.B2R prec emax cc - / 2) (Binary.B2R prec emax cc + / 2)).
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc.
  pose proof Hc0 as (Fc0 & _).
  pose proof Hc1 as (Fc1 & _).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR _].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR _].
  destruct (b64_eqb c1 c0) eqn:Heqb.
  - assert (HBeq : Binary.B2R prec emax c1 = Binary.B2R prec emax c0)
      by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact Heqb).
    unfold b64_lb_tlo. rewrite Heqb. rewrite B2R_b64_zero.
    unfold lb_tlo.
    destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0)) as [_ | Hq];
      [ | contradiction ].
    symmetry. apply (round_0 radix2 b64_fexp (round_mode mode_b64)).
  - assert (Hne : Binary.B2R prec emax c1 <> Binary.B2R prec emax c0).
    { intro He. assert (Ht : b64_eqb c1 c0 = true)
        by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact He). congruence. }
    rewrite (b64_lb_tlo_eq_rounded_quotients_grid c0 c1 cc Hc0 Hc1 Hcc Hne).
    rewrite HloR, HhiR, round_Rmin.
    unfold lb_tlo.
    destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0)) as [Hq | _];
      [ contradiction | reflexivity ].
Qed.

(* thi: the compute upper t-bound = b64_round of the exact spec t-bound. *)
Theorem b64_lb_thi_eq_round_exact_grid :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    Binary.B2R prec emax (b64_lb_thi c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half))
      = b64_round (lb_thi (Binary.B2R prec emax c0) (Binary.B2R prec emax c1)
                          (Binary.B2R prec emax cc - / 2) (Binary.B2R prec emax cc + / 2)).
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc.
  pose proof Hc0 as (Fc0 & _).
  pose proof Hc1 as (Fc1 & _).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR _].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR _].
  destruct (b64_eqb c1 c0) eqn:Heqb.
  - assert (HBeq : Binary.B2R prec emax c1 = Binary.B2R prec emax c0)
      by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact Heqb).
    unfold b64_lb_thi. rewrite Heqb. rewrite B2R_b64_one.
    unfold lb_thi.
    destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0)) as [_ | Hq];
      [ | contradiction ].
    symmetry. apply b64_round_1.
  - assert (Hne : Binary.B2R prec emax c1 <> Binary.B2R prec emax c0).
    { intro He. assert (Ht : b64_eqb c1 c0 = true)
        by (apply (b64_eqb_true_iff_B2R c1 c0 Fc1 Fc0); exact He). congruence. }
    rewrite (b64_lb_thi_eq_rounded_quotients_grid c0 c1 cc Hc0 Hc1 Hcc Hne).
    rewrite HloR, HhiR, round_Rmax.
    unfold lb_thi.
    destruct (Req_dec_T (Binary.B2R prec emax c1) (Binary.B2R prec emax c0)) as [Hq | _];
      [ contradiction | reflexivity ].
Qed.

(* ----------------------------------------------------------------------------
   SLICE 8: the clipped tmin / tmax are the correctly-rounded exact ones.

   Pushing the rounding through the outer Rmax-0 / Rmin-1 clip and the per-axis
   Rmax/Rmin (all monotone) gives: on the integer grid, the WHOLE compute t-bound
   numerator/denominator pipeline equals `b64_round` of the exact spec value.
   ---------------------------------------------------------------------------- *)

Theorem b64_tmin_eq_round_exact_grid :
  forall x0 x1 cx y0 y1 cy : binary64,
    coord_int_safe x0 -> coord_int_safe x1 -> coord_int_safe cx ->
    coord_int_safe y0 -> coord_int_safe y1 -> coord_int_safe cy ->
    Binary.B2R prec emax
      (b64_max b64_zero
        (b64_max (b64_lb_tlo x0 x1 (b64_minus cx b64_half) (b64_plus cx b64_half))
                 (b64_lb_tlo y0 y1 (b64_minus cy b64_half) (b64_plus cy b64_half))))
      = b64_round
          (Rmax 0 (Rmax (lb_tlo (Binary.B2R prec emax x0) (Binary.B2R prec emax x1)
                               (Binary.B2R prec emax cx - / 2) (Binary.B2R prec emax cx + / 2))
                        (lb_tlo (Binary.B2R prec emax y0) (Binary.B2R prec emax y1)
                               (Binary.B2R prec emax cy - / 2) (Binary.B2R prec emax cy + / 2)))).
Proof.
  intros x0 x1 cx y0 y1 cy Hx0 Hx1 Hcx Hy0 Hy1 Hcy.
  pose proof (b64_lb_tlo_finite_grid x0 x1 cx Hx0 Hx1 Hcx) as HxF.
  pose proof (b64_lb_tlo_finite_grid y0 y1 cy Hy0 Hy1 Hcy) as HyF.
  rewrite (b64_max_B2R _ _ is_finite_b64_zero (is_finite_b64_max _ _ HxF HyF)).
  rewrite B2R_b64_zero.
  rewrite (b64_max_B2R _ _ HxF HyF).
  rewrite (b64_lb_tlo_eq_round_exact_grid x0 x1 cx Hx0 Hx1 Hcx).
  rewrite (b64_lb_tlo_eq_round_exact_grid y0 y1 cy Hy0 Hy1 Hcy).
  rewrite round_Rmax.
  apply round_clip_max0.
Qed.

Theorem b64_tmax_eq_round_exact_grid :
  forall x0 x1 cx y0 y1 cy : binary64,
    coord_int_safe x0 -> coord_int_safe x1 -> coord_int_safe cx ->
    coord_int_safe y0 -> coord_int_safe y1 -> coord_int_safe cy ->
    Binary.B2R prec emax
      (b64_min b64_one
        (b64_min (b64_lb_thi x0 x1 (b64_minus cx b64_half) (b64_plus cx b64_half))
                 (b64_lb_thi y0 y1 (b64_minus cy b64_half) (b64_plus cy b64_half))))
      = b64_round
          (Rmin 1 (Rmin (lb_thi (Binary.B2R prec emax x0) (Binary.B2R prec emax x1)
                               (Binary.B2R prec emax cx - / 2) (Binary.B2R prec emax cx + / 2))
                        (lb_thi (Binary.B2R prec emax y0) (Binary.B2R prec emax y1)
                               (Binary.B2R prec emax cy - / 2) (Binary.B2R prec emax cy + / 2)))).
Proof.
  intros x0 x1 cx y0 y1 cy Hx0 Hx1 Hcx Hy0 Hy1 Hcy.
  pose proof (b64_lb_thi_finite_grid x0 x1 cx Hx0 Hx1 Hcx) as HxF.
  pose proof (b64_lb_thi_finite_grid y0 y1 cy Hy0 Hy1 Hcy) as HyF.
  rewrite (b64_min_B2R _ _ is_finite_b64_one (is_finite_b64_min _ _ HxF HyF)).
  rewrite B2R_b64_one.
  rewrite (b64_min_B2R _ _ HxF HyF).
  rewrite (b64_lb_thi_eq_round_exact_grid x0 x1 cx Hx0 Hx1 Hcx).
  rewrite (b64_lb_thi_eq_round_exact_grid y0 y1 cy Hy0 Hy1 Hcy).
  rewrite round_Rmin.
  apply round_clip_min1.
Qed.

