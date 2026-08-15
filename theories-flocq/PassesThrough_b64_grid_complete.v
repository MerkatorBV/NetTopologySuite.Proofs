(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_grid_complete
   ----------------------------------------------------------------------------
   SLICES 9-11: completeness, the conditional headline, rounding reflection.

   Slices 9-11: ON-GRID COMPLETENESS (the rounded filter never drops a
   pass); the CONDITIONAL grid-exactness headline; the rounding-reflection
   kernel that trades the rounding hypothesis for the pure-reals
   clip_separated separation hypothesis.

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

(* ----------------------------------------------------------------------------
   SLICE 9: ON-GRID COMPLETENESS -- the rounded filter never DROPS a pass on
   the grid (the noder-SAFE direction).

   This CLOSES one of C1's two directions.  Since rounding is monotone, the
   exact comparison `tmin <= tmax` (spec touch true) gives the rounded
   comparison `round tmin <= round tmax` (compute touch true) for free; the slab
   guards are bit-identical on the grid (Slice 3).  The remaining OPEN direction
   is on-grid soundness (compute => spec), which needs the lack-of-outward-
   guarantee argument -- see the OBLIGATION note below.
   ---------------------------------------------------------------------------- *)

(* Slab guard equality on the grid: the compute closed-slab guard equals the
   exact-spec guard (Slice 3 + the exact pixel half-edges). *)
Lemma slab_closed_grid_eq :
  forall c0 c1 cc : binary64,
    coord_int_safe c0 -> coord_int_safe c1 -> coord_int_safe cc ->
    b64_lb_inslab_closed c0 c1 (b64_minus cc b64_half) (b64_plus cc b64_half)
      = lb_inslab (Binary.B2R prec emax c0) (Binary.B2R prec emax c1)
                  (Binary.B2R prec emax cc - / 2) (Binary.B2R prec emax cc + / 2).
Proof.
  intros c0 c1 cc Hc0 Hc1 Hcc.
  pose proof Hc0 as (Fc0 & _).
  pose proof Hc1 as (Fc1 & _).
  pose proof (b64_minus_half_int_exact cc Hcc) as [HloR Flo].
  pose proof (b64_plus_half_int_exact cc Hcc) as [HhiR Fhi].
  rewrite (slab_guard_bridge c0 c1 _ _ Fc0 Fc1 Flo Fhi).
  rewrite HloR, HhiR. reflexivity.
Qed.

(* Single-touch on-grid completeness. *)
Theorem b64_liang_barsky_touches_complete_on_grid :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    b64_liang_barsky_touches P0 P1 C = true ->
    b64_liang_barsky_touches_compute P0 P1 C = true.
Proof.
  intros P0 P1 C (Hx0 & Hy0) (Hx1 & Hy1) (Hcx & Hcy) Hspec.
  unfold b64_liang_barsky_touches in Hspec.
  apply Bool.andb_true_iff in Hspec. destruct Hspec as [Hslabs Hcmp].
  apply Bool.andb_true_iff in Hslabs. destruct Hslabs as [HslabX HslabY].
  apply Rle_bool_elim in Hcmp.
  unfold b64_liang_barsky_touches_compute.
  apply Bool.andb_true_iff. split.
  - apply Bool.andb_true_iff. split.
    + rewrite (slab_closed_grid_eq (bx P0) (bx P1) (bx C) Hx0 Hx1 Hcx). exact HslabX.
    + rewrite (slab_closed_grid_eq (by_ P0) (by_ P1) (by_ C) Hy0 Hy1 Hcy). exact HslabY.
  - apply b64_le_complete.
    + apply is_finite_b64_max;
        [ exact is_finite_b64_zero
        | apply is_finite_b64_max;
          [ apply b64_lb_tlo_finite_grid; assumption
          | apply b64_lb_tlo_finite_grid; assumption ] ].
    + apply is_finite_b64_min;
        [ exact is_finite_b64_one
        | apply is_finite_b64_min;
          [ apply b64_lb_thi_finite_grid; assumption
          | apply b64_lb_thi_finite_grid; assumption ] ].
    + rewrite (b64_tmin_eq_round_exact_grid (bx P0)(bx P1)(bx C)(by_ P0)(by_ P1)(by_ C)
                 Hx0 Hx1 Hcx Hy0 Hy1 Hcy).
      rewrite (b64_tmax_eq_round_exact_grid (bx P0)(bx P1)(bx C)(by_ P0)(by_ P1)(by_ C)
                 Hx0 Hx1 Hcx Hy0 Hy1 Hcy).
      apply (round_le radix2 b64_fexp (round_mode mode_b64)).
      exact Hcmp.
Qed.

(* Full passes-through predicate, on the grid: never drops a pass.  Lifts the
   single-touch completeness through the Slice-1 collapse (grid points are snap
   fixed points). *)
Corollary b64_passes_through_complete_on_grid :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    b64_passes_through_hot_pixel P0 P1 C = true ->
    b64_passes_through_hot_pixel_compute P0 P1 C = true.
Proof.
  intros P0 P1 C HP0 HP1 HC Hpass.
  rewrite (b64_passes_through_compute_collapses_on_grid P0 P1 C
             (bpoint_int_safe_on_grid P0 HP0) (bpoint_int_safe_on_grid P1 HP1)).
  rewrite (b64_passes_through_collapses_on_grid P0 P1 C
             (bpoint_int_safe_on_grid P0 HP0) (bpoint_int_safe_on_grid P1 HP1)) in Hpass.
  apply b64_liang_barsky_touches_complete_on_grid; assumption.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 10: the conditional grid-exactness headline.

   Slices 3-9 reduce the whole on-grid `compute = spec` question to ONE real-
   number fact: that rounding both exact clip bounds preserves their <= verdict.
   We name that fact and Qed-certify the entire reduction modulo it -- the same
   honest "conditional headline" shape as hobby_theorem_4_1_conditional and
   overlay_ng_correct_conditional.  No Admitted / Axiom / Parameter: the gap is a
   plain Prop hypothesis of the theorem.

   The hypothesis's `<=`-true direction is FREE (monotonicity; that is exactly
   Slice 9's on-grid completeness), so the only genuinely open content is the
   reverse -- the soundness direction.  See the OBLIGATION note for the gap
   analysis and the coordinate-regime in which it provably holds.
   ---------------------------------------------------------------------------- *)

(* The exact spec clip bounds, named so the remaining obligation is crisp. *)
Definition tmin_exact (P0 P1 C : BPoint) : R :=
  Rmax 0 (Rmax (lb_tlo (Binary.B2R prec emax (bx P0)) (Binary.B2R prec emax (bx P1))
                       (Binary.B2R prec emax (bx C) - / 2) (Binary.B2R prec emax (bx C) + / 2))
               (lb_tlo (Binary.B2R prec emax (by_ P0)) (Binary.B2R prec emax (by_ P1))
                       (Binary.B2R prec emax (by_ C) - / 2) (Binary.B2R prec emax (by_ C) + / 2))).

Definition tmax_exact (P0 P1 C : BPoint) : R :=
  Rmin 1 (Rmin (lb_thi (Binary.B2R prec emax (bx P0)) (Binary.B2R prec emax (bx P1))
                       (Binary.B2R prec emax (bx C) - / 2) (Binary.B2R prec emax (bx C) + / 2))
               (lb_thi (Binary.B2R prec emax (by_ P0)) (Binary.B2R prec emax (by_ P1))
                       (Binary.B2R prec emax (by_ C) - / 2) (Binary.B2R prec emax (by_ C) + / 2))).

(* Single-touch grid exactness, conditional on the rounded clip comparison
   reflecting the exact one (the only remaining gap). *)
Theorem b64_liang_barsky_grid_exact_cond :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    (Rle_bool (b64_round (tmin_exact P0 P1 C)) (b64_round (tmax_exact P0 P1 C))
       = Rle_bool (tmin_exact P0 P1 C) (tmax_exact P0 P1 C)) ->
    b64_liang_barsky_touches_compute P0 P1 C = b64_liang_barsky_touches P0 P1 C.
Proof.
  intros P0 P1 C HP0 HP1 HC Hreflect.
  destruct HP0 as (Hx0 & Hy0). destruct HP1 as (Hx1 & Hy1). destruct HC as (Hcx & Hcy).
  unfold b64_liang_barsky_touches_compute, b64_liang_barsky_touches. cbv zeta.
  rewrite (slab_closed_grid_eq (bx P0) (bx P1) (bx C) Hx0 Hx1 Hcx).
  rewrite (slab_closed_grid_eq (by_ P0) (by_ P1) (by_ C) Hy0 Hy1 Hcy).
  rewrite b64_le_eq_Rle_bool.
  2: { apply is_finite_b64_max;
         [ exact is_finite_b64_zero
         | apply is_finite_b64_max; apply b64_lb_tlo_finite_grid; assumption ]. }
  2: { apply is_finite_b64_min;
         [ exact is_finite_b64_one
         | apply is_finite_b64_min; apply b64_lb_thi_finite_grid; assumption ]. }
  rewrite (b64_tmin_eq_round_exact_grid (bx P0) (bx P1) (bx C) (by_ P0) (by_ P1) (by_ C)
             Hx0 Hx1 Hcx Hy0 Hy1 Hcy).
  rewrite (b64_tmax_eq_round_exact_grid (bx P0) (bx P1) (bx C) (by_ P0) (by_ P1) (by_ C)
             Hx0 Hx1 Hcx Hy0 Hy1 Hcy).
  unfold tmin_exact, tmax_exact in Hreflect.
  rewrite Hreflect. reflexivity.
Qed.

(* Full passes-through predicate, conditional grid exactness (via the Slice-1
   collapse: grid points are snap fixed points). *)
Corollary b64_passes_through_grid_exact_cond :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    (Rle_bool (b64_round (tmin_exact P0 P1 C)) (b64_round (tmax_exact P0 P1 C))
       = Rle_bool (tmin_exact P0 P1 C) (tmax_exact P0 P1 C)) ->
    b64_passes_through_hot_pixel_compute P0 P1 C = b64_passes_through_hot_pixel P0 P1 C.
Proof.
  intros P0 P1 C HP0 HP1 HC Hreflect.
  rewrite (b64_passes_through_compute_collapses_on_grid P0 P1 C
             (bpoint_int_safe_on_grid P0 HP0) (bpoint_int_safe_on_grid P1 HP1)).
  rewrite (b64_passes_through_collapses_on_grid P0 P1 C
             (bpoint_int_safe_on_grid P0 HP0) (bpoint_int_safe_on_grid P1 HP1)).
  apply b64_liang_barsky_grid_exact_cond; assumption.
Qed.

(* The soundness direction the user asked for, as a direct corollary: on the
   grid, compute = true => spec = true, conditional on the same reflection. *)
Corollary b64_passes_through_sound_on_grid_cond :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    (Rle_bool (b64_round (tmin_exact P0 P1 C)) (b64_round (tmax_exact P0 P1 C))
       = Rle_bool (tmin_exact P0 P1 C) (tmax_exact P0 P1 C)) ->
    b64_passes_through_hot_pixel_compute P0 P1 C = true ->
    b64_passes_through_hot_pixel P0 P1 C = true.
Proof.
  intros P0 P1 C HP0 HP1 HC Hreflect Hc.
  rewrite <- (b64_passes_through_grid_exact_cond P0 P1 C HP0 HP1 HC Hreflect).
  exact Hc.
Qed.

(* ----------------------------------------------------------------------------
   SLICE 11: the rounding-reflection kernel -- turn Slice 10's rounding
   hypothesis into a pure-reals SEPARATION fact (no Rle_bool-of-rounds left).

   Round-to-nearest moves each value by at most half a ulp
   (`b64_error_le_half_ulp_round`).  So if `round a <= round b` then
   `a - b <= ulp(round a)/2 + ulp(round b)/2`: rounding can flip a strict `b < a`
   only when the two are within that combined half-ulp band.  Hence the rounded
   `<=` REFLECTS the exact `<=` as soon as the exact values are either ordered or
   separated by more than the band.  This is the general tool that discharges
   Slice 10's `Hreflect`; what remains is purely that `tmin_exact`/`tmax_exact`
   are so separated on the grid (the integer-determinant gap), with NO rounding
   in the statement.
   ---------------------------------------------------------------------------- *)

(* Half-ulp transfer: round a <= round b bounds the exact difference. *)
Lemma round_diff_le_of_round_le :
  forall a b : R,
    (b64_round a <= b64_round b)%R ->
    (a - b <= b64_ulp (b64_round a) / 2 + b64_ulp (b64_round b) / 2)%R.
Proof.
  intros a b Hle.
  pose proof (b64_error_le_half_ulp_round a) as Ha.
  pose proof (b64_error_le_half_ulp_round b) as Hb.
  apply Rabs_le_inv in Ha. apply Rabs_le_inv in Hb. lra.
Qed.

(* Reflection under separation: the rounded `<=` matches the exact `<=` whenever
   the exact values are ordered or separated beyond the combined half-ulp band. *)
Lemma round_reflects_le_of_sep :
  forall a b : R,
    (a <= b \/ b64_ulp (b64_round a) / 2 + b64_ulp (b64_round b) / 2 < a - b)%R ->
    ((b64_round a <= b64_round b)%R <-> (a <= b)%R).
Proof.
  intros a b Hsep. split.
  - intro Hr. destruct Hsep as [Hab | Hgap].
    + exact Hab.
    + exfalso. pose proof (round_diff_le_of_round_le a b Hr). lra.
  - intro Hab. apply (round_le radix2 b64_fexp (round_mode mode_b64)). exact Hab.
Qed.

(* The pure-reals separation predicate for the exact clip bounds.  No Rle_bool
   of rounds: just "interval nonempty, or empty beyond the half-ulp band". *)
Definition clip_separated (P0 P1 C : BPoint) : Prop :=
  (tmin_exact P0 P1 C <= tmax_exact P0 P1 C)%R
  \/ (b64_ulp (b64_round (tmin_exact P0 P1 C)) / 2
       + b64_ulp (b64_round (tmax_exact P0 P1 C)) / 2
     < tmin_exact P0 P1 C - tmax_exact P0 P1 C)%R.

(* Separation discharges Slice 10's reflection hypothesis. *)
Lemma clip_separated_reflects :
  forall P0 P1 C : BPoint,
    clip_separated P0 P1 C ->
    Rle_bool (b64_round (tmin_exact P0 P1 C)) (b64_round (tmax_exact P0 P1 C))
      = Rle_bool (tmin_exact P0 P1 C) (tmax_exact P0 P1 C).
Proof.
  intros P0 P1 C Hsep.
  pose proof (round_reflects_le_of_sep (tmin_exact P0 P1 C) (tmax_exact P0 P1 C) Hsep)
    as Hiff.
  destruct (Rle_bool (b64_round (tmin_exact P0 P1 C)) (b64_round (tmax_exact P0 P1 C)))
    eqn:E1;
    destruct (Rle_bool (tmin_exact P0 P1 C) (tmax_exact P0 P1 C)) eqn:E2;
    try reflexivity.
  - exfalso. apply Rle_bool_elim in E1. apply (proj1 Hiff) in E1.
    rewrite (Rle_bool_true _ _ E1) in E2. discriminate.
  - exfalso. apply Rle_bool_elim in E2. apply (proj2 Hiff) in E2.
    rewrite (Rle_bool_true _ _ E2) in E1. discriminate.
Qed.

(* Grid-exactness under separation -- the rounding hypothesis is GONE, replaced
   by the pure-reals `clip_separated` (the integer-determinant gap). *)
Corollary b64_passes_through_grid_exact_sep :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    clip_separated P0 P1 C ->
    b64_passes_through_hot_pixel_compute P0 P1 C = b64_passes_through_hot_pixel P0 P1 C.
Proof.
  intros P0 P1 C HP0 HP1 HC Hsep.
  apply b64_passes_through_grid_exact_cond; try assumption.
  apply clip_separated_reflects; assumption.
Qed.

Corollary b64_passes_through_sound_on_grid_sep :
  forall P0 P1 C : BPoint,
    bpoint_int_safe P0 -> bpoint_int_safe P1 -> bpoint_int_safe C ->
    clip_separated P0 P1 C ->
    b64_passes_through_hot_pixel_compute P0 P1 C = true ->
    b64_passes_through_hot_pixel P0 P1 C = true.
Proof.
  intros P0 P1 C HP0 HP1 HC Hsep Hc.
  rewrite <- (b64_passes_through_grid_exact_sep P0 P1 C HP0 HP1 HC Hsep).
  exact Hc.
Qed.

