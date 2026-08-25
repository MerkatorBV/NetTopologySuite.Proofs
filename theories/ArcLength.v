(* ============================================================================
   NetTopologySuite.Proofs.ArcLength
   ----------------------------------------------------------------------------
   Option-A arc primitives, foundation 3/N (issue #64 ask #1): exact arc length
   s = r * theta, with the chord/arc soundness relations a curve-aware buffer
   and linearisation rely on (M-LEN-CS / M-LEN-CC).

     arc_length r theta      := r * theta               (* the r*theta law   *)
     chord_subtended r theta := 2 * r * sin (theta / 2)  (* its chord         *)

   Headlines:
     chord_le_arc_length : 0<=r -> 0<=theta ->
         chord_subtended r theta <= arc_length r theta
       (the chord never exceeds the arc it subtends -- the arc analogue of
        Linearise.v's chord_le_detour; underpins curve length monotonicity).
     chord_subtended_sq  : (chord_subtended r theta)^2 = 2*r^2*(1 - cos theta)
       (half-angle bridge to the cosine/dot-product world: 1 - cos theta
        = 2 sin^2(theta/2); with theta the central angle from AngleBetween,
        cos theta = dot/(r*r), giving the exact rational chord^2 = 2*(r*r - dot)).

   Pure Stdlib trig (no atan2).  `sin_le_x` / `sin_lt_x_pos` avoid Stdlib
   `sin_lt_x` (MVT → `Classical_Prop.classic`): `|sin| ≤ 1` for x ≥ 1, and
   the 3-axiom Taylor envelope `pre_sin_bound` for 0 ≤ x ≤ 1.  THREE-AXIOM.
   No Admitted.  Refs #64.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Rtrigo_alt Arith.Factorial.
(* ArcLength is the scalar foundation. High-level arc_length_of for CircularArc lives in RelateArcAnalytic to avoid cycles. *)
Local Open Scope R_scope.

Definition arc_length (r theta : R) : R := r * theta.
Definition chord_subtended (r theta : R) : R := 2 * r * sin (theta / 2).

(* Two-term Taylor envelope: a − a³/6 + a⁵/120.  3-axiom. *)
Lemma sin_approx_2 :
  forall a : R, sin_approx a 2 = a - a ^ 3 / 6 + a ^ 5 / 120.
Proof.
  intros a.
  unfold sin_approx, sin_term.
  simpl.
  unfold Rdiv.
  field.
Qed.

(* 0 < x → sin x < x, without Stdlib sin_lt_x / MVT / classic. *)
Lemma sin_lt_x_pos : forall x : R, 0 < x -> sin x < x.
Proof.
  intros x Hx.
  destruct (Rle_lt_dec x 1) as [Hle | Hgt].
  - assert (H04 : x <= 4) by lra.
    destruct (pre_sin_bound x 0 (Rlt_le _ _ Hx) H04) as [_ Hub].
    rewrite sin_approx_2 in Hub.
    assert (Hgap : 0 < x ^ 3 / 6 - x ^ 5 / 120).
    { unfold Rdiv.
      replace (x ^ 3 * / 6 - x ^ 5 * / 120)
        with (x ^ 3 * (/ 6 - x ^ 2 * / 120)) by ring.
      apply Rmult_lt_0_compat.
      { apply pow_lt; exact Hx. }
      apply Rlt_0_minus. apply Rmult_lt_reg_r with 120.
      { lra. }
      replace ((/ 6 - x ^ 2 * / 120) * 120)
        with (20 - x * x) by (simpl; field).
      assert (x * x <= 1).
      { apply Rle_trans with (r2 := 1 * 1).
        { apply Rmult_le_compat; lra. }
        lra. }
      lra. }
    apply Rle_lt_trans with (r2 := x - x ^ 3 / 6 + x ^ 5 / 120).
    { exact Hub. }
    apply Rminus_lt.
    replace (x - x ^ 3 / 6 + x ^ 5 / 120 - x)
      with (- (x ^ 3 / 6 - x ^ 5 / 120)) by (unfold Rdiv; ring).
    apply Ropp_lt_gt_0_contravar. exact Hgap.
  - pose proof (SIN_bound x) as [_ Hs]. lra.
Qed.

(* sin x <= x for x >= 0.  Equality at 0; strict above via sin_lt_x_pos. *)
Lemma sin_le_x : forall x : R, 0 <= x -> sin x <= x.
Proof.
  intros x Hx. destruct (Req_dec x 0) as [E|E].
  - subst; rewrite sin_0; lra.
  - apply Rlt_le, sin_lt_x_pos; lra.
Qed.

Lemma arc_length_nonneg : forall r theta : R,
  0 <= r -> 0 <= theta -> 0 <= arc_length r theta.
Proof. intros r theta Hr Ht. unfold arc_length. nra. Qed.

(* Sanity: a full turn has arc length = circumference. *)
Lemma arc_length_full_turn : forall r : R, arc_length r (2 * PI) = 2 * PI * r.
Proof. intros r. unfold arc_length. ring. Qed.

(* Headline 1: the chord never exceeds the arc it subtends. *)
Theorem chord_le_arc_length : forall r theta : R,
  0 <= r -> 0 <= theta -> chord_subtended r theta <= arc_length r theta.
Proof.
  intros r theta Hr Ht. unfold chord_subtended, arc_length.
  assert (Hs : sin (theta / 2) <= theta / 2) by (apply sin_le_x; lra).
  nra.
Qed.

(* Headline 2: half-angle bridge to 1 - cos theta (hence to dot products). *)
Theorem chord_subtended_sq : forall r theta : R,
  chord_subtended r theta * chord_subtended r theta
    = 2 * (r * r) * (1 - cos theta).
Proof.
  intros r theta. unfold chord_subtended.
  assert (Hc : cos theta = 1 - 2 * sin (theta / 2) * sin (theta / 2)).
  { replace theta with (2 * (theta / 2)) at 1 by lra. apply cos_2a_sin. }
  rewrite Hc. ring.
Qed.

Print Assumptions sin_lt_x_pos.
Print Assumptions sin_le_x.
Print Assumptions chord_le_arc_length.
Print Assumptions chord_subtended_sq.

(* arc_length_of for CircularArc lives in RelateArcAnalytic.v (no cycle with arc_sweep_angle).
   This file contains only the scalar arc_length / chord_subtended foundations. *)
