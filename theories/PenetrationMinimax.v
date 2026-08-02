(* ============================================================================
   NetTopologySuite.Proofs.PenetrationMinimax
   ----------------------------------------------------------------------------
   Wen & Zhang, "A Minimax Model for Generalized Penetration Distance
   Between Convex Sets by Directed Hausdorff Distance", IEEE RA-L
   7(3):6123-6130, 2022 (doi:10.1109/LRA.2022.3166111).
   Part 2: THE PENETRATION DEPTH IS THE LARGEST ZERO OF A CONVEX
   FUNCTION, AND THE SECANT METHOD IS SAFE (paper eqs (9)-(13),
   Theorems 1-2), pinned on the exactly-solvable box instance.

   The paper's pipeline: for overlapping bodies A, B, the generalized
   penetration depth p_F(A,B) is the largest dilation lam of the gauge
   set F still inscribed in the Minkowski difference C = A (-) B
   (eq (9)); inclusion is detected by the directed Hausdorff distance,
   lam*F included in C  <->  h(lam*F, C) = 0 (eq (10)); so p_F is the
   LARGEST ZERO of f(lam) := h(lam*F, C) (eq (11)), a nonnegative,
   nondecreasing, convex "black-box" function (Theorem 1) that the
   secant iteration of Algorithm 1 brackets from above without ever
   undershooting (Theorem 2).  In a collision-response loop an
   undershoot is a real failure: the solver would report the bodies
   separated while they still overlap.

   What is proved here, in three layers:

   (a) MINKOWSKI LAYER (eq (1)-(2) color).  interval_minkowski_diff:
       the 1D Minkowski difference of two origin-centred intervals
       [-s,s] (-) [-u,u] is exactly [-(s+u), s+u] -- so for two
       axis-aligned origin-centred boxes the separating-translation
       budget really is s+u per axis, the crate-overlap depth every
       axis-aligned broadphase computes.

   (b) MODEL LAYER (eqs (9)-(11) on the box instance).  For
       C = [-c,c]^2 and F the unit sup-ball, the penetration profile is
       f_box c lam = max(0, lam - c):
         f_box_nonneg / f_box_nondecreasing / f_box_convex = Theorem 1
           (nondecreasing is also paper Lemma 1(i): h(lam*F, C) grows
           with the dilation since lam*F only gains points);
         box_inclusion_iff_le + f_box_zero_iff + box_inclusion_iff_fzero
           = the eq (10) equivalence "inclusion <-> h = 0 <-> lam <= c";
         the largest zero is c, the inscribed sup-ball radius = eq (9).

   (c) SECANT LAYER (Theorem 2, eqs (12)-(13)).  Abstract over ANY f
       satisfying the convexity inequality:
         convex_three_point: the cleared three-slope inequality
           f(b)(c-a) <= f(a)(c-b) + f(c)(b-a) for a < b < c;
         secant_step_safe: from lstar < l1 < l0 with f(lstar) = 0 and
           f(l1) > 0, the secant iterate stays in [lstar, l1) -- the
           monotone-decreasing, never-undershooting bracket of
           Theorem 2.  (The strict slope gap f(l1) < f(l0) is DERIVED
           from convexity, not assumed.)
       On the box instance f is affine right of its zero, so ONE secant
       step lands exactly on lam* (secant_one_step_exact); the rational
       pin runs the paper's own initialisation lam0 = 200 (Section IV)
       with c = 2 and hits 2 on the nose (secant_pin_paper_init).

   All rational; no sqrt, no limits, no inner minimax solver -- the
   PDHG recursion (16) and the continuity clause of Theorem 1 are NOT
   formalised (honest scope; see docs/hausdorff-penetration.md).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Minkowski layer: interval difference is the sum of half-widths.        *)
(* -------------------------------------------------------------------------- *)

(* [-s,s] (-) [-u,u] = [-(s+u), s+u]: z is a difference a - b of points of
   the two intervals iff |z| <= s + u.  The witness for the backward
   direction is the clamp of z to [-s,s] (rational whenever z is). *)
Lemma interval_minkowski_diff : forall s u z,
    0 <= s -> 0 <= u ->
    ((exists a b, Rabs a <= s /\ Rabs b <= u /\ z = a - b) <->
     Rabs z <= s + u).
Proof.
  intros s u z Hs Hu. split.
  - intros [a [b [Ha [Hb ->]]]].
    unfold Rabs in *;
      repeat match goal with
             | |- context [Rcase_abs ?t] => destruct (Rcase_abs t)
             | H : context [Rcase_abs ?t] |- _ => destruct (Rcase_abs t)
             end; lra.
  - intros Hz.
    exists (Rmax (- s) (Rmin s z)), (Rmax (- s) (Rmin s z) - z).
    unfold Rmax, Rmin, Rabs in *;
      repeat match goal with
             | |- context [Rle_dec ?a ?b] => destruct (Rle_dec a b)
             | H : context [Rle_dec ?a ?b] |- _ => destruct (Rle_dec a b)
             | |- context [Rcase_abs ?t] => destruct (Rcase_abs t)
             | H : context [Rcase_abs ?t] |- _ => destruct (Rcase_abs t)
             end;
      repeat split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Model layer: the box penetration profile f(lam) = h(lam*F, C) for      *)
(*     F = unit sup-ball, C = [-c,c]^2, in closed form: max(0, lam - c).      *)
(* -------------------------------------------------------------------------- *)

Definition f_box (c lam : R) : R := Rmax 0 (lam - c).

(* Theorem 1, nonnegativity clause. *)
Lemma f_box_nonneg : forall c lam, 0 <= f_box c lam.
Proof. intros. unfold f_box. apply Rmax_l. Qed.

(* Theorem 1, monotonicity clause -- also paper Lemma 1(i) in this model:
   enlarging the dilation lam*F can only increase its excess over C. *)
Lemma f_box_nondecreasing : forall c l l', l <= l' -> f_box c l <= f_box c l'.
Proof.
  intros c l l' H. unfold f_box, Rmax.
  destruct (Rle_dec 0 (l - c)); destruct (Rle_dec 0 (l' - c)); lra.
Qed.

(* Theorem 1, convexity clause (as the standard convexity inequality). *)
Lemma f_box_convex : forall c a b t,
    0 <= t <= 1 ->
    f_box c (t * a + (1 - t) * b) <= t * f_box c a + (1 - t) * f_box c b.
Proof.
  intros c a b t Ht. unfold f_box, Rmax.
  repeat match goal with
         | |- context [Rle_dec ?x ?y] => destruct (Rle_dec x y)
         end; nra.
Qed.

(* eq (10), value side: f hits zero exactly up to the inscribed radius c --
   the largest zero of f_box c is c, which is eq (9)'s p_F for this model. *)
Lemma f_box_zero_iff : forall c lam, f_box c lam = 0 <-> lam <= c.
Proof.
  intros c lam. unfold f_box, Rmax.
  destruct (Rle_dec 0 (lam - c)); split; intros; lra.
Qed.

(* eq (10), inclusion side: the dilated sup-ball lam*F sits inside C
   exactly when lam <= c (lam, c >= 0). *)
Lemma box_inclusion_iff_le : forall c lam,
    0 <= lam -> 0 <= c ->
    ((forall x y, Rabs x <= lam -> Rabs y <= lam ->
                  Rabs x <= c /\ Rabs y <= c)
     <-> lam <= c).
Proof.
  intros c lam Hl Hc. split.
  - intros Hinc.
    assert (Hll : Rabs lam <= lam) by (rewrite Rabs_pos_eq; lra).
    assert (H0l : Rabs 0 <= lam) by (rewrite Rabs_R0; lra).
    destruct (Hinc lam 0 Hll H0l) as [Hx _].
    rewrite Rabs_pos_eq in Hx; lra.
  - intros Hle x y Hx Hy. split; lra.
Qed.

(* eq (10) assembled: inclusion <-> the penetration profile vanishes. *)
Lemma box_inclusion_iff_fzero : forall c lam,
    0 <= lam -> 0 <= c ->
    ((forall x y, Rabs x <= lam -> Rabs y <= lam ->
                  Rabs x <= c /\ Rabs y <= c)
     <-> f_box c lam = 0).
Proof.
  intros c lam Hl Hc.
  pose proof (box_inclusion_iff_le c lam Hl Hc).
  pose proof (f_box_zero_iff c lam).
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Secant layer: Theorem 2's never-undershoot guarantee, from the         *)
(*     convexity inequality alone.                                            *)
(* -------------------------------------------------------------------------- *)

Section SecantSafety.

  Variable f : R -> R.
  Hypothesis f_convex : forall a b t,
      0 <= t <= 1 ->
      f (t * a + (1 - t) * b) <= t * f a + (1 - t) * f b.

  (* The cleared three-slope inequality: for a < b < c the chord over
     [a,c] lies above f at b.  This is eq (12) with denominators
     multiplied out, so no division discipline is needed downstream. *)
  Lemma convex_three_point : forall a b c,
      a < b < c ->
      f b * (c - a) <= f a * (c - b) + f c * (b - a).
  Proof.
    intros a b c [Hab Hbc].
    assert (Hca : 0 < c - a) by lra.
    set (t := (c - b) / (c - a)).
    assert (Ht0 : 0 <= t).
    { unfold t, Rdiv. apply Rmult_le_pos; [ lra | ].
      left. apply Rinv_0_lt_compat. lra. }
    assert (Ht1 : t <= 1).
    { unfold t. apply (Rmult_le_reg_r (c - a)); [ lra | ].
      replace ((c - b) / (c - a) * (c - a)) with (c - b) by (field; lra).
      lra. }
    assert (Hb : b = t * a + (1 - t) * c) by (unfold t; field; lra).
    pose proof (f_convex a c t (conj Ht0 Ht1)) as Hc.
    rewrite <- Hb in Hc.
    assert (Hc' : f b * (c - a) <= (t * f a + (1 - t) * f c) * (c - a))
      by (apply Rmult_le_compat_r; [ lra | exact Hc ]).
    replace ((t * f a + (1 - t) * f c) * (c - a))
      with (f a * (c - b) + f c * (b - a)) in Hc'
      by (unfold t; field; lra).
    exact Hc'.
  Qed.

  (* Theorem 2's induction core (eq (13)): with the true root lstar below
     the current bracket lstar < l1 < l0 and f(l1) > 0, the secant step
       l2 = l1 - (l1 - l0) / (f l1 - f l0) * f l1
     is strictly below l1 and never undershoots lstar.  The denominator
     is alive because convexity FORCES f l1 < f l0 (derived, not
     assumed).  For collision response: the solver's depth estimate
     decreases monotonically but never reports "separated" early. *)
  Lemma secant_step_safe : forall lstar l1 l0,
      f lstar = 0 ->
      lstar < l1 < l0 ->
      0 < f l1 ->
      lstar <= l1 - (l1 - l0) / (f l1 - f l0) * f l1 < l1.
  Proof.
    intros lstar l1 l0 Hz [H1 H0] Hpos.
    pose proof (convex_three_point lstar l1 l0 (conj H1 H0)) as Hm.
    rewrite Hz in Hm.
    assert (Hm' : f l1 * (l0 - lstar) <= f l0 * (l1 - lstar)) by lra.
    assert (Hlt : f l1 < f l0).
    { destruct (Rlt_or_le (f l1) (f l0)) as [Hlt | Hge]; [ exact Hlt | ].
      exfalso. nra. }
    assert (HD : f l1 - f l0 < 0) by lra.
    split.
    - apply (Rmult_le_reg_r (f l0 - f l1)); [ lra | ].
      replace ((l1 - (l1 - l0) / (f l1 - f l0) * f l1) * (f l0 - f l1))
        with (l1 * (f l0 - f l1) + (l1 - l0) * f l1)
        by (field; lra).
      nra.
    - assert (Hq : 0 < (l1 - l0) / (f l1 - f l0)).
      { replace ((l1 - l0) / (f l1 - f l0))
          with ((l0 - l1) / (f l0 - f l1)) by (field; lra).
        apply Rdiv_lt_0_compat; lra. }
      nra.
  Qed.

End SecantSafety.

(* -------------------------------------------------------------------------- *)
(* §4  Exact secant pins on the box instance.                                 *)
(* -------------------------------------------------------------------------- *)

(* Right of its largest zero the box profile is affine: f = lam - c. *)
Lemma f_box_affine_above : forall c lam, c <= lam -> f_box c lam = lam - c.
Proof. intros c lam H. unfold f_box. apply Rmax_right. lra. Qed.

(* On an affine stretch the secant is exact: one step from any bracket
   c < l1 < l0 lands exactly on the penetration depth c. *)
Lemma secant_one_step_exact : forall c l1 l0,
    c < l1 < l0 ->
    l1 - (l1 - l0) / (f_box c l1 - f_box c l0) * f_box c l1 = c.
Proof.
  intros c l1 l0 [H1 H0].
  rewrite !f_box_affine_above by lra.
  field. lra.
Qed.

(* Rational pin with the paper's own Section-IV initialisation lam0 = 200
   (and lam1 = 190 < lam0): for depth c = 2 the first secant iterate is
   exactly 2.  Algorithm 1 with exact arithmetic terminates immediately
   on box-vs-box -- the interesting cases are the curved ones. *)
Lemma secant_pin_paper_init :
  190 - (190 - 200) / (f_box 2 190 - f_box 2 200) * f_box 2 190 = 2.
Proof. apply secant_one_step_exact. lra. Qed.

(* The box profile satisfies the abstract secant-safety interface: the
   composition below is Theorem 2 instantiated at the model of §2, with
   the paper's initialisation bracket. *)
Lemma secant_box_never_undershoots : forall c l1 l0,
    0 <= c -> c < l1 < l0 ->
    c <= l1 - (l1 - l0) / (f_box c l1 - f_box c l0) * f_box c l1 < l1.
Proof.
  intros c l1 l0 Hc [H1 H0].
  apply (secant_step_safe (f_box c) (f_box_convex c)).
  - apply f_box_zero_iff. lra.
  - lra.
  - rewrite f_box_affine_above by lra. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions interval_minkowski_diff.
Print Assumptions secant_step_safe.
Print Assumptions secant_box_never_undershoots.
