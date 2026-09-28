(* ============================================================================
   NetTopologySuite.Proofs.ZetaEggBridge
   ----------------------------------------------------------------------------
   C2 (#770 build order, step 2). The ζ chart of CircleChart built from the
   host CircularEgg, in the 3-axiom lane.

   The chart comes from the egg, not the other way round.  With the egg's
   own mid angle m = θ₀ + Δθ/2, the pole is the antipode of the mid point,

     egg_pole c = O − r·(cos m, sin m),     u = O − Q = r·(cos m, sin m),

   so ζ = 0 is the arc mid and the chart point is O + rotate(u, 2·atan3 ζ).
   Then

     t_of_zeta c ζ := 1/2 + 2·atan3 ζ / Δθ.

     egg_pole_on_circle   |O − egg_pole c|² = r²
     t_of_zeta_monotone   a < b  ⇒  0 < (t(b) − t(a)) · Δθ
     circ_eval_t_of_zeta  Δθ ≠ 0  ⇒  circ_eval c (t_of_zeta c ζ) = zeta_pt O Q ζ

   No atan2.  No branch cut.  No mod 2π: θ₀ + t·Δθ = m + 2·atan3 ζ is exact
   by definition, for any stored θ₀.  The monotone lemma is signed by Δθ,
   so it has no orientation split.  Whether t lies in [0, 1] is span
   membership, which is P's job, not C2's.

   Oracle lane. Not a CircularEgg reparameterisation (not B). Does not
   remint CircGamma, leftover Ⅹ, LoopDischarged, I_ok_mixed as host, or
   MkNurbs. Does not import Atan2 (Category C).
   No Admitted. No Axiom. No Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance SheetHenCircEgg CircleChart AtanIvt.
Local Open Scope R_scope.

Definition egg_mid_angle (c : CircularEgg) : R :=
  circ_theta0 c + circ_sweep c / 2.

Definition egg_pole (c : CircularEgg) : Point :=
  mkPoint (px (circ_o c) - circ_r c * cos (egg_mid_angle c))
          (py (circ_o c) - circ_r c * sin (egg_mid_angle c)).

Definition zeta_pt (O Q : Point) (z : R) : Point :=
  mkPoint (px O + zeta_ptx (px O - px Q) (py O - py Q) z)
          (py O + zeta_pty (px O - px Q) (py O - py Q) z).

Definition t_of_zeta (c : CircularEgg) (z : R) : R :=
  / 2 + 2 * atan3 z / circ_sweep c.

Lemma egg_pole_on_circle : forall c,
  dist_sq (circ_o c) (egg_pole c) = circ_r c * circ_r c.
Proof.
  intro c. unfold dist_sq, egg_pole. simpl.
  pose proof (sin2_cos2 (egg_mid_angle c)) as E. unfold Rsqr in E.
  replace (circ_r c * circ_r c)
    with (circ_r c * circ_r c
          * (sin (egg_mid_angle c) * sin (egg_mid_angle c)
             + cos (egg_mid_angle c) * cos (egg_mid_angle c)))
    by (rewrite E; ring).
  ring.
Qed.

Lemma atan3_strict : forall a b, a < b -> atan3 a < atan3 b.
Proof.
  intros a b Hab.
  destruct (Rle_lt_or_eq_dec _ _ (atan3_le a b (Rlt_le _ _ Hab))) as [H|H].
  - exact H.
  - exfalso.
    destruct (atan3_spec a) as [Ba Sa]. destruct (atan3_spec b) as [Bb Sb].
    assert (Hc : 0 < cos (atan3 a)) by (apply cos_gt_0; lra).
    rewrite H in Sa, Hc.
    assert (a * cos (atan3 b) = b * cos (atan3 b)) by lra.
    assert (a = b).
    { apply (Rmult_eq_reg_r (cos (atan3 b))); [lra | lra]. }
    lra.
Qed.

Theorem t_of_zeta_monotone : forall c a b,
  circ_sweep c <> 0 ->
  a < b ->
  0 < (t_of_zeta c b - t_of_zeta c a) * circ_sweep c.
Proof.
  intros c a b Hs Hab. unfold t_of_zeta.
  replace ((/ 2 + 2 * atan3 b / circ_sweep c
            - (/ 2 + 2 * atan3 a / circ_sweep c)) * circ_sweep c)
    with (2 * (atan3 b - atan3 a)) by (field; exact Hs).
  pose proof (atan3_strict a b Hab). lra.
Qed.

Theorem circ_eval_t_of_zeta : forall c z,
  circ_sweep c <> 0 ->
  circ_eval c (t_of_zeta c z) = zeta_pt (circ_o c) (egg_pole c) z.
Proof.
  intros c z Hs.
  assert (Hang : circ_theta0 c + t_of_zeta c z * circ_sweep c
                 = egg_mid_angle c + 2 * atan3 z).
  { unfold t_of_zeta, egg_mid_angle. field. exact Hs. }
  assert (Hz : 0 < 1 + z * z) by nra.
  unfold circ_eval, zeta_pt, egg_pole. simpl. rewrite Hang.
  set (m := egg_mid_angle c).
  replace (px (circ_o c) - (px (circ_o c) - circ_r c * cos m))
    with (circ_r c * cos m) by ring.
  replace (py (circ_o c) - (py (circ_o c) - circ_r c * sin m))
    with (circ_r c * sin m) by ring.
  f_equal.
  - rewrite cos_plus, cos_2_atan3, sin_2_atan3. unfold zeta_ptx.
    field. lra.
  - rewrite sin_plus, cos_2_atan3, sin_2_atan3. unfold zeta_pty.
    field. lra.
Qed.

Print Assumptions egg_pole_on_circle.
Print Assumptions t_of_zeta_monotone.
Print Assumptions circ_eval_t_of_zeta.
