(* ============================================================================
   NetTopologySuite.Proofs.ClothoidFresnel
   ----------------------------------------------------------------------------
   Issue #564 / claimId 508-e: instantiate the #561 speed-integral pack
   on the genuine Fresnel clothoid

     g(t) = (Cx t, Cy t)
     Cx' = cos(t²/2)    Cy' = sin(t²/2)

   Route 1 does not construct the Fresnel integrals (no Coquelicot /
   RInt; ADR-0001 route D stays consumer-gated). This letter discharges
   the two analytic pack premises at unit speed σ ≡ 1,
   F = fun t => 1 * t (matches constant_speed_premises; not bare id):

     uniformly_continuous_on (fun _ => 1)          (constant; free)
     increment_squeezed (fun t => 1 * t) (fun _ => 1)
     chord_rate_tight (fresnel_curve Cx Cy) (fun _ => 1)

   The remaining Technique-park hypothesis is that Cx, Cy are primitives
   of the Fresnel integrands (increment_squeezed). The heading t²/2 is
   Lipschitz on any compact window, so a fine gap makes the increment
   a first-order match to the unit velocity and the chord realizes the
   gap. Then

     fresnel_primitives Cx Cy a b
       → is_curve_length (fresnel_curve Cx Cy) a b (b − a).

   Witness: any such primitives on the [0, 1] window have metric
   length exactly 1. The same premises discharge ClothoidLength.v's
   H_unit_chord / H_unit_approx (never globally — the Euler spiral
   wraps). ClothoidLength_unit.v's straight-line inhabitant stays;
   this is the first curved instance.

   Windowing is essential. Do not strengthen to all of R.
   No CurveSegment growth, no ADR-0004 remint, no TRIAGE flip.
   No Heine–Cantor. No `Admitted`, no `Axiom`, no `Parameter`.  3-axiom.

   Flocq association (same pins as EllipseSpeedIntegral.v):
   [rewrite (Rabs_right 2)] needs a subterm [Rabs 2]. Left-associated
   [2 * sin * sin] becomes [Rabs (2 * sin)] after one [Rabs_mult].
   Parenthesize [2 * (sin * sin)]. Same for heading
   [((t-s)*(t+s))*/2]: Rabs_mult first, then [Rabs_right (/2)],
   then Rabs_mult to expose [Rabs (t-s)]. Do not [field] those
   scales — cancel with [Rinv_r] / [Rinv_l].
   CI death on 7bbdee1 L161: [Rabs_right 2] with no [Rabs 2].
   CI death on e0dc2b1 L272: [Rabs_minus_sym heading s t] looks for
   [Rabs (hs − ht)]; the leftover after [cos_abs_lipschitz] is already
   [Rabs (ht − hs)]. Apply [fresnel_heading_lipschitz] directly.
   CI death on e4ef3d9 L325: nested [lra] inside [Rmult_le_pos]
   cannot find a witness for [0 <= t-s]. Pose [Hgap0] first and
   pass it as [exact]; expand [(σ±K*gap)*gap] with [sub_mul_distr]
   / [add_mul_distr], not [ring]. Same class: [1*(t-s)] is
   [Rmult_1_l], and [e * sqrt 2 = K * gap * gap] is [Rmult_comm]
   / [Rmult_assoc], not [ring].
   CI death on bb7888f L365: [fresnel_vx_lipschitz] yields
   [M*(u-s)]; [increment_tracks_left] asks for the uniform
   [M*(t-s)]. Lift with [Rmult_le_compat_l] and [u<=t].
   CI death on df7e564 L427: [rewrite <- Rsqr_neg] looks for
   [(- (x-y))²]; the goal is still a product. Fold both
   sides to [Rsqr] first, then [opp_minus] + [Rsqr_neg].
   CI death on 3929a26 L451: binder [by] is a vernacular
   keyword ([forall ax ay bx by]). Rename the fourth
   coordinate to [cy].
   CI death on b1fa7ac L438: [symmetry; apply Rsqr_neg] looks
   for [x² = (-x)²] against [(-(x-y))² = (x-y)²]. Do not
   use [Rsqr_neg]; expand [(-d)*(-d)] with [Ropp_mult_distr].
   CI death on 2e24a57 L436: [Ropp_mult_distr_l] / unary minus
   notation does not expose [- ((x-y)*-(x-y))]. Use
   [eq_sym (Rmult_opp_opp d d)] instead of rewriting.
   CI death on bcf6ac9 L521: [apply Rabs_right] is
   [Rabs r = r], goal is [x*x = Rabs (x*x)]. Rewrite
   [Rabs_right] on the product, then [reflexivity].
   CI death on f4b6f90 L599: [replace (1*(t-s))] misses
   [(fun _ => 1) s * (t-s)]; [rewrite <- fresnel_vel_chord]
   then leaves [1 * dist]. [change] the constant function
   to [1], [rewrite Rmult_1_l], [fold gap] first.
   CI death on 1a2063b L645: a global [rewrite <- fresnel_vel_chord]
   after [fold gap] rewrites every [gap], including the
   contract RHS [eps * gap], so the leftover is
   [K * gap * gap <= eps * dist origin vel] and
   [Rmult_le_compat_r] cannot unify [dist] with [gap].
   Rewrite the subtracted occurrence only ([at 1]);
   the factor on [eps] stays [gap].
   CI death on 12a6ed7 L713: [replace 1 with (1-0)] rewrites
   every [1], including the window endpoint, so the leftover
   is [is_curve_length g 0 (1-0) (1-0)] and apply cannot
   unify [1] with [1-0]. Pose [fresnel_is_curve_length]
   first; [rewrite Rminus_0_r] on the length only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveLength ArcRectifiable
                               SpeedIntegral ClothoidLength.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Fresnel heading and integrands.                                            *)
(* -------------------------------------------------------------------------- *)

Definition fresnel_heading (t : R) : R := (t * t) / 2.

Definition fresnel_vx (t : R) : R := cos (fresnel_heading t).
Definition fresnel_vy (t : R) : R := sin (fresnel_heading t).

Definition fresnel_curve (Cx Cy : R -> R) : Curve :=
  fun t => mkPoint (Cx t) (Cy t).

Definition fresnel_primitives (Cx Cy : R -> R) (a b : R) : Prop :=
  increment_squeezed Cx fresnel_vx a b /\
  increment_squeezed Cy fresnel_vy a b.

Definition fresnel_window_lip (a b : R) : R :=
  Rmax (Rabs a) (Rabs b).

Lemma fresnel_unit_speed : forall t,
  fresnel_vx t * fresnel_vx t + fresnel_vy t * fresnel_vy t = 1.
Proof.
  intros t.
  unfold fresnel_vx, fresnel_vy.
  pose proof (sin2_cos2 (fresnel_heading t)) as H.
  unfold Rsqr in H.
  rewrite (Rplus_comm (sin _ * sin _) (cos _ * cos _)) in H.
  exact H.
Qed.

Lemma fresnel_window_lip_nonneg : forall a b,
  0 <= fresnel_window_lip a b.
Proof.
  intros a b. unfold fresnel_window_lip.
  apply (Rle_trans 0 (Rabs a)); [apply Rabs_pos | apply Rmax_l].
Qed.

Lemma abs_in_window : forall a b t,
  a <= t -> t <= b ->
  Rabs t <= fresnel_window_lip a b.
Proof.
  intros a b t Hat Htb.
  unfold fresnel_window_lip.
  destruct (Rle_dec 0 t) as [Ht0 | Htn].
  - rewrite (Rabs_right t) by lra.
    apply (Rle_trans t (Rabs b) (Rmax (Rabs a) (Rabs b))).
    + assert (0 <= b) by lra.
      rewrite (Rabs_right b) by lra. exact Htb.
    + apply Rmax_r.
  - rewrite (Rabs_left t) by lra.
    apply (Rle_trans (- t) (Rabs a) (Rmax (Rabs a) (Rabs b))).
    + assert (a < 0) by lra.
      rewrite (Rabs_left a) by lra. lra.
    + apply Rmax_l.
Qed.

(* -------------------------------------------------------------------------- *)
(* Trig Lipschitz (local copies; do not import EllipseSpeedIntegral).         *)
(* -------------------------------------------------------------------------- *)

Lemma cos_s_minus_cos_t : forall s t,
  cos s - cos t
  = 2 * (sin ((s + t) / 2) * sin ((t - s) / 2)).
Proof.
  intros s t.
  transitivity
    (cos ((s + t) / 2 - (t - s) / 2)
     - cos ((s + t) / 2 + (t - s) / 2)).
  - f_equal; [f_equal | f_equal]; field.
  - rewrite cos_minus, cos_plus. ring.
Qed.

Lemma sin_s_minus_sin_t : forall s t,
  sin s - sin t
  = - (2 * (cos ((s + t) / 2) * sin ((t - s) / 2))).
Proof.
  intros s t.
  transitivity
    (sin ((s + t) / 2 - (t - s) / 2)
     - sin ((s + t) / 2 + (t - s) / 2)).
  - f_equal; [f_equal | f_equal]; field.
  - rewrite sin_minus, sin_plus. ring.
Qed.

Lemma cos_abs_le_1 : forall x, Rabs (cos x) <= 1.
Proof.
  intros x.
  rewrite <- (Rabs_right 1) by lra.
  apply Rsqr_le_abs_0.
  unfold Rsqr.
  pose proof (sin2_cos2 x) as Hsc. unfold Rsqr in Hsc.
  pose proof (sqr_nonneg (sin x)) as Hs. unfold Rsqr in Hs.
  lra.
Qed.

Lemma Rabs_sin_le_abs : forall x,
  Rabs (sin x) <= Rabs x.
Proof.
  intros x.
  destruct (Rle_dec 0 x) as [Hx | Hn].
  - rewrite (Rabs_right x) by lra. apply Rabs_sin_le. exact Hx.
  - rewrite (Rabs_left1 x) by lra.
    rewrite <- (Rabs_Ropp (sin x)).
    rewrite <- sin_neg.
    apply Rabs_sin_le. lra.
Qed.

Lemma cos_abs_lipschitz : forall a b,
  Rabs (cos a - cos b) <= Rabs (a - b).
Proof.
  intros a b.
  rewrite cos_s_minus_cos_t.
  rewrite Rabs_mult.
  rewrite (Rabs_right 2) by lra.
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [lra |].
    rewrite Rabs_mult.
    apply Rmult_le_compat_r; [apply Rabs_pos |].
    pose proof (SIN_bound ((a + b) / 2)) as Hs.
    apply Rabs_le. exact Hs.
  - rewrite Rmult_1_l.
    eapply Rle_trans.
    + apply Rmult_le_compat_l; [lra |].
      apply Rabs_sin_le_abs.
    + unfold Rdiv.
      rewrite Rabs_mult.
      rewrite (Rabs_right (/ 2)) by lra.
      rewrite (Rabs_minus_sym b a).
      replace (2 * (Rabs (a - b) * / 2)) with (Rabs (a - b)).
      2:{ rewrite <- Rmult_assoc.
          rewrite (Rmult_comm 2 (Rabs (a - b))).
          rewrite Rmult_assoc.
          rewrite Rinv_r by lra.
          rewrite Rmult_1_r.
          reflexivity. }
      apply Rle_refl.
Qed.

Lemma sin_abs_lipschitz : forall a b,
  Rabs (sin a - sin b) <= Rabs (a - b).
Proof.
  intros a b.
  rewrite sin_s_minus_sin_t.
  rewrite Rabs_Ropp.
  rewrite Rabs_mult.
  rewrite (Rabs_right 2) by lra.
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [lra |].
    rewrite Rabs_mult.
    apply Rmult_le_compat_r; [apply Rabs_pos |].
    apply cos_abs_le_1.
  - rewrite Rmult_1_l.
    eapply Rle_trans.
    + apply Rmult_le_compat_l; [lra |].
      apply Rabs_sin_le_abs.
    + unfold Rdiv.
      rewrite Rabs_mult.
      rewrite (Rabs_right (/ 2)) by lra.
      rewrite (Rabs_minus_sym b a).
      replace (2 * (Rabs (a - b) * / 2)) with (Rabs (a - b)).
      2:{ rewrite <- Rmult_assoc.
          rewrite (Rmult_comm 2 (Rabs (a - b))).
          rewrite Rmult_assoc.
          rewrite Rinv_r by lra.
          rewrite Rmult_1_r.
          reflexivity. }
      apply Rle_refl.
Qed.

Lemma fresnel_heading_diff : forall s t,
  fresnel_heading t - fresnel_heading s = (t - s) * (t + s) / 2.
Proof.
  intros s t. unfold fresnel_heading, Rdiv. ring.
Qed.

Lemma fresnel_heading_lipschitz : forall a b s t,
  a <= s -> s <= t -> t <= b ->
  Rabs (fresnel_heading t - fresnel_heading s)
  <= fresnel_window_lip a b * (t - s).
Proof.
  intros a b s t Has Hst Htb.
  rewrite fresnel_heading_diff.
  unfold Rdiv.
  set (M := fresnel_window_lip a b).
  assert (HM : 0 <= M) by (unfold M; apply fresnel_window_lip_nonneg).
  assert (HsM : Rabs s <= M) by (unfold M; apply abs_in_window; lra).
  assert (HtM : Rabs t <= M) by (unfold M; apply abs_in_window; lra).
  rewrite Rabs_mult.
  rewrite (Rabs_right (/ 2)) by lra.
  rewrite Rabs_mult.
  rewrite (Rabs_right (t - s)) by lra.
  apply (Rle_trans _ ((t - s) * (Rabs t + Rabs s) * / 2)).
  - apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra |].
    apply Rmult_le_compat_l; [lra |].
    apply Rabs_triang.
  - apply (Rle_trans _ ((t - s) * (M + M) * / 2)).
    + apply Rmult_le_compat_r; [apply Rlt_le, Rinv_0_lt_compat; lra |].
      apply Rmult_le_compat_l; [lra |].
      apply Rplus_le_compat; [exact HtM | exact HsM].
    + replace (M + M) with (M * 2) by ring.
      rewrite (Rmult_assoc (t - s) (M * 2) (/ 2)).
      rewrite (Rmult_assoc M 2 (/ 2)).
      rewrite Rinv_r by lra.
      rewrite Rmult_1_r.
      rewrite (Rmult_comm (t - s) M).
      apply Rle_refl.
Qed.

Lemma fresnel_vx_lipschitz : forall a b s t,
  a <= s -> s <= t -> t <= b ->
  Rabs (fresnel_vx t - fresnel_vx s)
  <= fresnel_window_lip a b * (t - s).
Proof.
  intros a b s t Has Hst Htb.
  unfold fresnel_vx.
  eapply Rle_trans; [apply cos_abs_lipschitz |].
  apply fresnel_heading_lipschitz; assumption.
Qed.

Lemma fresnel_vy_lipschitz : forall a b s t,
  a <= s -> s <= t -> t <= b ->
  Rabs (fresnel_vy t - fresnel_vy s)
  <= fresnel_window_lip a b * (t - s).
Proof.
  intros a b s t Has Hst Htb.
  unfold fresnel_vy.
  eapply Rle_trans; [apply sin_abs_lipschitz |].
  apply fresnel_heading_lipschitz; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Increment of a primitive tracks the left-endpoint integrand.               *)
(* -------------------------------------------------------------------------- *)

Lemma rabs_of_two_sided : forall x c e,
  0 <= e ->
  c - e <= x <= c + e ->
  Rabs (x - c) <= e.
Proof.
  intros x c e He [Hlo Hhi].
  destruct (Rle_dec 0 (x - c)) as [Hpos | Hneg].
  - rewrite (Rabs_right (x - c)) by lra. lra.
  - rewrite (Rabs_left (x - c)) by lra. lra.
Qed.

Lemma sub_mul_distr : forall x y z,
  (x - y) * z = x * z - y * z.
Proof.
  intros x y z.
  unfold Rminus.
  rewrite Rmult_plus_distr_r.
  rewrite Ropp_mult_distr_l.
  reflexivity.
Qed.

Lemma add_mul_distr : forall x y z,
  (x + y) * z = x * z + y * z.
Proof.
  intros x y z. apply Rmult_plus_distr_r.
Qed.

Lemma increment_tracks_left :
  forall F σ a b s t K,
    increment_squeezed F σ a b ->
    0 <= K ->
    a <= s -> s <= t -> t <= b ->
    (forall u, s <= u -> u <= t -> Rabs (σ u - σ s) <= K * (t - s)) ->
    Rabs (F t - F s - σ s * (t - s)) <= K * (t - s) * (t - s).
Proof.
  intros F σ a b s t K Hsq HK Has Hst Htb Hlip.
  set (gap := t - s).
  set (lo := σ s - K * gap).
  set (hi := σ s + K * gap).
  assert (Hgap0 : 0 <= gap) by (unfold gap; lra).
  assert (Hbd : forall u, s <= u -> u <= t -> lo <= σ u <= hi).
  { intros u Hus Hut.
    specialize (Hlip u Hus Hut).
    apply rabs_le_both in Hlip.
    unfold lo, hi, gap in *. lra. }
  pose proof (Hsq s t lo hi Has Hst Htb Hbd) as Hinc.
  unfold lo, hi, gap in Hinc.
  rewrite sub_mul_distr, add_mul_distr in Hinc.
  apply (rabs_of_two_sided (F t - F s) (σ s * (t - s))
           (K * (t - s) * (t - s))).
  - apply Rmult_le_pos; [apply Rmult_le_pos; [exact HK | exact Hgap0] | exact Hgap0].
  - exact Hinc.
Qed.

Lemma fresnel_Cx_tracks : forall Cx Cy a b s t,
  fresnel_primitives Cx Cy a b ->
  a <= s -> s <= t -> t <= b ->
  Rabs (Cx t - Cx s - fresnel_vx s * (t - s))
  <= fresnel_window_lip a b * (t - s) * (t - s).
Proof.
  intros Cx Cy a b s t [Hx _] Has Hst Htb.
  apply (increment_tracks_left Cx fresnel_vx a b s t
           (fresnel_window_lip a b) Hx
           (fresnel_window_lip_nonneg a b) Has Hst Htb).
  intros u Hus Hut.
  eapply Rle_trans.
  - apply (fresnel_vx_lipschitz a b s u Has Hus).
    apply (Rle_trans u t b Hut Htb).
  - apply Rmult_le_compat_l.
    + apply fresnel_window_lip_nonneg.
    + lra.
Qed.

Lemma fresnel_Cy_tracks : forall Cx Cy a b s t,
  fresnel_primitives Cx Cy a b ->
  a <= s -> s <= t -> t <= b ->
  Rabs (Cy t - Cy s - fresnel_vy s * (t - s))
  <= fresnel_window_lip a b * (t - s) * (t - s).
Proof.
  intros Cx Cy a b s t [_ Hy] Has Hst Htb.
  apply (increment_tracks_left Cy fresnel_vy a b s t
           (fresnel_window_lip a b) Hy
           (fresnel_window_lip_nonneg a b) Has Hst Htb).
  intros u Hus Hut.
  eapply Rle_trans.
  - apply (fresnel_vy_lipschitz a b s u Has Hus).
    apply (Rle_trans u t b Hut Htb).
  - apply Rmult_le_compat_l.
    + apply fresnel_window_lip_nonneg.
    + lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Euclidean comparison: | |p| − |q| | ≤ |p − q|.                             *)
(* -------------------------------------------------------------------------- *)

Lemma dist_abs_diff : forall p q r,
  Rabs (dist p q - dist p r) <= dist q r.
Proof.
  intros p q r.
  destruct (Rle_dec 0 (dist p q - dist p r)) as [Hpos | Hneg].
  - rewrite (Rabs_right (dist p q - dist p r)) by lra.
    pose proof (dist_triangle p r q) as Htr.
    rewrite (dist_sym r q) in Htr.
    lra.
  - rewrite (Rabs_left (dist p q - dist p r)) by lra.
    pose proof (dist_triangle p q r) as Htr.
    lra.
Qed.

Lemma opp_minus : forall x y, y - x = - (x - y).
Proof.
  intros x y.
  unfold Rminus.
  rewrite Ropp_plus_distr.
  rewrite Ropp_involutive.
  apply Rplus_comm.
Qed.

Lemma sq_minus_comm : forall x y,
  (x - y) * (x - y) = (y - x) * (y - x).
Proof.
  intros x y.
  rewrite (opp_minus x y).
  apply (eq_sym (Rmult_opp_opp (x - y) (x - y))).
Qed.

Lemma fresnel_chord_as_origin : forall Cx Cy s t,
  dist (fresnel_curve Cx Cy s) (fresnel_curve Cx Cy t)
  = dist (mkPoint 0 0) (mkPoint (Cx t - Cx s) (Cy t - Cy s)).
Proof.
  intros Cx Cy s t.
  unfold fresnel_curve, dist.
  rewrite dist_sq_general.
  rewrite dist_sq_pythagorean.
  f_equal.
  rewrite (sq_minus_comm (Cx s) (Cx t)).
  rewrite (sq_minus_comm (Cy s) (Cy t)).
  reflexivity.
Qed.

Lemma dist_of_coords : forall ax ay cx cy,
  dist (mkPoint ax ay) (mkPoint cx cy)
  = sqrt ((ax - cx) * (ax - cx) + (ay - cy) * (ay - cy)).
Proof.
  intros ax ay cx cy. unfold dist, dist_sq. simpl. reflexivity.
Qed.

Lemma prod_sqr_nonneg : forall x, 0 <= x * x.
Proof.
  intros x. pose proof (Rle_0_sqr x) as H. unfold Rsqr in H. exact H.
Qed.

(* Flocq [ring] has already refused similar factorizations in
   EllipseSpeedIntegral.v. Expand [(v*g)*(v*g)] by hand. *)
Lemma sq_scale : forall v g,
  v * g * (v * g) = (v * v) * (g * g).
Proof.
  intros v g.
  transitivity (Rsqr (v * g)).
  - unfold Rsqr. reflexivity.
  - rewrite Rsqr_mult. unfold Rsqr. reflexivity.
Qed.

Lemma two_sq : forall e, e * e + e * e = 2 * (e * e).
Proof.
  intros e.
  replace 2 with (1 + 1) by ring.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_1_l.
  reflexivity.
Qed.

Lemma fresnel_vel_chord : forall s gap,
  0 <= gap ->
  dist (mkPoint 0 0) (mkPoint (fresnel_vx s * gap) (fresnel_vy s * gap))
  = gap.
Proof.
  intros s gap Hg.
  unfold dist.
  rewrite dist_sq_pythagorean.
  rewrite (sq_scale (fresnel_vx s) gap).
  rewrite (sq_scale (fresnel_vy s) gap).
  rewrite <- Rmult_plus_distr_r.
  rewrite fresnel_unit_speed.
  rewrite Rmult_1_l.
  rewrite sqrt_square by exact Hg.
  reflexivity.
Qed.

Lemma sqrt_two_of_sq : forall e,
  0 <= e ->
  sqrt (e * e + e * e) = e * sqrt 2.
Proof.
  intros e He.
  rewrite two_sq.
  rewrite sqrt_mult; [| lra | apply prod_sqr_nonneg].
  replace (e * e) with (Rsqr e) by (unfold Rsqr; reflexivity).
  rewrite sqrt_Rsqr by exact He.
  apply Rmult_comm.
Qed.

Lemma abs_mul_self : forall x, x * x = Rabs x * Rabs x.
Proof.
  intros x.
  rewrite <- Rabs_mult.
  rewrite (Rabs_right (x * x)).
  2:{ apply Rle_ge. apply prod_sqr_nonneg. }
  reflexivity.
Qed.

Lemma sq_le_of_abs : forall x e,
  0 <= e ->
  Rabs x <= e ->
  x * x <= e * e.
Proof.
  intros x e He Hx.
  rewrite (abs_mul_self x).
  rewrite (abs_mul_self e).
  rewrite (Rabs_right e) by (apply Rle_ge; exact He).
  apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hx | exact Hx].
Qed.

(* -------------------------------------------------------------------------- *)
(* First-order chord-rate at unit speed.                                      *)
(* -------------------------------------------------------------------------- *)

Lemma holder_window_lt : forall K gap eps,
  0 <= K ->
  0 <= gap ->
  0 < eps ->
  gap < eps / (K + 1) ->
  K * gap < eps.
Proof.
  intros K gap eps HK Hg Heps Hdt.
  destruct (Req_dec gap 0) as [Hg0 | Hgnz].
  - rewrite Hg0. rewrite Rmult_0_r. exact Heps.
  - assert (Hgp : 0 < gap).
    { destruct Hg as [Hlt | Heq]; [exact Hlt |].
      destruct Hgnz. symmetry. exact Heq. }
    apply (Rlt_le_trans (K * gap) ((K + 1) * gap) eps).
    + rewrite Rmult_plus_distr_r. rewrite Rmult_1_l.
      rewrite <- (Rplus_0_r (K * gap)) at 1.
      apply Rplus_lt_compat_l. exact Hgp.
    + apply (Rmult_le_reg_r (/ (K + 1))).
      * apply Rinv_0_lt_compat. lra.
      * replace ((K + 1) * gap * / (K + 1)) with gap.
        2:{ rewrite (Rmult_comm (K + 1)).
            rewrite Rmult_assoc.
            rewrite Rinv_r by lra.
            rewrite Rmult_1_r. reflexivity. }
        replace (eps * / (K + 1)) with (eps / (K + 1))
          by (unfold Rdiv; reflexivity).
        apply Rlt_le. exact Hdt.
Qed.

Lemma fresnel_chord_rate : forall Cx Cy a b,
  fresnel_primitives Cx Cy a b ->
  chord_rate_tight (fresnel_curve Cx Cy) (fun _ => 1) a b.
Proof.
  intros Cx Cy a b Hpr eps Heps.
  set (M := fresnel_window_lip a b).
  set (K := sqrt 2 * M).
  assert (HM : 0 <= M) by (unfold M; apply fresnel_window_lip_nonneg).
  assert (HK : 0 <= K).
  { unfold K. apply Rmult_le_pos; [apply sqrt_pos | exact HM]. }
  set (delta := eps / (K + 1)).
  exists delta.
  assert (Hdpos : 0 < delta).
  { unfold delta, Rdiv.
    apply Rmult_lt_0_compat; [exact Heps |].
    apply Rinv_0_lt_compat. lra. }
  split; [exact Hdpos |].
  intros s t Has Hst Htb Hdt.
  set (gap := t - s).
  assert (Hgap0 : 0 <= gap) by (unfold gap; lra).
  change ((fun _ : R => 1) s * (t - s)) with (1 * (t - s)).
  rewrite Rmult_1_l.
  fold gap.
  rewrite fresnel_chord_as_origin.
  (*
    [rewrite <- fresnel_vel_chord] on [dist origin chord − gap]
    must not touch the contract factor [eps * gap] (1a2063b L645).
    Restrict to the subtracted occurrence.
  *)
  rewrite <- (fresnel_vel_chord s gap Hgap0) at 1.
  eapply Rle_trans.
  - apply (dist_abs_diff
             (mkPoint 0 0)
             (mkPoint (Cx t - Cx s) (Cy t - Cy s))
             (mkPoint (fresnel_vx s * gap) (fresnel_vy s * gap))).
  - set (dx := Cx t - Cx s - fresnel_vx s * gap).
    set (dy := Cy t - Cy s - fresnel_vy s * gap).
    set (e := M * gap * gap).
    assert (He0 : 0 <= e).
    { unfold e. apply Rmult_le_pos;
        [apply Rmult_le_pos; [exact HM | exact Hgap0] | exact Hgap0]. }
    assert (Hdx : Rabs dx <= e).
    { unfold dx, e, M, gap.
      apply (fresnel_Cx_tracks Cx Cy a b s t Hpr Has Hst Htb). }
    assert (Hdy : Rabs dy <= e).
    { unfold dy, e, M, gap.
      apply (fresnel_Cy_tracks Cx Cy a b s t Hpr Has Hst Htb). }
    rewrite dist_of_coords.
    replace ((Cx t - Cx s - fresnel_vx s * gap)
             * (Cx t - Cx s - fresnel_vx s * gap)
             + (Cy t - Cy s - fresnel_vy s * gap)
               * (Cy t - Cy s - fresnel_vy s * gap))
      with (dx * dx + dy * dy)
      by (unfold dx, dy; reflexivity).
    eapply Rle_trans.
    + apply sqrt_le_1.
      * apply Rplus_le_le_0_compat; apply prod_sqr_nonneg.
      * apply Rplus_le_le_0_compat; apply prod_sqr_nonneg.
      * apply Rplus_le_compat.
        -- apply sq_le_of_abs; [exact He0 | exact Hdx].
        -- apply sq_le_of_abs; [exact He0 | exact Hdy].
    + rewrite (sqrt_two_of_sq e He0).
      assert (HKgap : K * gap < eps).
      { apply (holder_window_lt K gap eps HK Hgap0 Heps).
        unfold gap, delta in *. exact Hdt. }
      replace (e * sqrt 2) with (K * gap * gap).
      2:{ unfold e, K.
          rewrite (Rmult_comm ((M * gap) * gap) (sqrt 2)).
          rewrite <- (Rmult_assoc (sqrt 2) (M * gap) gap).
          rewrite (Rmult_assoc (sqrt 2) M gap).
          reflexivity. }
      apply Rmult_le_compat_r; [exact Hgap0 | apply Rlt_le; exact HKgap].
Qed.

(* -------------------------------------------------------------------------- *)
(* Pack instance and headlines.                                               *)
(* -------------------------------------------------------------------------- *)

Lemma one_times : forall t, 1 * t = t.
Proof.
  intros t. apply Rmult_1_l.
Qed.

Lemma one_times_diff : forall s t, 1 * t - 1 * s = t - s.
Proof.
  intros s t.
  rewrite (one_times t). rewrite (one_times s). reflexivity.
Qed.

Lemma fresnel_speed_integral_premises :
  forall Cx Cy a b,
    a <= b ->
    fresnel_primitives Cx Cy a b ->
    speed_integral_premises
      (fresnel_curve Cx Cy) (fun _ => 1) (fun t => 1 * t) a b.
Proof.
  intros Cx Cy a b Hab Hpr.
  apply (constant_speed_premises (fresnel_curve Cx Cy) 1 a b Hab).
  - lra.
  - apply fresnel_chord_rate. exact Hpr.
Qed.

(* WITNESS {"claimId":"508-e","topic":"metric","lemma":"fresnel_is_curve_length","title":"Increment-squeezed Fresnel primitives yield metric length b-a","file":"theories/ClothoidFresnel.v","witness":"508-e-fresnel","board":"#564"} *)

Theorem fresnel_is_curve_length :
  forall Cx Cy a b,
    a <= b ->
    fresnel_primitives Cx Cy a b ->
    is_curve_length (fresnel_curve Cx Cy) a b (b - a).
Proof.
  intros Cx Cy a b Hab Hpr.
  rewrite <- (one_times_diff a b).
  apply (speed_integral_is_curve_length
           (fresnel_curve Cx Cy) (fun _ => 1) (fun t => 1 * t) a b).
  apply fresnel_speed_integral_premises; assumption.
Qed.

(* WITNESS {"claimId":"508-e-unit-window","topic":"metric","lemma":"fresnel_unit_window_length","title":"[0,1] Fresnel window has metric length 1","file":"theories/ClothoidFresnel.v","witness":"508-e-fresnel","board":"#564"} *)

Corollary fresnel_unit_window_length :
  forall Cx Cy,
    fresnel_primitives Cx Cy 0 1 ->
    is_curve_length (fresnel_curve Cx Cy) 0 1 1.
Proof.
  intros Cx Cy Hpr.
  (*
    2026-08-31 CI death at apply fresnel_is_curve_length (L713):
    [replace 1 with (1-0)] rewrites both the window [b] and the
    length, leaving [is_curve_length g 0 (1-0) (1-0)]. Pose the
    [b-a] fact first; peel [1-0] with [Rminus_0_r] only.
  *)
  assert (Hab : 0 <= 1) by lra.
  pose proof (fresnel_is_curve_length Cx Cy 0 1 Hab Hpr) as Hlen.
  rewrite Rminus_0_r in Hlen.
  exact Hlen.
Qed.

Lemma fresnel_H_unit_chord : forall Cx Cy a b s t,
  a <= b ->
  fresnel_primitives Cx Cy a b ->
  a <= s -> s <= t -> t <= b ->
  dist (fresnel_curve Cx Cy s) (fresnel_curve Cx Cy t) <= t - s.
Proof.
  intros Cx Cy a b s t Hab Hpr Has Hst Htb.
  pose proof (fresnel_speed_integral_premises Cx Cy a b Hab Hpr) as Hsip.
  pose proof (speed_integral_chord_modulus
                (fresnel_curve Cx Cy) (fun _ => 1) (fun u => 1 * u) a b
                Hsip s t Has Hst Htb) as Hmod.
  rewrite (one_times_diff s t) in Hmod.
  exact Hmod.
Qed.

Lemma fresnel_H_unit_approx : forall Cx Cy a b eps,
  a <= b ->
  fresnel_primitives Cx Cy a b ->
  0 < eps ->
  exists delta, 0 < delta /\
    forall s t, a <= s -> s <= t -> t <= b -> t - s < delta ->
      (t - s) - dist (fresnel_curve Cx Cy s) (fresnel_curve Cx Cy t)
      <= eps * (t - s).
Proof.
  intros Cx Cy a b eps Hab Hpr Heps.
  pose proof (fresnel_speed_integral_premises Cx Cy a b Hab Hpr) as Hsip.
  destruct (speed_integral_tightness
              (fresnel_curve Cx Cy) (fun _ => 1) (fun u => 1 * u) a b
              Hsip eps Heps) as (d & Hd & Htight).
  exists d. split; [exact Hd |].
  intros s t Has Hst Htb Hdt.
  specialize (Htight s t Has Hst Htb Hdt).
  rewrite (one_times_diff s t) in Htight.
  exact Htight.
Qed.

(* WITNESS {"claimId":"508-e-clothoid-contract","topic":"metric","lemma":"fresnel_discharges_clothoid_window","title":"Fresnel primitives discharge the windowed K-token contract","file":"theories/ClothoidFresnel.v","witness":"508-e-fresnel","board":"#564"} *)

Theorem fresnel_discharges_clothoid_window :
  forall Cx Cy a b,
    a <= b ->
    fresnel_primitives Cx Cy a b ->
    is_curve_length (fresnel_curve Cx Cy) a b (b - a).
Proof.
  intros Cx Cy a b Hab Hpr.
  apply (clothoid_arclength_is_curve_length
           (fresnel_curve Cx Cy) a b Hab).
  - intros s t Hs Hst Ht.
    apply (fresnel_H_unit_chord Cx Cy a b s t Hab Hpr Hs Hst Ht).
  - intros eps Heps.
    apply (fresnel_H_unit_approx Cx Cy a b eps Hab Hpr Heps).
Qed.

Print Assumptions fresnel_is_curve_length.
Print Assumptions fresnel_unit_window_length.
Print Assumptions fresnel_discharges_clothoid_window.
Print Assumptions fresnel_chord_rate.
