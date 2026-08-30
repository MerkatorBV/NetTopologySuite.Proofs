(* ============================================================================
   NetTopologySuite.Proofs.EllipseSpeedIntegral
   ----------------------------------------------------------------------------
   Issue #563 / claimId 508-d: instantiate the #561 speed-integral pack
   on the genuine (rx ≠ ry) ellipse.

   Route 1 does not construct an incomplete elliptic integral (no
   Coquelicot / RInt). This letter discharges the two analytic pack
   premises for σ = √(rx² sin² t + ry² cos² t):

     uniformly_continuous_on (ellipse_speed rx ry)   (Hölder 1/2)
     chord_rate_tight (ellipse_param …) (ellipse_speed rx ry)

   The remaining Technique-park hypothesis is increment_squeezed E σ —
   "E is a primitive of the elliptic speed". Then

     increment_squeezed E (ellipse_speed rx ry) a b
       → is_curve_length (ellipse_param …) a b (E b − E a).

   Witness: any such E on the rx=3, ry=4 quarter has
     3·(π/2) ≤ E(π/2) − E 0 ≤ 4·(π/2)
   from the speed sandwich (no oracle dependency).

   EllipseLength_E.v's circular discharge and H_E_* Section stay.
   This file does not remint SpeedIntegral. No Heine–Cantor.
   No CurveSegment growth, no ADR-0004 remint, no TRIAGE flip.

   No `Admitted`, no `Axiom`, no `Parameter`.  3-axiom.
   Nested goals under [-] use [+] / [*]. No [nra].
   Do not [rewrite <- sqrt_sqrt] inside a [by ring] — on flocq
   the rewrite is a convertibility no-op and ring then sees
   [sqrt] (0d39b90 L81, "not a valid ring equation"). Pose the
   identity, expand the square, then rewrite.
   [rewrite <- sqrt_square] without [at 1] rewrites the [y] inside
   [sqrt y] (082ef13 L102, no subterm [sqrt x * sqrt y]).
   [rewrite <- Hmin2 in Hlo] looks for the product; Hlo has
   [Rmin (rx²,ry²)] (216ebce L153). Rewrite forward.
   [rewrite (Rabs_right 2)] needs a subterm [Rabs 2]. Left-associated
   [2 * cos * sin] becomes [Rabs (2 * cos)] after one [Rabs_mult]
   (784051a L226). Parenthesize [2 * (cos * sin)].
   After that pin the leftover [2 * Rabs (sin (gap/2))] is not
   [Rabs (sin _)]; apply [Rmult_le_compat_l] then [Rabs_sin_le_abs]
   (a49f234 L237). Cancel [2*(Rabs * /2)] with [Rinv_r], not [field].
   [apply Rplus_le_compat; apply Rabs_le; assumption] leaves evars
   because flocq [1+1] is not convertible to [2] (67541e1 L282,
   "No such assumption"). [replace 2 with (1+1) by ring], then
   [exact HtB]. Do not nest [+] under [+] (b233899 L288 Focus).
   Inner [Rplus_le_compat] arms use [*].
   [lra] on [(t-s)*2 <= 2*(t-s)] cannot find a witness
   (860debe L294). Do not [replace 2 with (1+1)] in the
   Rabs-sum arm — that makes the leftover [(t-s)*(1+1)]
   vs [2*(t-s)] (a299db8 L296, "not a valid ring equation").
   Prove [<= 2] via [1+1] then [replace (1+1) with 2].
   [apply Req_le] on [1+1 <= ?b] instantiates [?b] as [1+1]
   (974266b L302, leftover [(t-s)*(IPR 1 + IPR 1)]). Assert
   [Rabs (sin t + sin s) <= 2] with a concrete conclusion.
   [holder_window_lt] first arm [lra] cannot witness
   [K*gap < (K+1)*gap] when [gap] may be 0 (1480ac6 L335).
   Split [gap = 0]; cancel [/(K+1)] with [Rinv_r].
   Flocq [sqrt_Rsqr] is [0 <= x -> sqrt (Rsqr x) = x], so
   [rewrite sqrt_Rsqr] already yields [2], not [Rabs 2]
   (84b2036 L419). [sqrt_Rsqr 2] by [lra]; [sqrt_Rsqr_abs] for [su].
   After [set (gap := t-s)] the chord-rate goal has [ss * gap],
   not [2 * xv * ss] (7d2c5cc L489). Prove [2 * xv = gap] with
   [Rinv_r]; do not [field] that scale.
   [Rmult_le_compat_l] on [2 * M * (xv³/6)] unifies [(2*M)] with [2]
   (2015aaa L513). Parenthesize [2 * (M * …)]; scale [xv=gap/2]
   with [Rinv_mult_distr], not [field].
   [Rinv_mult] is not [Rinv_mult_distr]: [rewrite Rinv_mult; [|lra|lra]]
   is "expected 1 tactic" (7647e7b L529). Keep the [distr] name.
   [ring] does not see [s*2] as [s+s] (9b03bd6 L558). Expand
   [-s*2] as [-s + -s] via [replace 2 with (1+1)].
   Final [ring] of [Hmid_s] after that expand still fails
   (bfa07f0 L560 / 295a15b L567): leftover
   [(s+t)+(-s+-s) = t-s] is not a flocq ring equation.
   Close with [Rplus_comm] / [Rplus_assoc] / [Rplus_opp_r].
   [apply Rmult_1_r] needs [?r*1 = ?r]; after [/2*2] cancel the
   replace-witness is [s+t = (s+t)*1] (7ff799a L247). [rewrite].
   Do not [field] the ε/2 chord-rate arms ([gap*/gap], [/24*24],
   [eps/2*24], [/(K+1)], [eps/2+eps/2]). Cancel with [Rinv_r] /
   [Rinv_l] / [Rinv_mult_distr]. [a+a] is [1+1] times [a], not [2*a].

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveLength ArcLength ArcRectifiable
                               EllipseLength EllipseLength_E SpeedIntegral.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Speed = √(speed²).                                                         *)
(* -------------------------------------------------------------------------- *)

Definition ellipse_speed (rx ry t : R) : R :=
  sqrt (ellipse_speed_sq rx ry t).

Lemma ellipse_speed_nonneg : forall rx ry t,
  0 <= ellipse_speed rx ry t.
Proof.
  intros rx ry t. unfold ellipse_speed. apply sqrt_pos.
Qed.

Lemma Rmax_nonneg : forall rx ry,
  0 <= rx -> 0 <= ry -> 0 <= Rmax rx ry.
Proof.
  intros rx ry Hrx _. apply (Rle_trans 0 rx); [exact Hrx | apply Rmax_l].
Qed.

Lemma Rmin_nonneg : forall rx ry,
  0 <= rx -> 0 <= ry -> 0 <= Rmin rx ry.
Proof.
  intros rx ry Hrx Hry. apply Rmin_glb; assumption.
Qed.

Lemma sqrt_minus_sq : forall x y,
  0 <= x -> 0 <= y ->
  (sqrt x - sqrt y) * (sqrt x - sqrt y)
  = x + y - 2 * sqrt x * sqrt y.
Proof.
  intros x y Hx Hy.
  pose proof (sqrt_sqrt x Hx) as Hx2.
  pose proof (sqrt_sqrt y Hy) as Hy2.
  transitivity
    (sqrt x * sqrt x + sqrt y * sqrt y - 2 * sqrt x * sqrt y).
  - ring.
  - rewrite Hx2, Hy2. ring.
Qed.

Lemma sqrt_abs_le_sqrt_diff : forall x y,
  0 <= x -> 0 <= y ->
  Rabs (sqrt x - sqrt y) <= sqrt (Rabs (x - y)).
Proof.
  intros x y Hx Hy.
  rewrite <- (sqrt_Rsqr_abs (sqrt x - sqrt y)).
  apply sqrt_le_1.
  - apply Rle_0_sqr.
  - apply Rabs_pos.
  - unfold Rsqr.
    rewrite (sqrt_minus_sq x y Hx Hy).
    destruct (Rle_dec y x) as [Hyx | Hnxy].
    + rewrite (Rabs_right (x - y)) by lra.
      assert (H : y <= sqrt x * sqrt y).
      { pose proof (sqrt_square y Hy) as Hyy.
        rewrite <- Hyy at 1.
        pose proof (sqrt_mult x y Hx Hy) as Hprod.
        rewrite <- Hprod.
        apply sqrt_le_1.
        - apply Rmult_le_pos; exact Hy.
        - apply Rmult_le_pos; [exact Hx | exact Hy].
        - apply Rmult_le_compat_r; [exact Hy | exact Hyx]. }
      lra.
    + assert (Hxy : x <= y) by lra.
      rewrite (Rabs_left1 (x - y)) by lra.
      replace (- (x - y)) with (y - x) by ring.
      assert (H : x <= sqrt x * sqrt y).
      { pose proof (sqrt_square x Hx) as Hxx.
        rewrite <- Hxx at 1.
        pose proof (sqrt_mult x y Hx Hy) as Hprod.
        rewrite <- Hprod.
        apply sqrt_le_1.
        - apply Rmult_le_pos; exact Hx.
        - apply Rmult_le_pos; [exact Hx | exact Hy].
        - apply Rmult_le_compat_l; [exact Hx | exact Hxy]. }
      lra.
Qed.

Lemma ellipse_speed_bounds : forall rx ry t,
  0 <= rx -> 0 <= ry ->
  Rmin rx ry <= ellipse_speed rx ry t <= Rmax rx ry.
Proof.
  intros rx ry t Hrx Hry.
  pose proof (ellipse_speed_sq_sandwich rx ry t) as Hsq.
  destruct Hsq as [Hlo Hhi].
  unfold ellipse_speed.
  assert (Hmn0 : 0 <= Rmin rx ry) by (apply Rmin_nonneg; assumption).
  assert (Hmx0 : 0 <= Rmax rx ry) by (apply Rmax_nonneg; assumption).
  assert (Hmin2 : Rmin (rx * rx) (ry * ry) = Rmin rx ry * Rmin rx ry).
  { destruct (Rle_dec rx ry) as [Hle | Hgt].
    - rewrite (Rmin_left rx ry Hle).
      rewrite (Rmin_left (rx * rx) (ry * ry));
        [ring | apply Rmult_le_compat; lra].
    - rewrite (Rmin_right rx ry) by lra.
      rewrite (Rmin_right (rx * rx) (ry * ry));
        [ring | apply Rmult_le_compat; lra]. }
  assert (Hmax2 : Rmax (rx * rx) (ry * ry) = Rmax rx ry * Rmax rx ry).
  { destruct (Rle_dec rx ry) as [Hle | Hgt].
    - rewrite (Rmax_right rx ry Hle).
      rewrite (Rmax_right (rx * rx) (ry * ry));
        [ring | apply Rmult_le_compat; lra].
    - rewrite (Rmax_left rx ry) by lra.
      rewrite (Rmax_left (rx * rx) (ry * ry));
        [ring | apply Rmult_le_compat; lra]. }
  split.
  - rewrite <- (sqrt_square (Rmin rx ry) Hmn0).
    rewrite Hmin2 in Hlo.
    apply sqrt_le_1.
    + apply Rmult_le_pos; exact Hmn0.
    + apply ellipse_speed_sq_nonneg.
    + exact Hlo.
  - rewrite <- (sqrt_square (Rmax rx ry) Hmx0).
    rewrite Hmax2 in Hhi.
    apply sqrt_le_1.
    + apply ellipse_speed_sq_nonneg.
    + apply Rmult_le_pos; exact Hmx0.
    + exact Hhi.
Qed.

(* -------------------------------------------------------------------------- *)
(* Half-angle factorizations.                                                 *)
(* -------------------------------------------------------------------------- *)

Lemma cos_s_minus_cos_t : forall s t,
  cos s - cos t
  = 2 * sin ((s + t) / 2) * sin ((t - s) / 2).
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

(* Flocq [ring] refuses [(s+t)+(-s+-s) = t-s] (295a15b L567). *)
Lemma half_sum_minus_left : forall s t,
  (s + t) / 2 - s = (t - s) / 2.
Proof.
  intros s t.
  unfold Rdiv, Rminus.
  apply (Rmult_eq_reg_r 2); [| lra].
  rewrite Rmult_plus_distr_r.
  replace ((s + t) * / 2 * 2) with (s + t).
  2:{ rewrite Rmult_assoc. rewrite Rinv_l by lra.
      rewrite Rmult_1_r. reflexivity. }
  replace ((t + - s) * / 2 * 2) with (t + - s).
  2:{ rewrite Rmult_assoc. rewrite Rinv_l by lra.
      rewrite Rmult_1_r. reflexivity. }
  replace ((- s) * 2) with (- s + - s).
  2:{ replace 2 with (1 + 1) by ring.
      rewrite Rmult_plus_distr_l. rewrite Rmult_1_r. reflexivity. }
  rewrite (Rplus_comm s t).
  rewrite Rplus_assoc.
  rewrite <- (Rplus_assoc s (- s) (- s)).
  rewrite Rplus_opp_r.
  rewrite Rplus_0_l.
  reflexivity.
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

Lemma ellipse_speed_sq_diff_bound : forall rx ry s t,
  s <= t ->
  Rabs (ellipse_speed_sq rx ry t - ellipse_speed_sq rx ry s)
  <= 2 * Rabs (rx * rx - ry * ry) * (t - s).
Proof.
  intros rx ry s t Hst.
  unfold ellipse_speed_sq.
  replace (rx * rx * (sin t * sin t) + ry * ry * (cos t * cos t)
           - (rx * rx * (sin s * sin s) + ry * ry * (cos s * cos s)))
    with ((rx * rx - ry * ry) * (sin t * sin t - sin s * sin s)).
  2:{ pose proof (sin2_cos2 t) as Ht. pose proof (sin2_cos2 s) as Hs.
      unfold Rsqr in Ht, Hs.
      replace (cos t * cos t) with (1 - sin t * sin t) by lra.
      replace (cos s * cos s) with (1 - sin s * sin s) by lra.
      ring. }
  rewrite Rabs_mult.
  replace (sin t * sin t - sin s * sin s)
    with ((sin t - sin s) * (sin t + sin s)) by ring.
  rewrite Rabs_mult.
  assert (Hsum2 : Rabs (sin t + sin s) <= 2).
  { eapply Rle_trans; [apply Rabs_triang |].
    pose proof (SIN_bound t) as HtB.
    pose proof (SIN_bound s) as HsB.
    apply (Rle_trans (Rabs (sin t) + Rabs (sin s)) (1 + 1) 2).
    - apply Rplus_le_compat.
      + apply Rabs_le. exact HtB.
      + apply Rabs_le. exact HsB.
    - apply Req_le. replace (1 + 1) with 2 by ring. reflexivity. }
  eapply Rle_trans.
  - apply Rmult_le_compat_l; [apply Rabs_pos |].
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | |].
    + apply sin_abs_lipschitz.
    + exact Hsum2.
  - rewrite (Rabs_right (t - s)) by lra.
    replace (Rabs (rx * rx - ry * ry) * ((t - s) * 2))
      with (2 * Rabs (rx * rx - ry * ry) * (t - s)) by ring.
    apply Rle_refl.
Qed.

Lemma ellipse_speed_holder : forall rx ry s t,
  s <= t ->
  Rabs (ellipse_speed rx ry t - ellipse_speed rx ry s)
  <= sqrt (2 * Rabs (rx * rx - ry * ry) * (t - s)).
Proof.
  intros rx ry s t Hst.
  unfold ellipse_speed.
  eapply Rle_trans.
  - apply sqrt_abs_le_sqrt_diff;
      [apply ellipse_speed_sq_nonneg | apply ellipse_speed_sq_nonneg].
  - apply sqrt_le_1.
    + apply Rabs_pos.
    + apply Rmult_le_pos.
      * apply Rmult_le_pos; [lra | apply Rabs_pos].
      * lra.
    + apply ellipse_speed_sq_diff_bound. exact Hst.
Qed.

Lemma holder_window_lt : forall K gap eps,
  0 <= K ->
  0 <= gap ->
  0 < eps ->
  gap < eps * eps / (K + 1) ->
  K * gap < eps * eps.
Proof.
  intros K gap eps HK Hg Heps Hdt.
  destruct (Req_dec gap 0) as [Hg0 | Hgnz].
  - rewrite Hg0. rewrite Rmult_0_r.
    apply Rmult_lt_0_compat; [exact Heps | exact Heps].
  - assert (Hgp : 0 < gap).
    { destruct Hg as [Hlt | Heq]; [exact Hlt |].
      destruct Hgnz. symmetry. exact Heq. }
    apply (Rlt_le_trans (K * gap) ((K + 1) * gap) (eps * eps)).
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
        replace (eps * eps * / (K + 1)) with (eps * eps / (K + 1))
          by (unfold Rdiv; reflexivity).
        apply Rlt_le. exact Hdt.
Qed.

Lemma ellipse_speed_uc : forall rx ry a b,
  uniformly_continuous_on (ellipse_speed rx ry) a b.
Proof.
  intros rx ry a b eps Heps.
  set (K := 2 * Rabs (rx * rx - ry * ry)).
  assert (HK : 0 <= K)
    by (unfold K; apply Rmult_le_pos; [lra | apply Rabs_pos]).
  exists (eps * eps / (K + 1)).
  split.
  - unfold Rdiv. apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra |].
    apply Rinv_0_lt_compat. lra.
  - intros s t _ Hst _ Hdt.
    eapply Rle_lt_trans.
    + apply ellipse_speed_holder. exact Hst.
    + rewrite <- (sqrt_square eps) by lra.
      apply sqrt_lt_1.
      * apply Rmult_le_pos; [exact HK | lra].
      * apply Rmult_le_pos; lra.
      * apply (holder_window_lt K (t - s) eps HK); lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Exact chord = 2 |sin(gap/2)| σ(mid).                                       *)
(* -------------------------------------------------------------------------- *)

Lemma ellipse_dist_sq_mid : forall Oc rx ry rot s t,
  dist_sq (ellipse_pt Oc rx ry rot s) (ellipse_pt Oc rx ry rot t)
  = 4 * (sin ((t - s) / 2) * sin ((t - s) / 2))
      * ellipse_speed_sq rx ry ((s + t) / 2).
Proof.
  intros Oc rx ry rot s t.
  rewrite ellipse_dist_sq.
  rewrite cos_s_minus_cos_t, sin_s_minus_sin_t.
  unfold ellipse_speed_sq.
  ring.
Qed.

Lemma prod_sqr_nonneg : forall x, 0 <= x * x.
Proof.
  intros x. pose proof (Rle_0_sqr x) as H. unfold Rsqr in H. exact H.
Qed.

Lemma ellipse_chord_eq_speed : forall Oc rx ry rot s t,
  dist (ellipse_param Oc rx ry rot s) (ellipse_param Oc rx ry rot t)
  = 2 * Rabs (sin ((t - s) / 2)) * ellipse_speed rx ry ((s + t) / 2).
Proof.
  intros Oc rx ry rot s t.
  unfold ellipse_param, dist, ellipse_speed.
  rewrite ellipse_dist_sq_mid.
  set (su := sin ((t - s) / 2)).
  set (mid := (s + t) / 2).
  set (q := ellipse_speed_sq rx ry mid).
  assert (H4 : 0 <= 4) by lra.
  assert (Hsu : 0 <= su * su) by (apply prod_sqr_nonneg).
  assert (Hq : 0 <= q) by (unfold q; apply ellipse_speed_sq_nonneg).
  rewrite (sqrt_mult (4 * (su * su)) q);
    [| apply Rmult_le_pos; [exact H4 | exact Hsu] | exact Hq].
  rewrite (sqrt_mult 4 (su * su)); [| exact H4 | exact Hsu].
  replace 4 with (Rsqr 2) by (unfold Rsqr; ring).
  rewrite (sqrt_Rsqr 2) by lra.
  replace (su * su) with (Rsqr su) by (unfold Rsqr; reflexivity).
  rewrite sqrt_Rsqr_abs.
  ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* First-order chord-rate.                                                    *)
(* -------------------------------------------------------------------------- *)

(* half_gap_lt_one / sin_half_gap_nonneg live in SpeedIntegral. *)

Lemma ellipse_chord_rate : forall Oc rx ry rot a b,
  0 <= rx -> 0 <= ry ->
  chord_rate_tight (ellipse_param Oc rx ry rot) (ellipse_speed rx ry) a b.
Proof.
  intros Oc rx ry rot a b Hrx Hry eps Heps.
  set (K := 2 * Rabs (rx * rx - ry * ry)).
  set (M := Rmax rx ry).
  assert (HK : 0 <= K)
    by (unfold K; apply Rmult_le_pos; [lra | apply Rabs_pos]).
  assert (HM : 0 <= M) by (unfold M; apply Rmax_nonneg; assumption).
  set (d1 := eps * eps / (4 * (K + 1))).
  set (d2 := sqrt (6 * eps / (M + 1))).
  set (delta := Rmin 2 (Rmin d1 (Rmin 1 d2))).
  exists delta.
  assert (Hd1 : 0 < d1).
  { unfold d1, Rdiv. apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat; lra |].
    apply Rinv_0_lt_compat. lra. }
  assert (Hd2 : 0 < d2).
  { unfold d2. apply sqrt_lt_R0. unfold Rdiv.
    apply Rmult_lt_0_compat; [lra | apply Rinv_0_lt_compat; lra]. }
  assert (Hdpos : 0 < delta).
  { unfold delta. apply Rmin_glb_lt; [lra |].
    apply Rmin_glb_lt; [exact Hd1 |].
    apply Rmin_glb_lt; [lra | exact Hd2]. }
  split; [exact Hdpos |].
  intros s t Has Hst Htb Hdt.
  set (gap := t - s).
  set (xv := gap / 2).
  set (mid := (s + t) / 2).
  assert (Hgap0 : 0 <= gap) by (unfold gap; lra).
  assert (Hxv0 : 0 <= xv).
  { unfold xv, Rdiv. apply Rmult_le_pos; [exact Hgap0 |].
    apply Rlt_le, Rinv_0_lt_compat. lra. }
  assert (Hgap2 : gap < 2).
  { unfold gap. eapply Rlt_le_trans; [exact Hdt | unfold delta; apply Rmin_l]. }
  assert (Hsin0 : 0 <= sin xv).
    { unfold xv, gap. apply sin_half_gap_nonneg; [exact Hst | exact Hgap2]. }
  rewrite ellipse_chord_eq_speed.
  rewrite (Rabs_right (sin ((t - s) / 2))).
  2:{ unfold xv, gap in Hsin0. exact (Rle_ge _ _ Hsin0). }
  replace ((t - s) / 2) with xv by (unfold xv, gap; reflexivity).
  replace ((s + t) / 2) with mid by reflexivity.
  set (sm := ellipse_speed rx ry mid).
  set (ss := ellipse_speed rx ry s).
  assert (Hsm0 : 0 <= sm) by (unfold sm; apply ellipse_speed_nonneg).
  assert (Hss0 : 0 <= ss) by (unfold ss; apply ellipse_speed_nonneg).
  assert (HsmM : sm <= M).
  { unfold sm, M. apply (proj2 (ellipse_speed_bounds rx ry mid Hrx Hry)). }
  assert (H2xv : 2 * xv = gap).
  { unfold xv, Rdiv.
    rewrite <- Rmult_assoc.
    rewrite (Rmult_comm 2 gap).
    rewrite Rmult_assoc.
    rewrite Rinv_r by lra.
    rewrite Rmult_1_r. reflexivity. }
  replace (ss * gap) with (2 * xv * ss) by (rewrite H2xv; ring).
  pose proof (Rabs_triang (2 * sin xv * sm - 2 * xv * sm)
                          (2 * xv * sm - 2 * xv * ss)) as Htr.
  replace (2 * sin xv * sm - 2 * xv * ss)
    with ((2 * sin xv * sm - 2 * xv * sm) + (2 * xv * sm - 2 * xv * ss))
    by ring.
  eapply Rle_trans; [exact Htr |].
  assert (Hsinx : sin xv <= xv) by (apply sin_le_x; exact Hxv0).
  assert (Hx4 : xv <= 4).
  { apply Rlt_le. apply (Rlt_le_trans xv 1 4); [| lra].
    apply (half_gap_lt_one s t). unfold gap in Hgap2. exact Hgap2. }
  assert (Hslack : xv - sin xv <= xv * xv * xv / 6).
  { pose proof (sin_lower_taylor xv Hxv0 Hx4) as Htaylor. lra. }
  assert (Harm1' : Rabs (2 * sin xv * sm - 2 * xv * sm)
                   <= M * (gap * gap * gap) / 24).
  { replace (2 * sin xv * sm - 2 * xv * sm)
      with (2 * (sm * (sin xv - xv))) by ring.
    rewrite Rabs_mult. rewrite (Rabs_right 2) by lra.
    rewrite Rabs_mult. rewrite (Rabs_right sm) by (apply Rle_ge; exact Hsm0).
    rewrite Rabs_left1 by lra.
    replace (- (sin xv - xv)) with (xv - sin xv) by ring.
    apply (Rle_trans _ (2 * (M * (xv * xv * xv / 6)))).
    - apply Rmult_le_compat_l; [lra |].
      apply Rmult_le_compat; [exact Hsm0 | lra | exact HsmM | exact Hslack].
    - apply Req_le.
      rewrite <- H2xv.
      unfold Rdiv.
      replace ((2 * xv) * (2 * xv) * (2 * xv))
        with (8 * (xv * xv * xv)) by ring.
      replace (2 * (M * (xv * xv * xv * / 6)))
        with ((2 * / 6) * (M * (xv * xv * xv))) by ring.
      replace (M * (8 * (xv * xv * xv)) * / 24)
        with ((8 * / 24) * (M * (xv * xv * xv))) by ring.
      replace (8 * / 24) with (2 * / 6).
      2:{ replace 24 with (4 * 6) by ring.
          rewrite Rinv_mult_distr; [| lra | lra].
          replace 8 with (2 * 4) by ring.
          rewrite <- Rmult_assoc.
          rewrite (Rmult_assoc 2 4 (/ 4)).
          rewrite Rinv_r by lra.
          rewrite Rmult_1_r. reflexivity. }
      reflexivity. }
  assert (Harm2 : Rabs (2 * xv * sm - 2 * xv * ss)
                  <= gap * sqrt (K * (gap / 2))).
  { replace (2 * xv * sm - 2 * xv * ss) with (2 * (xv * (sm - ss))) by ring.
    rewrite Rabs_mult. rewrite (Rabs_right 2) by lra.
    rewrite Rabs_mult. rewrite (Rabs_right xv) by lra.
    replace (2 * (xv * Rabs (sm - ss))) with (gap * Rabs (sm - ss))
      by (rewrite <- H2xv; ring).
    apply Rmult_le_compat_l; [exact Hgap0 |].
    unfold sm, ss.
    replace (Rabs (ellipse_speed rx ry mid - ellipse_speed rx ry s))
      with (Rabs (ellipse_speed rx ry s - ellipse_speed rx ry mid))
      by (apply Rabs_minus_sym).
    assert (Hmid_s : mid - s = xv).
    { unfold mid, xv, gap. apply half_sum_minus_left. }
    assert (Hs_mid : s <= mid).
    { apply (Rplus_le_reg_r (- s)).
      rewrite Rplus_opp_r.
      replace (mid + - s) with (mid - s) by (unfold Rminus; reflexivity).
      rewrite Hmid_s. exact Hxv0. }
    pose proof (ellipse_speed_holder rx ry s mid Hs_mid) as Hh.
    eapply Rle_trans; [exact Hh |].
    apply Req_le. f_equal.
    unfold K. rewrite Hmid_s.
    unfold xv, Rdiv. reflexivity. }
  eapply Rle_trans.
  - apply Rplus_le_compat; [exact Harm1' | exact Harm2].
  - (* each arm ≤ (eps/2) gap *)
    apply (Rle_trans _ (eps / 2 * gap + eps / 2 * gap)).
    + apply Rplus_le_compat.
      * (* M gap³/24 ≤ (eps/2) gap *)
        destruct (Req_dec gap 0) as [Hg0 | Hgnz].
        { rewrite Hg0. unfold Rdiv. lra. }
        apply (Rmult_le_reg_r (/ gap)); [apply Rinv_0_lt_compat; lra |].
        assert (Hginv : gap * / gap = 1).
        { apply Rinv_r. exact Hgnz. }
        replace (M * (gap * gap * gap) / 24 * / gap)
          with (M * (gap * gap) / 24).
        { unfold Rdiv.
          replace (((M * (gap * gap * gap)) * / 24) * / gap)
            with (M * (gap * gap) * (gap * / gap) * / 24) by ring.
          rewrite Hginv. ring. }
        replace (eps / 2 * gap * / gap) with (eps / 2).
        { unfold Rdiv.
          replace ((eps * / 2) * gap * / gap)
            with (eps * / 2 * (gap * / gap)) by ring.
          rewrite Hginv. ring. }
        apply (Rmult_le_reg_r 24); [lra |].
        replace (M * (gap * gap) / 24 * 24) with (M * (gap * gap)).
        { unfold Rdiv.
          replace ((M * (gap * gap) * / 24) * 24)
            with (M * (gap * gap) * (/ 24 * 24)) by ring.
          rewrite Rinv_l by lra. ring. }
        replace (eps / 2 * 24) with (12 * eps).
        { unfold Rdiv.
          replace ((eps * / 2) * 24) with (eps * (/ 2 * 24)) by ring.
          replace 24 with (2 * 12) by ring.
          rewrite <- (Rmult_assoc (/ 2) 2 12).
          rewrite Rinv_l by lra. ring. }
        (* gap < d2 = sqrt(6 eps / (M+1)) ⇒ gap² < 6 eps / (M+1)
           ⇒ M gap² < 6 M eps / (M+1) ≤ 6 eps *)
        assert (Hgd2 : gap < d2).
        { unfold gap. eapply Rlt_le_trans; [exact Hdt |].
          unfold delta.
          eapply Rle_trans; [apply Rmin_r |].
          eapply Rle_trans; [apply Rmin_r |].
          apply Rmin_r. }
        assert (Hgsq : gap * gap < 6 * eps / (M + 1)).
        { unfold d2 in Hgd2.
          eapply Rlt_le_trans.
          - apply (pos_lt_sq gap d2 Hgap0 Hgd2).
          - unfold d2. rewrite sqrt_sqrt.
            + apply Rle_refl.
            + unfold Rdiv. apply Rmult_le_pos; [lra |].
              apply Rlt_le, Rinv_0_lt_compat. lra. }
        apply (Rle_trans _ (M * (6 * eps / (M + 1)))).
        { apply Rmult_le_compat_l; [exact HM | apply Rlt_le; exact Hgsq]. }
        replace (M * (6 * eps / (M + 1))) with (6 * eps * (M / (M + 1))).
        { unfold Rdiv. ring. }
        apply (Rle_trans _ (6 * eps)).
        { replace (6 * eps) with (6 * eps * 1) at 2 by ring.
          apply Rmult_le_compat_l; [apply Rmult_le_pos; lra |].
          unfold Rdiv. apply (Rmult_le_reg_r (M + 1)); [lra |].
          replace (M * / (M + 1) * (M + 1)) with M.
          { rewrite (Rmult_assoc M (/ (M + 1)) (M + 1)).
            rewrite Rinv_l by lra. ring. }
          lra. }
        lra.
      * (* gap √(K gap/2) ≤ (eps/2) gap *)
        destruct (Req_dec gap 0) as [Hg0 | Hgnz].
        { rewrite Hg0. unfold Rdiv.
          rewrite Rmult_0_l. rewrite Rmult_0_r. apply Rle_refl. }
        apply (Rmult_le_reg_r (/ gap)); [apply Rinv_0_lt_compat; lra |].
        assert (Hginv : gap * / gap = 1).
        { apply Rinv_r. exact Hgnz. }
        replace (gap * sqrt (K * (gap / 2)) * / gap)
          with (sqrt (K * (gap / 2))).
        { replace (gap * sqrt (K * (gap / 2)) * / gap)
            with (sqrt (K * (gap / 2)) * (gap * / gap)) by ring.
          rewrite Hginv. ring. }
        replace (eps / 2 * gap * / gap) with (eps / 2).
        { unfold Rdiv.
          replace ((eps * / 2) * gap * / gap)
            with (eps * / 2 * (gap * / gap)) by ring.
          rewrite Hginv. ring. }
        apply sqrt_le_1.
        -- apply Rmult_le_pos; [exact HK |].
           unfold Rdiv. apply Rmult_le_pos; [exact Hgap0 |].
           apply Rlt_le, Rinv_0_lt_compat. lra.
        -- unfold Rdiv. apply Rmult_le_pos; [apply Rmult_le_pos; lra |].
           apply Rlt_le, Rinv_0_lt_compat. lra.
        -- assert (Hgd1 : gap < d1).
           { unfold gap. eapply Rlt_le_trans; [exact Hdt |].
             unfold delta.
             eapply Rle_trans; [apply Rmin_r | apply Rmin_l]. }
           unfold d1 in Hgd1.
           apply (Rle_trans _ (K * (eps * eps / (4 * (K + 1)) / 2))).
           ++ apply Rmult_le_compat_l; [exact HK |].
              unfold Rdiv. apply Rmult_le_compat_r;
                [apply Rlt_le, Rinv_0_lt_compat; lra | apply Rlt_le; exact Hgd1].
           ++ unfold Rdiv.
              replace (K * (eps * eps * / (4 * (K + 1)) * / 2))
                with (K / (K + 1) * (eps * eps / 8)).
              { unfold Rdiv.
                assert (Hinv4K : / (4 * (K + 1)) = / 4 * / (K + 1)).
                { apply Rinv_mult_distr; lra. }
                rewrite Hinv4K.
                replace (K * (eps * eps * (/ 4 * / (K + 1)) * / 2))
                  with (K * / (K + 1) * (eps * eps * (/ 4 * / 2))) by ring.
                replace (/ 4 * / 2) with (/ 8).
                { rewrite <- Rinv_mult_distr by lra.
                  replace (4 * 2) with 8 by ring. reflexivity. }
                ring. }
              apply (Rle_trans _ (eps * eps / 8)).
              ** replace (eps * eps / 8) with (1 * (eps * eps / 8)) at 2 by ring.
                 apply Rmult_le_compat_r.
                 { unfold Rdiv. apply Rmult_le_pos;
                     [apply Rmult_le_pos; lra |].
                   apply Rlt_le, Rinv_0_lt_compat. lra. }
                 unfold Rdiv. apply (Rmult_le_reg_r (K + 1)); [lra |].
                 replace (K * / (K + 1) * (K + 1)) with K.
                 { rewrite (Rmult_assoc K (/ (K + 1)) (K + 1)).
                   rewrite Rinv_l by lra. ring. }
                 lra.
              ** unfold Rdiv.
                 replace (eps / 2 * (eps / 2)) with (eps * eps / 4).
                 { unfold Rdiv.
                   replace ((eps * / 2) * (eps * / 2))
                     with (eps * eps * (/ 2 * / 2)) by ring.
                   replace (/ 2 * / 2) with (/ 4).
                   { rewrite <- Rinv_mult_distr by lra.
                     replace (2 * 2) with 4 by ring. reflexivity. }
                   ring. }
                 apply (Rmult_le_reg_r 8); [lra |].
                 replace (eps * eps * / 8 * 8) with (eps * eps).
                 { replace ((eps * eps * / 8) * 8)
                     with (eps * eps * (/ 8 * 8)) by ring.
                   rewrite Rinv_l by lra. ring. }
                 replace (eps * eps * / 4 * 8) with (2 * (eps * eps)).
                 { replace ((eps * eps * / 4) * 8)
                     with (eps * eps * (/ 4 * 8)) by ring.
                   replace 8 with (4 * 2) by ring.
                   rewrite <- (Rmult_assoc (/ 4) 4 2).
                   rewrite Rinv_l by lra. ring. }
                 lra.
    + replace (eps / 2 * gap + eps / 2 * gap) with (eps * gap).
      { unfold Rdiv.
        replace ((eps * / 2) * gap + (eps * / 2) * gap)
          with ((eps * / 2 + eps * / 2) * gap) by ring.
        replace (eps * / 2 + eps * / 2) with (eps * / 2 * 2).
        { replace 2 with (1 + 1) by ring.
          rewrite Rmult_plus_distr_l. rewrite Rmult_1_r. reflexivity. }
        replace (eps * / 2 * 2 * gap) with (eps * (/ 2 * 2) * gap) by ring.
        rewrite Rinv_l by lra. ring. }
      apply Rle_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* Pack instance and headline.                                                *)
(* -------------------------------------------------------------------------- *)

Lemma ellipse_speed_nonneg_on : forall rx ry a b,
  forall t, a <= t -> t <= b -> 0 <= ellipse_speed rx ry t.
Proof.
  intros rx ry a b t _ _. apply ellipse_speed_nonneg.
Qed.

Lemma ellipse_speed_integral_premises :
  forall Oc rx ry rot (E : R -> R) a b,
    0 <= rx -> 0 <= ry -> a <= b ->
    increment_squeezed E (ellipse_speed rx ry) a b ->
    speed_integral_premises
      (ellipse_param Oc rx ry rot)
      (ellipse_speed rx ry) E a b.
Proof.
  intros Oc rx ry rot E a b Hrx Hry Hab Hsq.
  refine (conj Hab (conj _ (conj _ (conj Hsq _)))).
  - apply ellipse_speed_nonneg_on.
  - apply ellipse_speed_uc.
  - apply ellipse_chord_rate; assumption.
Qed.

(* WITNESS {"claimId":"508-d","topic":"metric","lemma":"ellipse_speed_integral_is_curve_length","title":"Increment-squeezed elliptic primitive is the metric length","file":"theories/EllipseSpeedIntegral.v","witness":"508-d-elliptic-e","board":"#563"} *)

Theorem ellipse_speed_integral_is_curve_length :
  forall Oc rx ry rot (E : R -> R) a b,
    0 <= rx -> 0 <= ry -> a <= b ->
    increment_squeezed E (ellipse_speed rx ry) a b ->
    is_curve_length (ellipse_param Oc rx ry rot) a b (E b - E a).
Proof.
  intros Oc rx ry rot E a b Hrx Hry Hab Hsq.
  apply (speed_integral_is_curve_length
           (ellipse_param Oc rx ry rot)
           (ellipse_speed rx ry) E a b).
  apply ellipse_speed_integral_premises; assumption.
Qed.

Lemma ellipse_E_increment_sandwich :
  forall rx ry (E : R -> R) a b,
    0 <= rx -> 0 <= ry -> a <= b ->
    increment_squeezed E (ellipse_speed rx ry) a b ->
    Rmin rx ry * (b - a) <= E b - E a <= Rmax rx ry * (b - a).
Proof.
  intros rx ry E a b Hrx Hry Hab Hsq.
  apply (Hsq a b (Rmin rx ry) (Rmax rx ry) Hab Hab Hab).
  intros u _ _. apply ellipse_speed_bounds; assumption.
Qed.

(* WITNESS {"claimId":"508-d-34-quarter","topic":"metric","lemma":"ellipse_34_quarter_E_sandwich","title":"rx=3, ry=4 quarter: any squeezed E-increment lies in [3π/2, 4π/2]","file":"theories/EllipseSpeedIntegral.v","witness":"508-d-elliptic-e","board":"#563"} *)

Corollary ellipse_34_quarter_E_sandwich :
  forall (E : R -> R),
    increment_squeezed E (ellipse_speed 3 4) 0 (PI / 2) ->
    3 * (PI / 2) <= E (PI / 2) - E 0 <= 4 * (PI / 2).
Proof.
  intros E Hsq.
  pose proof PI_RGT_0 as Hpi.
  assert (Hab : 0 <= PI / 2) by lra.
  pose proof (ellipse_E_increment_sandwich 3 4 E 0 (PI / 2)
                ltac:(lra) ltac:(lra) Hab Hsq) as H.
  rewrite Rmin_left in H by lra.
  rewrite Rmax_right in H by lra.
  replace (3 * (PI / 2 - 0)) with (3 * (PI / 2)) in H by ring.
  replace (4 * (PI / 2 - 0)) with (4 * (PI / 2)) in H by ring.
  exact H.
Qed.

Corollary ellipse_34_quarter_via_speed_integral :
  forall Oc rot (E : R -> R),
    increment_squeezed E (ellipse_speed 3 4) 0 (PI / 2) ->
    is_curve_length (ellipse_param Oc 3 4 rot) 0 (PI / 2) (E (PI / 2) - E 0).
Proof.
  intros Oc rot E Hsq.
  pose proof PI_RGT_0 as Hpi.
  apply ellipse_speed_integral_is_curve_length; lra || exact Hsq.
Qed.

Print Assumptions ellipse_speed_integral_is_curve_length.
Print Assumptions ellipse_34_quarter_E_sandwich.
Print Assumptions ellipse_speed_uc.
Print Assumptions ellipse_chord_rate.
