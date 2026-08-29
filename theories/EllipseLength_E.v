(* ============================================================================
   NetTopologySuite.Proofs.EllipseLength_E
   ----------------------------------------------------------------------------
   Issue #508 ellipse next rung (P1): Technique-park discharge of the
   elliptic-E hypotheses from EllipseLength.v.

   EllipseLength.ellipse_conditional_is_curve_length remains the headline:
   IF E is a first-order-tight chord modulus THEN L = E b − E a.  This file
   does not invent a closed form.  It:

     1. Names the elliptic speed integrand
          σ²(t) = rx² sin² t + ry² cos² t
        and pins the sandwich
          Rmin(rx²,ry²) ≤ σ²(t) ≤ Rmax(rx²,ry²)
        (convex combination of the squared semi-axes).  Any honest E is an
        antiderivative of √σ²; that integral is the missing method.

     2. DISCHARGES both named hypotheses on the circular slice rx = ry = r
        at E(t) = r·t — the already-Qed closed form — so the Technique-park
        interface is inhabited in-corpus.  Tightness uses the 3-axiom
        Taylor envelope sin x ≥ x − x³/6 on [0, 4].

     3. Re-states the general (rx ≠ ry) pair as a Technique-park Section.

   No `Admitted`, no `Axiom`, no `Parameter`.  3-axiom.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveLength ArcLength ArcRectifiable
                               EllipseLength.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The elliptic speed integrand (Technique-park primitive).                   *)
(* -------------------------------------------------------------------------- *)

Definition ellipse_speed_sq (rx ry t : R) : R :=
  rx * rx * (sin t * sin t) + ry * ry * (cos t * cos t).

Lemma ellipse_speed_sq_nonneg : forall rx ry t,
  0 <= ellipse_speed_sq rx ry t.
Proof.
  intros rx ry t. unfold ellipse_speed_sq.
  pose proof (sqr_nonneg rx). pose proof (sqr_nonneg ry).
  pose proof (sqr_nonneg (sin t)). pose proof (sqr_nonneg (cos t)).
  nra.
Qed.

Lemma ellipse_speed_sq_circular : forall r t,
  ellipse_speed_sq r r t = r * r.
Proof.
  intros r t. unfold ellipse_speed_sq.
  pose proof (sin2_cos2 t) as H. unfold Rsqr in H. lra.
Qed.

Lemma ellipse_speed_sq_sandwich : forall rx ry t,
  Rmin (rx * rx) (ry * ry) <= ellipse_speed_sq rx ry t
  <= Rmax (rx * rx) (ry * ry).
Proof.
  intros rx ry t. unfold ellipse_speed_sq.
  pose proof (sin2_cos2 t) as Hsc. unfold Rsqr in Hsc.
  pose proof (sqr_nonneg (sin t)) as Hs.
  pose proof (sqr_nonneg (cos t)) as Hc.
  unfold Rsqr in Hs, Hc.
  set (a := rx * rx). set (b := ry * ry).
  set (w := sin t * sin t).
  assert (Hw : 0 <= w <= 1) by (unfold w; nra).
  assert (Hcomb : a * w + b * (1 - w) = a * w + b * (cos t * cos t)).
  { unfold w. nra. }
  rewrite <- Hcomb.
  destruct (Rle_dec a b) as [Hab | Hba].
  - rewrite Rmin_left, Rmax_right by lra.
    nra.
  - rewrite Rmin_right, Rmax_left by lra.
    nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Circular discharge: E(t) = r·t inhabits H_E_chord and H_E_approx.          *)
(* -------------------------------------------------------------------------- *)

Lemma ellipse_circular_E_chord : forall Oc r rot s t,
  0 <= r -> s <= t ->
  dist (ellipse_param Oc r r rot s) (ellipse_param Oc r r rot t)
  <= (r * t) - (r * s).
Proof.
  intros Oc r rot s t Hr Hst.
  pose proof (ellipse_chord_le Oc r r rot s t Hr Hr Hst) as Hcr.
  rewrite Rmax_left in Hcr by lra.
  lra.
Qed.

Lemma ellipse_circular_E_approx : forall Oc r rot eps,
  0 <= r -> 0 < eps ->
  exists delta, 0 < delta /\
    forall s t, s <= t -> t - s < delta ->
      (r * t) - (r * s)
      - dist (ellipse_param Oc r r rot s) (ellipse_param Oc r r rot t)
      <= eps * (t - s).
Proof.
  intros Oc r rot eps Hr Heps.
  destruct (Req_dec r 0) as [Hr0 | Hrnz].
  - exists 1. split; [lra |].
    intros s t Hst _.
    subst r.
    pose proof (ellipse_chord_le Oc 0 0 rot s t (Rle_refl 0) (Rle_refl 0) Hst)
      as Hch.
    rewrite Rmax_left in Hch by lra.
    pose proof (dist_nonneg
                  (ellipse_param Oc 0 0 rot s)
                  (ellipse_param Oc 0 0 rot t)).
    lra.
  - assert (Hrpos : 0 < r) by lra.
    (* gap² ≤ 24·eps/r  ⇒  r·gap³/24 ≤ eps·gap; cap at 2 so gap/2 ≤ 1 ≤ 4. *)
    set (delta := Rmin 2 (sqrt (24 * eps / r))).
    exists delta.
    assert (Hdpos : 0 < delta).
    { unfold delta. apply Rmin_glb_lt; [lra |].
      apply sqrt_lt_R0. apply Rdiv_lt_0_compat; [nra | exact Hrpos]. }
    split; [exact Hdpos |].
    intros s t Hst Hdlt.
    set (gap := t - s).
    assert (Hgap0 : 0 <= gap) by (unfold gap; lra).
    assert (Hgap2 : gap < 2).
    { unfold gap. eapply Rlt_le_trans; [exact Hdlt |].
      unfold delta. apply Rmin_l. }
    pose proof (ellipse_chord_ge Oc r r rot s t Hr Hr) as Hlo.
    rewrite Rmin_left in Hlo by lra.
    assert (Hsinpos : 0 <= sin (gap / 2)).
    { apply sin_ge_0; [lra |]. pose proof PI_RGT_0. lra. }
    rewrite (Rabs_right (sin (gap / 2))) in Hlo by lra.
    unfold ellipse_param in Hlo.
    assert (Hdiff :
      r * t - r * s
      - dist (ellipse_param Oc r r rot s) (ellipse_param Oc r r rot t)
      <= r * gap - 2 * r * sin (gap / 2)).
    { unfold ellipse_param, gap. lra. }
    eapply Rle_trans; [exact Hdiff |].
    assert (Hx : 0 <= gap / 2) by lra.
    assert (Hx4 : gap / 2 <= 4) by lra.
    pose proof (sin_lower_taylor (gap / 2) Hx Hx4) as Htaylor.
    assert (Hcalc :
      r * gap - 2 * r * sin (gap / 2)
      <= r * gap - 2 * r * (gap / 2 - (gap / 2) ^ 3 / 6)).
    { apply Rplus_le_compat_l, Ropp_le_contravar.
      apply Rmult_le_compat_l; [lra | exact Htaylor]. }
    eapply Rle_trans; [exact Hcalc |].
    replace (r * gap - 2 * r * (gap / 2 - (gap / 2) ^ 3 / 6))
      with (r * (gap ^ 3 / 24)) by (unfold Rdiv; ring).
    destruct (Req_dec gap 0) as [Hg0 | Hgnz].
    { rewrite Hg0. nra. }
    assert (Hgappos : 0 < gap) by lra.
    (* r·gap³/24 ≤ eps·gap  iff  r·gap²/24 ≤ eps *)
    apply (Rmult_le_reg_r (/ gap)); [apply Rinv_0_lt_compat; exact Hgappos |].
    replace (r * (gap ^ 3 / 24) * / gap)
      with (r * (gap * gap) / 24) by (unfold Rdiv; field; lra).
    replace (eps * gap * / gap) with eps by (field; lra).
    assert (Hgapsq : gap * gap < delta * delta) by nra.
    assert (Hbound : delta * delta <= 24 * eps / r).
    { unfold delta.
      pose proof (Rmin_r 2 (sqrt (24 * eps / r))) as Hm.
      assert (Hsqrt : 0 <= sqrt (24 * eps / r)) by apply sqrt_pos.
      assert (Hmin0 : 0 <= Rmin 2 (sqrt (24 * eps / r)))
        by (apply Rmin_glb; lra).
      apply Rsqr_incr_1 in Hm; [| exact Hmin0 | exact Hsqrt].
      unfold Rsqr in Hm.
      rewrite sqrt_sqrt in Hm
        by (apply Rlt_le, Rdiv_lt_0_compat; [nra | exact Hrpos]).
      exact Hm. }
    apply Rmult_le_reg_r with (r := 24); [lra |].
    replace (r * (gap * gap) / 24 * 24) with (r * (gap * gap))
      by (field; lra).
    replace (eps * 24) with (24 * eps) by ring.
    apply Rmult_le_reg_r with (r := / r); [apply Rinv_0_lt_compat; exact Hrpos |].
    replace (r * (gap * gap) * / r) with (gap * gap) by (field; lra).
    replace (24 * eps * / r) with (24 * eps / r) by (unfold Rdiv; ring).
    apply Rlt_le.
    eapply Rlt_le_trans; [exact Hgapsq | exact Hbound].
Qed.

(* WITNESS {"claimId":"ellipselengthe-ellipse-circular-e-discharges","topic":"arc","lemma":"ellipse_circular_E_discharges","title":"Circular slice rx=ry discharges H_E_chord and H_E_approx at E(t)=r*t","file":"theories/EllipseLength_E.v"} *)

Theorem ellipse_circular_E_discharges : forall Oc r rot a b,
  0 <= r -> a <= b ->
  is_curve_length (ellipse_param Oc r r rot) a b ((r * b) - (r * a)).
Proof.
  intros Oc r rot a b Hr Hab.
  apply (ellipse_conditional_is_curve_length Oc r r rot (fun t => r * t)).
  - intros s t Hst. apply ellipse_circular_E_chord; assumption.
  - intros eps Heps.
    apply (ellipse_circular_E_approx Oc r rot eps); assumption.
  - exact Hab.
Qed.

(* -------------------------------------------------------------------------- *)
(* Technique park: the general elliptic-E integrand is still external.        *)
(* -------------------------------------------------------------------------- *)

Section EllipseEllipticEPark.
  Variables (Oc : Point) (rx ry rot : R).
  Hypothesis Hrx : 0 <= rx.
  Hypothesis Hry : 0 <= ry.
  Variable E : R -> R.

  Hypothesis H_E_chord : forall s t,
    s <= t ->
    dist (ellipse_param Oc rx ry rot s) (ellipse_param Oc rx ry rot t)
    <= E t - E s.

  Hypothesis H_E_approx : forall eps, 0 < eps ->
    exists delta, 0 < delta /\
      forall s t, s <= t -> t - s < delta ->
        E t - E s
        - dist (ellipse_param Oc rx ry rot s) (ellipse_param Oc rx ry rot t)
        <= eps * (t - s).

  Theorem ellipse_park_is_curve_length : forall a b,
    a <= b ->
    is_curve_length (ellipse_param Oc rx ry rot) a b (E b - E a).
  Proof.
    intros a b Hab.
    apply (ellipse_conditional_is_curve_length Oc rx ry rot E);
      assumption.
  Qed.

End EllipseEllipticEPark.

Print Assumptions ellipse_circular_E_discharges.
Print Assumptions ellipse_speed_sq_sandwich.
Print Assumptions ellipse_park_is_curve_length.
