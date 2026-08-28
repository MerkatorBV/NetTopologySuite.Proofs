(* ============================================================================
   NetTopologySuite.Proofs.EllipseLength
   ----------------------------------------------------------------------------
   Issue #508 ellipse rung 1 (the zoo attack order's next stop after the arc
   lane): the ELLIPTICALCURVE parameterization and its length against the
   CurveLength spec, at two tiers.

   The parameterization matches the oracle's `E` token (ISO/IEC 13249-3:2016
   §5.1.67 <elliptical text> projection): centre, semi-axes rx/ry, rotation,
   PARAMETRIC angle t ↦ O + R(rot)·(rx cos t, ry sin t).

   Tier 0 (UNCONDITIONAL, this file, 3-axiom):
     - ellipse_chord_le     every chord ≤ Rmax rx ry · gap (rotation is an
                            isometry; half-angle + the 3-axiom |sin x| ≤ x)
     - ellipse_length_upper any is_curve_length value L ≤ Rmax rx ry·(b−a)
       (the chord lower bound is CurveLength.curve_length_ge_chord, free)

   Tier 1 (CONDITIONAL, ADR-0001 idiom — named Section hypotheses):
     ellipse length is an incomplete elliptic integral of the second kind;
     no in-corpus integration machinery exists (the #508 grilling fixed this
     tier's contract).  The primitive E : R → R enters as a Section variable
     with two named hypotheses:
       H_E_chord   every chord is bounded by its E-increment
       H_E_approx  on fine gaps the E-increment exceeds the chord by at most
                   ε·gap (first-order tightness of the arc-length primitive)
     and the headline is Qed FROM them:
       ellipse_conditional_is_curve_length :
         is_curve_length (ellipse_param …) a b (E b − E a).
     DISCHARGE STATUS: unlike the clothoid lane (ClothoidResidual.v, whose
     hypotheses are externally witnessed Qed in clothoid-halley-coq), no
     external witness exists yet for these two — the missing method is
     in-corpus (or external) integral machinery for the elliptic-E primitive:
     a TECHNIQUE PARK item by the #508 contract.  Until then the oracle's
     LENGTH_UNIFIED quadrature + DENSIFIED cross-check (gated by Carlson
     integrals in red_length_unified_zoo_tests.py) is the differential
     witness that such an E exists numerically.

   3-axiom: no atan2 anywhere — the parameterization is explicit, and the
   least-half squeeze reuses ArcRectifiable's uniform-partition plumbing.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance CurveLength ArcLength ArcRectifiable.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The ELLIPTICALCURVE parameterization (oracle `E` token semantics).         *)
(* -------------------------------------------------------------------------- *)

Definition ellipse_pt (Oc : Point) (rx ry rot t : R) : Point :=
  mkPoint (px Oc + cos rot * (rx * cos t) - sin rot * (ry * sin t))
          (py Oc + sin rot * (rx * cos t) + cos rot * (ry * sin t)).

Definition ellipse_param (Oc : Point) (rx ry rot : R) : Curve :=
  ellipse_pt Oc rx ry rot.

(* The squared trig gap, in half-angle form. *)
Lemma trig_gap_sq : forall s t : R,
  (cos s - cos t) * (cos s - cos t) + (sin s - sin t) * (sin s - sin t)
  = 4 * (sin ((t - s) / 2) * sin ((t - s) / 2)).
Proof.
  intros s t.
  assert (Hcm : cos (t - s) = cos t * cos s + sin t * sin s)
    by apply cos_minus.
  assert (Hs2s : sin s * sin s + cos s * cos s = 1)
    by (pose proof (sin2_cos2 s) as H; unfold Rsqr in H; lra).
  assert (Hs2t : sin t * sin t + cos t * cos t = 1)
    by (pose proof (sin2_cos2 t) as H; unfold Rsqr in H; lra).
  assert (Hhalf : cos (t - s)
                  = 1 - 2 * sin ((t - s) / 2) * sin ((t - s) / 2)).
  { replace (t - s) with (2 * ((t - s) / 2)) at 1 by field.
    apply cos_2a_sin. }
  replace ((cos s - cos t) * (cos s - cos t)
           + (sin s - sin t) * (sin s - sin t))
    with ((sin s * sin s + cos s * cos s)
          + (sin t * sin t + cos t * cos t)
          - 2 * (cos t * cos s + sin t * sin s)) by ring.
  rewrite Hs2s, Hs2t, <- Hcm, Hhalf. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tier 0: the unconditional upper sandwich.                                  *)
(* -------------------------------------------------------------------------- *)

Lemma ellipse_chord_le : forall Oc rx ry rot s t,
  0 <= rx -> 0 <= ry -> s <= t ->
  dist (ellipse_param Oc rx ry rot s) (ellipse_param Oc rx ry rot t)
  <= Rmax rx ry * (t - s).
Proof.
  intros Oc rx ry rot s t Hrx Hry Hst.
  set (m := Rmax rx ry).
  assert (Hxm : rx <= m) by apply Rmax_l.
  assert (Hym : ry <= m) by apply Rmax_r.
  assert (Hm0 : 0 <= m) by lra.
  unfold ellipse_param, dist.
  assert (Hrot : sin rot * sin rot + cos rot * cos rot = 1)
    by (pose proof (sin2_cos2 rot) as H; unfold Rsqr in H; lra).
  set (su := sin ((t - s) / 2)).
  assert (Hds : dist_sq (ellipse_pt Oc rx ry rot s) (ellipse_pt Oc rx ry rot t)
                = rx * rx * ((cos s - cos t) * (cos s - cos t))
                  + ry * ry * ((sin s - sin t) * (sin s - sin t))).
  { unfold dist_sq, ellipse_pt; cbn [px py].
    replace ((px Oc + cos rot * (rx * cos s) - sin rot * (ry * sin s)
              - (px Oc + cos rot * (rx * cos t) - sin rot * (ry * sin t)))
             * (px Oc + cos rot * (rx * cos s) - sin rot * (ry * sin s)
                - (px Oc + cos rot * (rx * cos t) - sin rot * (ry * sin t)))
             + (py Oc + sin rot * (rx * cos s) + cos rot * (ry * sin s)
                - (py Oc + sin rot * (rx * cos t) + cos rot * (ry * sin t)))
               * (py Oc + sin rot * (rx * cos s) + cos rot * (ry * sin s)
                  - (py Oc + sin rot * (rx * cos t) + cos rot * (ry * sin t))))
      with ((sin rot * sin rot + cos rot * cos rot)
            * (rx * rx * ((cos s - cos t) * (cos s - cos t))
               + ry * ry * ((sin s - sin t) * (sin s - sin t)))) by ring.
    rewrite Hrot. ring. }
  assert (HX : 0 <= (cos s - cos t) * (cos s - cos t))
    by (pose proof (Rle_0_sqr (cos s - cos t)) as H; unfold Rsqr in H; lra).
  assert (HY : 0 <= (sin s - sin t) * (sin s - sin t))
    by (pose proof (Rle_0_sqr (sin s - sin t)) as H; unfold Rsqr in H; lra).
  assert (Hbound : dist_sq (ellipse_pt Oc rx ry rot s) (ellipse_pt Oc rx ry rot t)
                   <= Rsqr (2 * m * Rabs su)).
  { rewrite Hds.
    assert (Hxx : rx * rx <= m * m) by nra.
    assert (Hyy : ry * ry <= m * m) by nra.
    assert (Hcomb : rx * rx * ((cos s - cos t) * (cos s - cos t))
                    + ry * ry * ((sin s - sin t) * (sin s - sin t))
                    <= m * m * ((cos s - cos t) * (cos s - cos t)
                                + (sin s - sin t) * (sin s - sin t))) by nra.
    eapply Rle_trans; [exact Hcomb |].
    rewrite trig_gap_sq.
    assert (Habs : Rabs su * Rabs su = su * su).
    { rewrite <- Rabs_mult. apply Rabs_right.
      pose proof (Rle_0_sqr su) as H; unfold Rsqr in H; lra. }
    unfold Rsqr. fold su. rewrite <- Habs. apply Req_le. ring. }
  eapply Rle_trans.
  { apply sqrt_le_1_alt. exact Hbound. }
  rewrite sqrt_Rsqr_abs.
  rewrite (Rabs_right (2 * m * Rabs su))
    by (pose proof (Rabs_pos su); nra).
  assert (H2 : 0 <= (t - s) / 2) by lra.
  pose proof (Rabs_sin_le ((t - s) / 2) H2) as Hsin.
  assert (Hstep : 2 * m * Rabs su <= 2 * m * ((t - s) / 2)).
  { apply Rmult_le_compat_l; [lra |]. unfold su. exact Hsin. }
  lra.
Qed.

Lemma ellipse_polyline_le : forall Oc rx ry rot ts t b,
  0 <= rx -> 0 <= ry -> chain t ts b ->
  polyline_len (ellipse_param Oc rx ry rot) t (ts ++ [b])
  <= Rmax rx ry * (b - t).
Proof.
  intros Oc rx ry rot ts; induction ts as [|u tl IH]; simpl; intros t b Hrx Hry Hch.
  - pose proof (ellipse_chord_le Oc rx ry rot t b Hrx Hry Hch). lra.
  - destruct Hch as [Htu Hch].
    pose proof (ellipse_chord_le Oc rx ry rot t u Hrx Hry Htu).
    specialize (IH u b Hrx Hry Hch). lra.
Qed.

Theorem ellipse_length_upper : forall Oc rx ry rot a b L,
  0 <= rx -> 0 <= ry -> a <= b ->
  is_curve_length (ellipse_param Oc rx ry rot) a b L ->
  L <= Rmax rx ry * (b - a).
Proof.
  intros Oc rx ry rot a b L Hrx Hry Hab [_ Hlst].
  apply Hlst. intros l (ts & Hch & Hl). subst l.
  apply ellipse_polyline_le; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tier 1: the conditional headline (ADR-0001 idiom).                         *)
(* -------------------------------------------------------------------------- *)

Section EllipseConditionalTier.
  Variables (Oc : Point) (rx ry rot : R).

  Let g : Curve := ellipse_param Oc rx ry rot.

  (* The arc-length primitive: an incomplete elliptic integral of the second
     kind, characterized by the two named hypotheses below. *)
  Variable E : R -> R.

  Hypothesis H_E_chord : forall s t,
    s <= t -> dist (g s) (g t) <= E t - E s.

  Hypothesis H_E_approx : forall eps, 0 < eps ->
    exists delta, 0 < delta /\
      forall s t, s <= t -> t - s < delta ->
        E t - E s - dist (g s) (g t) <= eps * (t - s).

  Lemma ellipse_polyline_le_E : forall ts t b,
    chain t ts b -> polyline_len g t (ts ++ [b]) <= E b - E t.
  Proof.
    induction ts as [|u tl IH]; simpl; intros t b Hch.
    - pose proof (H_E_chord t b Hch). lra.
    - destruct Hch as [Htu Hch].
      pose proof (H_E_chord t u Htu).
      specialize (IH u b Hch). lra.
  Qed.

  Lemma uniform_lower_E : forall h eps,
    0 <= h ->
    (forall t, E (t + h) - E t - dist (g t) (g (t + h)) <= eps * h) ->
    forall m t0,
      E (t0 + INR m * h) - E t0 - eps * (INR m * h)
      <= polyline_len g t0 (uniform_tail t0 h m).
  Proof.
    intros h eps Hh Hedge.
    induction m as [|k IH]; intros t0; cbn [uniform_tail polyline_len].
    - simpl. replace (t0 + 0 * h) with t0 by ring. lra.
    - specialize (IH (t0 + h)). rewrite S_INR.
      pose proof (Hedge t0) as He0.
      replace (t0 + h + INR k * h) with (t0 + (INR k + 1) * h) in IH by ring.
      lra.
  Qed.

  Theorem ellipse_conditional_is_curve_length : forall a b,
    a <= b -> is_curve_length g a b (E b - E a).
  Proof.
    intros a b Hab. split.
    - intros l (ts & Hch & Hl). subst l.
      apply (ellipse_polyline_le_E ts a b Hch).
    - intros M HM.
      destruct (Rle_dec (E b - E a) M) as [Hok | Hbad]. { exact Hok. }
      exfalso.
      set (dlt := E b - E a - M).
      assert (Hdlt : 0 < dlt) by (unfold dlt; lra).
      set (eps := dlt / (b - a + 1)).
      assert (Heps : 0 < eps).
      { unfold eps. apply Rdiv_lt_0_compat; lra. }
      destruct (H_E_approx eps Heps) as (delta & Hdpos & Hd).
      destruct (exists_nat_gt ((b - a) / delta)) as [n0 Hn0].
      assert (Hnpos : 0 < INR (S n0))
        by (rewrite S_INR; pose proof (pos_INR n0); lra).
      assert (Hngt : (b - a) / delta < INR (S n0))
        by (rewrite S_INR; lra).
      set (h := (b - a) / INR (S n0)).
      assert (Hh0 : 0 <= h) by (unfold h; apply Rle_mult_inv_pos; lra).
      assert (Hnh : INR (S n0) * h = b - a) by (unfold h; field; lra).
      assert (Hhd : h < delta).
      { apply Rmult_lt_reg_l with (INR (S n0)); [lra |].
        rewrite Hnh.
        pose proof (Rmult_lt_compat_l delta _ _ Hdpos Hngt) as Hm.
        replace (delta * ((b - a) / delta)) with (b - a) in Hm
          by (field; lra).
        lra. }
      assert (Hedge : forall t,
        E (t + h) - E t - dist (g t) (g (t + h)) <= eps * h).
      { intro t.
        assert (Ht := Hd t (t + h)).
        replace (t + h - t) with h in Ht by ring.
        apply Ht; lra. }
      assert (Hins : inscribed_len g a b
                       (polyline_len g a (uniform_tail a h n0 ++ [b]))).
      { exists (uniform_tail a h n0). split; [| reflexivity].
        apply uniform_tail_chain; [exact Hh0 |].
        assert (Hb' : b = a + INR (S n0) * h) by (rewrite Hnh; ring).
        rewrite Hb', S_INR.
        pose proof (pos_INR n0). nra. }
      specialize (HM _ Hins).
      assert (Hb : b = a + INR (S n0) * h) by (rewrite Hnh; ring).
      assert (Hval : E b - E a - eps * (b - a)
                     <= polyline_len g a (uniform_tail a h n0 ++ [b])).
      { replace (uniform_tail a h n0 ++ [b])
          with (uniform_tail a h (S n0))
          by (rewrite Hb; apply uniform_tail_snoc).
        rewrite <- Hnh.
        rewrite Hb at 1.
        apply (uniform_lower_E h eps Hh0 Hedge (S n0) a). }
      assert (Hlt : eps * (b - a) < dlt).
      { assert (H1 : eps * (b - a + 1) = dlt) by (unfold eps; field; lra).
        nra. }
      unfold dlt in Hlt. lra.
  Qed.

End EllipseConditionalTier.

Print Assumptions ellipse_length_upper.
