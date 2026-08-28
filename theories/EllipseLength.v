(* ============================================================================
   NetTopologySuite.Proofs.EllipseLength
   ----------------------------------------------------------------------------
   Issue #508 ellipse rungs 1–3 (the zoo attack order's next stop after the
   arc lane): the ELLIPTICALCURVE parameterization and its length against
   the CurveLength spec — the unconditional Rmin/Rmax sandwich, the rx = ry
   circular bridge, and the conditional elliptic-E tier.

   The parameterization matches the oracle's `E` token (ISO/IEC 13249-3:2016
   §5.1.67 <elliptical text> projection): centre, semi-axes rx/ry, rotation,
   PARAMETRIC angle t ↦ O + R(rot)·(rx cos t, ry sin t).

   Rung 1, Tier 0 (UNCONDITIONAL, 3-axiom):
     - ellipse_chord_le     every chord ≤ Rmax rx ry · gap (rotation is an
                            isometry; half-angle + the 3-axiom |sin x| ≤ x)
     - ellipse_length_upper any is_curve_length value L ≤ Rmax rx ry·(b−a)
       (the chord lower bound is CurveLength.curve_length_ge_chord, free)

   Rung 2 (UNCONDITIONAL, 3-axiom): the rx = ry CIRCULAR BRIDGE —
     ellipse_circular_is_curve_length : an equal-axes ellipse is a
     parameter-shifted circle (ellipse_pt_equal_axes), so its metric length
     is r·(b−a) via CurveLength's ext/shift invariances and
     ArcRectifiable.arc_r_theta_is_curve_length.  This is the oracle's
     E-token closed form as a spec theorem.

   Rung 3 (UNCONDITIONAL, 3-axiom): the Rmin LOWER SANDWICH —
     ellipse_chord_ge (chords ≥ 2·Rmin·|sin(gap/2)|, the shared
     ellipse_dist_sq computation bounded below) feeds
     ArcRectifiable.chord_envelope_lower at c = Rmin rx ry, giving
     ellipse_length_lower : Rmin rx ry·(b−a) ≤ L, assembled with Tier 0
     into ellipse_length_sandwich : Rmin·(b−a) ≤ L ≤ Rmax·(b−a) —
     pinching to exactly r·(b−a) at rx = ry, agreeing with rung 2.

   Rung 1, Tier 1 (CONDITIONAL, ADR-0001 idiom — named Section hypotheses):
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
   conditional tier instantiates ArcRectifiable's generic first-order-tight
   primitive engine (curve_length_of_primitive) at F = E.

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

(* Rotation is an isometry: the shared dist_sq computation of both chord
   bounds — the rot terms collapse under sin²+cos². *)
Lemma ellipse_dist_sq : forall Oc rx ry rot s t,
  dist_sq (ellipse_pt Oc rx ry rot s) (ellipse_pt Oc rx ry rot t)
  = rx * rx * ((cos s - cos t) * (cos s - cos t))
    + ry * ry * ((sin s - sin t) * (sin s - sin t)).
Proof.
  intros Oc rx ry rot s t.
  assert (Hrot : sin rot * sin rot + cos rot * cos rot = 1)
    by (pose proof (sin2_cos2 rot) as H; unfold Rsqr in H; lra).
  unfold dist_sq, ellipse_pt; cbn [px py].
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
  rewrite Hrot. ring.
Qed.

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
  set (su := sin ((t - s) / 2)).
  assert (HX : 0 <= (cos s - cos t) * (cos s - cos t))
    by (pose proof (Rle_0_sqr (cos s - cos t)) as H; unfold Rsqr in H; lra).
  assert (HY : 0 <= (sin s - sin t) * (sin s - sin t))
    by (pose proof (Rle_0_sqr (sin s - sin t)) as H; unfold Rsqr in H; lra).
  assert (Hbound : dist_sq (ellipse_pt Oc rx ry rot s) (ellipse_pt Oc rx ry rot t)
                   <= Rsqr (2 * m * Rabs su)).
  { rewrite ellipse_dist_sq.
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
  intros Oc rx ry rot ts t b Hrx Hry Hch.
  replace (Rmax rx ry * (b - t)) with (Rmax rx ry * b - Rmax rx ry * t)
    by ring.
  apply (polyline_le_of_chord_modulus (ellipse_param Oc rx ry rot)
           (fun x => Rmax rx ry * x) t b ts t).
  - intros s u Hts Hsu Hub. cbv beta.
    pose proof (ellipse_chord_le Oc rx ry rot s u Hrx Hry Hsu). lra.
  - lra.
  - exact Hch.
Qed.

Theorem ellipse_length_upper : forall Oc rx ry rot a b L,
  0 <= rx -> 0 <= ry -> a <= b ->
  is_curve_length (ellipse_param Oc rx ry rot) a b L ->
  L <= Rmax rx ry * (b - a).
Proof.
  intros Oc rx ry rot a b L Hrx Hry Hab HL.
  replace (Rmax rx ry * (b - a)) with (Rmax rx ry * b - Rmax rx ry * a)
    by ring.
  apply (curve_length_upper_of_chord_modulus (ellipse_param Oc rx ry rot)
           (fun x => Rmax rx ry * x) a b L); [| exact HL].
  intros s t Has Hst Htb. cbv beta.
  pose proof (ellipse_chord_le Oc rx ry rot s t Hrx Hry Hst). lra.
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

  (* The named hypotheses weaken to the (windowed) premises of the generic
     first-order-tight primitive engine, at F = E. *)
  Theorem ellipse_conditional_is_curve_length : forall a b,
    a <= b -> is_curve_length g a b (E b - E a).
  Proof.
    intros a b Hab.
    apply (curve_length_of_primitive g E a b); [| | exact Hab].
    - intros s t _ Hst _. apply H_E_chord. exact Hst.
    - intros eps Heps.
      destruct (H_E_approx eps Heps) as (delta & Hd0 & Hd).
      exists delta. split; [exact Hd0 |].
      intros s t _ Hst _ Hts. apply Hd; assumption.
  Qed.

End EllipseConditionalTier.

Print Assumptions ellipse_length_upper.

(* -------------------------------------------------------------------------- *)
(* Rung 2: the rx = ry circular bridge — the oracle's E-token closed form     *)
(* (rx = ry  =>  r·|sweep|) as a spec theorem.  An equal-axes ellipse is a    *)
(* parameter-shifted circle (the rotation folds into the angle), so the       *)
(* CurveLength shift/ext invariances hand the length to                       *)
(* ArcRectifiable.arc_r_theta_is_curve_length.  Unconditional, 3-axiom.       *)
(* -------------------------------------------------------------------------- *)

Lemma ellipse_pt_equal_axes : forall Oc r rot t,
  ellipse_pt Oc r r rot t = circle_pt Oc r (rot + t).
Proof.
  intros Oc r rot t. unfold ellipse_pt, circle_pt.
  f_equal.
  - rewrite cos_plus. ring.
  - rewrite sin_plus. ring.
Qed.

Theorem ellipse_circular_is_curve_length : forall Oc r rot a b,
  0 <= r -> a <= b ->
  is_curve_length (ellipse_param Oc r r rot) a b (r * (b - a)).
Proof.
  intros Oc r rot a b Hr Hab.
  apply (is_curve_length_ext (fun t => circle_param Oc r (rot + t))).
  { intro t. unfold ellipse_param, circle_param.
    symmetry. apply ellipse_pt_equal_axes. }
  replace (r * (b - a)) with (r * ((rot + b) - (rot + a))) by ring.
  apply (is_curve_length_shift (circle_param Oc r) rot a b).
  apply arc_r_theta_is_curve_length; [exact Hr | lra].
Qed.

Print Assumptions ellipse_circular_is_curve_length.

(* -------------------------------------------------------------------------- *)
(* Rung 3: the Rmin lower sandwich.  Tier 0 gave L ≤ Rmax rx ry·(b−a); here   *)
(* the shared ellipse_dist_sq computation flips into a chord LOWER bound     *)
(* 2·Rmin rx ry·|sin(gap/2)| — exactly the half-angle envelope of            *)
(* ArcRectifiable.chord_envelope_lower, which then forces                    *)
(* Rmin rx ry·(b−a) ≤ L for ANY is_curve_length value.  Together:            *)
(* Rmin·(b−a) ≤ L ≤ Rmax·(b−a), collapsing to L = r·(b−a) when rx = ry —     *)
(* consistent with the rung-2 bridge.  Unconditional, 3-axiom.               *)
(* -------------------------------------------------------------------------- *)

Lemma ellipse_chord_ge : forall Oc rx ry rot s t,
  0 <= rx -> 0 <= ry ->
  2 * Rmin rx ry * Rabs (sin ((t - s) / 2))
  <= dist (ellipse_param Oc rx ry rot s) (ellipse_param Oc rx ry rot t).
Proof.
  intros Oc rx ry rot s t Hrx Hry.
  set (mn := Rmin rx ry).
  assert (Hmx : mn <= rx) by apply Rmin_l.
  assert (Hmy : mn <= ry) by apply Rmin_r.
  assert (Hm0 : 0 <= mn) by (apply Rmin_glb; assumption).
  unfold ellipse_param, dist.
  set (su := sin ((t - s) / 2)).
  assert (Hbound : Rsqr (2 * mn * Rabs su)
                   <= dist_sq (ellipse_pt Oc rx ry rot s)
                              (ellipse_pt Oc rx ry rot t)).
  { rewrite ellipse_dist_sq.
    assert (HX : 0 <= (cos s - cos t) * (cos s - cos t))
      by (pose proof (Rle_0_sqr (cos s - cos t)) as H; unfold Rsqr in H; lra).
    assert (HY : 0 <= (sin s - sin t) * (sin s - sin t))
      by (pose proof (Rle_0_sqr (sin s - sin t)) as H; unfold Rsqr in H; lra).
    assert (Hxx : mn * mn <= rx * rx) by nra.
    assert (Hyy : mn * mn <= ry * ry) by nra.
    assert (Hcomb : mn * mn * ((cos s - cos t) * (cos s - cos t)
                               + (sin s - sin t) * (sin s - sin t))
                    <= rx * rx * ((cos s - cos t) * (cos s - cos t))
                       + ry * ry * ((sin s - sin t) * (sin s - sin t)))
      by nra.
    eapply Rle_trans; [| exact Hcomb].
    rewrite trig_gap_sq.
    assert (Habs : Rabs su * Rabs su = su * su).
    { rewrite <- Rabs_mult. apply Rabs_right.
      pose proof (Rle_0_sqr su) as H; unfold Rsqr in H; lra. }
    unfold Rsqr. fold su. rewrite <- Habs. apply Req_le. ring. }
  rewrite <- (sqrt_Rsqr (2 * mn * Rabs su))
    by (pose proof (Rabs_pos su); nra).
  apply sqrt_le_1_alt. exact Hbound.
Qed.

Theorem ellipse_length_lower : forall Oc rx ry rot a b L,
  0 <= rx -> 0 <= ry -> a <= b ->
  is_curve_length (ellipse_param Oc rx ry rot) a b L ->
  Rmin rx ry * (b - a) <= L.
Proof.
  intros Oc rx ry rot a b L Hrx Hry Hab [Hub _].
  apply (chord_envelope_lower (ellipse_param Oc rx ry rot)
                              (Rmin rx ry) a b L).
  - apply Rmin_glb; assumption.
  - exact Hab.
  - intros s t. apply ellipse_chord_ge; assumption.
  - exact Hub.
Qed.

(* WITNESS {"claimId":"ellipselength-ellipse-length-sandwich","topic":"arc","lemma":"ellipse_length_sandwich","title":"Ellipse metric length sandwich: Rmin*(b-a) <= L <= Rmax*(b-a) for the E-token parameterization","file":"theories/EllipseLength.v"} *)

Corollary ellipse_length_sandwich : forall Oc rx ry rot a b L,
  0 <= rx -> 0 <= ry -> a <= b ->
  is_curve_length (ellipse_param Oc rx ry rot) a b L ->
  Rmin rx ry * (b - a) <= L <= Rmax rx ry * (b - a).
Proof.
  intros Oc rx ry rot a b L Hrx Hry Hab HL.
  split.
  - apply (ellipse_length_lower Oc rx ry rot a b L); assumption.
  - apply (ellipse_length_upper Oc rx ry rot a b L); assumption.
Qed.

Print Assumptions ellipse_length_lower.
Print Assumptions ellipse_length_sandwich.
