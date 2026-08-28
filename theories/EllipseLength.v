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
Qed.

(* -------------------------------------------------------------------------- *)
(* Tier 0: the unconditional upper sandwich.                                  *)
(* -------------------------------------------------------------------------- *)

Lemma ellipse_chord_le : forall Oc rx ry rot s t,
  0 <= rx -> 0 <= ry -> s <= t ->
  dist (ellipse_param Oc rx ry rot s) (ellipse_param Oc rx ry rot t)
  <= Rmax rx ry * (t - s).
Proof.
Qed.

Lemma ellipse_polyline_le : forall Oc rx ry rot ts t b,
  0 <= rx -> 0 <= ry -> chain t ts b ->
  polyline_len (ellipse_param Oc rx ry rot) t (ts ++ [b])
  <= Rmax rx ry * (b - t).
Proof.
Qed.

Theorem ellipse_length_upper : forall Oc rx ry rot a b L,
  0 <= rx -> 0 <= ry -> a <= b ->
  is_curve_length (ellipse_param Oc rx ry rot) a b L ->
  L <= Rmax rx ry * (b - a).
Proof.
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
  Qed.

  Lemma uniform_lower_E : forall h eps,
    0 <= h ->
    (forall t, E (t + h) - E t - dist (g t) (g (t + h)) <= eps * h) ->
    forall m t0,
      E (t0 + INR m * h) - E t0 - eps * (INR m * h)
      <= polyline_len g t0 (uniform_tail t0 h m).
  Proof.
  Qed.

  Theorem ellipse_conditional_is_curve_length : forall a b,
    a <= b -> is_curve_length g a b (E b - E a).
  Proof.
  Qed.

End EllipseConditionalTier.

Print Assumptions ellipse_length_upper.
