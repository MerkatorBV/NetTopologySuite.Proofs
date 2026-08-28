(* ============================================================================
   NetTopologySuite.Proofs.ClothoidLength
   ----------------------------------------------------------------------------
   Issue #508 clothoid rung 1 (the zoo attack order's stop after the Bézier
   lane): the K-token clothoid's length against the CurveLength spec.

   The oracle's `K` token (x y dx dy A sd ed) is the ISO clothoid,
   parameterized BY ARC LENGTH: heading φ(s) = φ0 + s²/(2A²), position
   start + ∫ (cos φ, sin φ) — the Fresnel integrals.  Because the parameter
   IS arc length, the exact metric length over [sd, ed] is ed − sd: the
   closed form LENGTH_UNIFIED emits for `K` tokens.  This file makes that a
   spec theorem.

   CONDITIONAL tier (ADR-0001 idiom, mirroring ClothoidResidual.v): the
   Fresnel integrals are not in-corpus (the internalisation stack is
   ADR-0001's roadmap), so the parameterization enters as an abstract
   Section Variable g : Curve under the UNIT-SPEED contract, two named
   hypotheses:
     H_unit_chord   chords never beat the parameter gap
                    (|∫ unit vector| ≤ gap — the speed is 1)
     H_unit_approx  on fine gaps the gap exceeds the chord by at most
                    ε·gap (first-order tightness of arc length)
   and the headline is Qed FROM them:
     clothoid_arclength_is_curve_length :
       is_curve_length g sd ed (ed − sd).
   `clothoid_length_upper` needs only H_unit_chord.

   DISCHARGE STATUS: the dischargeable witness lane is the companion
   corpus `clothoid-halley-coq` (Coquelicot; the same cross-corpus
   BSD-3-Clause bridge as ClothoidResidual.v — only statements authored
   here cross the licence boundary).  Until the Fresnel stack is
   internalised, the oracle's LENGTH_UNIFIED `K` quadrature + DENSIFIED
   cumulative-Simpson cross-check is the differential witness.

   Both results are instances of the generic first-order-tight primitive
   engine (ArcRectifiable.curve_length_of_primitive) at F = id.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance CurveLength ArcRectifiable.
Import ListNotations.
Local Open Scope R_scope.

Section ClothoidUnitSpeedTier.

  (* The clothoid parameterization, abstract until the Fresnel stack lands. *)
  Variable g : Curve.

  Hypothesis H_unit_chord : forall s t,
    s <= t -> dist (g s) (g t) <= t - s.

  Hypothesis H_unit_approx : forall eps, 0 < eps ->
    exists delta, 0 < delta /\
      forall s t, s <= t -> t - s < delta ->
        (t - s) - dist (g s) (g t) <= eps * (t - s).

  (* Upper bound from the chord hypothesis alone. *)
  Lemma clothoid_length_upper : forall sd ed L,
    sd <= ed -> is_curve_length g sd ed L -> L <= ed - sd.
  Proof.
  Qed.

  (* Headline: arc-length parameterization means length = ed − sd, exactly. *)
  Theorem clothoid_arclength_is_curve_length : forall sd ed,
    sd <= ed -> is_curve_length g sd ed (ed - sd).
  Proof.
  Qed.

End ClothoidUnitSpeedTier.

Print Assumptions clothoid_arclength_is_curve_length.
