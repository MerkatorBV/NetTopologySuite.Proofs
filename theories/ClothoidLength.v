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
   Section Variable g : Curve under the UNIT-SPEED contract ON THE TOKEN'S
   OWN WINDOW [sd, ed], two named hypotheses:
     H_unit_chord   chords within the window never beat the parameter gap
                    (|∫ unit vector| ≤ gap — the speed is 1)
     H_unit_approx  on fine gaps within the window the gap exceeds the
                    chord by at most ε·gap (first-order tightness)
   and the headline is Qed FROM them:
     clothoid_arclength_is_curve_length : is_curve_length g sd ed (ed − sd)
   as the generic first-order-tight primitive engine
   (ArcRectifiable.curve_length_of_primitive) at F = id;
   `clothoid_length_upper` needs only H_unit_chord (the chord-modulus
   telescoping, not the full engine).

   The WINDOW matters: the Euler spiral wraps toward its asymptotic point,
   so no GLOBAL tightness δ exists for it — but on every compact window the
   curvature is bounded and the windowed contract holds.  Stating the
   hypotheses on [sd, ed] keeps them dischargeable for the concrete curve.

   DISCHARGE STATUS: the dischargeable witness lane is the companion
   corpus `clothoid-halley-coq` (Coquelicot; the same cross-corpus
   BSD-3-Clause bridge as ClothoidResidual.v — only statements authored
   here cross the licence boundary).  Until the Fresnel stack is
   internalised, the oracle's LENGTH_UNIFIED `K` quadrature + DENSIFIED
   cumulative-Simpson cross-check is the differential witness.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals.
From NTS.Proofs Require Import Distance CurveLength ArcRectifiable.
Local Open Scope R_scope.

Section ClothoidUnitSpeedTier.

  (* The clothoid parameterization, abstract until the Fresnel stack lands,
     and the K token's arc-length window. *)
  Variable g : Curve.
  Variables sd ed : R.

  Hypothesis H_window : sd <= ed.

  Hypothesis H_unit_chord : forall s t,
    sd <= s -> s <= t -> t <= ed -> dist (g s) (g t) <= t - s.

  Hypothesis H_unit_approx : forall eps, 0 < eps ->
    exists delta, 0 < delta /\
      forall s t, sd <= s -> s <= t -> t <= ed -> t - s < delta ->
        (t - s) - dist (g s) (g t) <= eps * (t - s).

  (* Upper bound from the chord hypothesis alone. *)
  Lemma clothoid_length_upper : forall L,
    is_curve_length g sd ed L -> L <= ed - sd.
  Proof.
    intros L HL.
    apply (curve_length_upper_of_chord_modulus g (fun x => x) sd ed L);
      [| exact HL].
    intros s t Has Hst Htb. cbv beta. apply H_unit_chord; assumption.
  Qed.

  (* Headline: arc-length parameterization means length = ed − sd, exactly. *)
  (* WITNESS {"claimId":"clothoidlength-clothoid-arclength-is-curve-length","topic":"metric","lemma":"clothoid_arclength_is_curve_length","title":"Arc-length-parameterized clothoid has metric length exactly ed - sd (K-token closed form)","file":"theories/ClothoidLength.v"} *)
  Theorem clothoid_arclength_is_curve_length :
    is_curve_length g sd ed (ed - sd).
  Proof.
    apply (curve_length_of_primitive g (fun x => x) sd ed
             H_unit_chord H_unit_approx H_window).
  Qed.

End ClothoidUnitSpeedTier.

Print Assumptions clothoid_arclength_is_curve_length.
