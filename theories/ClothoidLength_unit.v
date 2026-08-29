(* ============================================================================
   NetTopologySuite.Proofs.ClothoidLength_unit
   ----------------------------------------------------------------------------
   Issue #508 clothoid next rung (P1): windowed unit-speed discharge of
   ClothoidLength.v's H_unit_chord / H_unit_approx.

   The K-token closed form remains ed − sd.  This file does NOT quantify
   tightness over all of R (false for the Euler spiral) and does NOT
   internalise Fresnel integrals (ADR-0001 still parks that stack).

   Two inhabitants of the windowed contract, both 3-axiom:

     1. In-corpus: any UNIT-SPEED STRAIGHT segment
          g(s) = P + s·u    with |u| = 1
        has chord = gap exactly on every window, so both hypotheses
        discharge and clothoid_arclength_is_curve_length instantiates.
        This shows the #555 interface is inhabited without Fresnel.

     2. Technique park: the concrete Euler spiral (ISO clothoid,
        φ(s) = φ0 + s²/(2A²), Fresnel position) remains an external
        witness in clothoid-halley-coq (Coquelicot).  Only the statement
        that "the windowed contract is the discharge obligation" is
        authored here — the same BSD-3-Clause / EUPL-1.2 licence split
        as ClothoidResidual.v.

   No `Admitted`, no `Axiom`, no `Parameter`.  3-axiom.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveLength ArcRectifiable
                               ClothoidLength.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* In-corpus inhabitant: unit-speed straight line.                            *)
(* -------------------------------------------------------------------------- *)

Definition unit_line (P : Point) (ux uy : R) (s : R) : Point :=
  mkPoint (px P + s * ux) (py P + s * uy).

Definition unit_line_param (P : Point) (ux uy : R) : Curve :=
  unit_line P ux uy.

Lemma unit_line_chord : forall P ux uy s t,
  ux * ux + uy * uy = 1 ->
  dist (unit_line_param P ux uy s) (unit_line_param P ux uy t)
  = Rabs (t - s).
Proof.
  intros P ux uy s t Hu.
  unfold unit_line_param, unit_line, dist, dist_sq; cbn [px py].
  replace ((px P + s * ux - (px P + t * ux))
           * (px P + s * ux - (px P + t * ux))
           + (py P + s * uy - (py P + t * uy))
             * (py P + s * uy - (py P + t * uy)))
    with ((t - s) * (t - s) * (ux * ux + uy * uy)) by ring.
  rewrite Hu.
  replace ((t - s) * (t - s) * 1) with (Rsqr (t - s)) by (unfold Rsqr; ring).
  rewrite sqrt_Rsqr_abs. reflexivity.
Qed.

Lemma unit_line_H_chord : forall P ux uy sd ed s t,
  ux * ux + uy * uy = 1 ->
  sd <= s -> s <= t -> t <= ed ->
  dist (unit_line_param P ux uy s) (unit_line_param P ux uy t) <= t - s.
Proof.
  intros P ux uy sd ed s t Hu _ Hst _.
  rewrite (unit_line_chord P ux uy s t Hu).
  rewrite Rabs_right; lra.
Qed.

Lemma unit_line_H_approx : forall P ux uy sd ed eps,
  ux * ux + uy * uy = 1 ->
  0 < eps ->
  exists delta, 0 < delta /\
    forall s t, sd <= s -> s <= t -> t <= ed -> t - s < delta ->
      (t - s)
      - dist (unit_line_param P ux uy s) (unit_line_param P ux uy t)
      <= eps * (t - s).
Proof.
  intros P ux uy sd ed eps Hu Heps.
  exists 1. split; [lra |].
  intros s t _ Hst _ _.
  rewrite (unit_line_chord P ux uy s t Hu).
  rewrite Rabs_right by lra.
  nra.
Qed.

(* WITNESS {"claimId":"clothoidlengthunit-unit-line-discharges","topic":"metric","lemma":"unit_line_discharges_window","title":"Unit-speed straight line discharges the windowed K-token contract; length is ed-sd","file":"theories/ClothoidLength_unit.v"} *)

Theorem unit_line_discharges_window : forall P ux uy sd ed,
  ux * ux + uy * uy = 1 ->
  sd <= ed ->
  is_curve_length (unit_line_param P ux uy) sd ed (ed - sd).
Proof.
  intros P ux uy sd ed Hu Hwin.
  apply (clothoid_arclength_is_curve_length
           (unit_line_param P ux uy) sd ed Hwin).
  - intros s t Hs Hst Ht.
    apply (unit_line_H_chord P ux uy sd ed s t Hu Hs Hst Ht).
  - intros eps Heps.
    apply (unit_line_H_approx P ux uy sd ed eps Hu Heps).
Qed.

(* -------------------------------------------------------------------------- *)
(* Technique park: the Euler spiral's windowed contract is external.          *)
(* -------------------------------------------------------------------------- *)

Section ClothoidFresnelPark.
  (* Concrete ISO clothoid parameterization, abstract until ADR-0001
     internalises Fresnel.  The window [sd, ed] is the K-token's own. *)
  Variable g : Curve.
  Variables sd ed : R.
  Hypothesis H_window : sd <= ed.

  Hypothesis H_unit_chord : forall s t,
    sd <= s -> s <= t -> t <= ed -> dist (g s) (g t) <= t - s.

  Hypothesis H_unit_approx : forall eps, 0 < eps ->
    exists delta, 0 < delta /\
      forall s t, sd <= s -> s <= t -> t <= ed -> t - s < delta ->
        (t - s) - dist (g s) (g t) <= eps * (t - s).

  (* Re-registration: the #555 headline, with the discharge pointer named
     as clothoid-halley-coq (windowed, never global). *)
  Theorem clothoid_fresnel_park_length :
    is_curve_length g sd ed (ed - sd).
  Proof.
    apply (clothoid_arclength_is_curve_length g sd ed H_window
             H_unit_chord H_unit_approx).
  Qed.

End ClothoidFresnelPark.

Print Assumptions unit_line_discharges_window.
Print Assumptions clothoid_fresnel_park_length.
