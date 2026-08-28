(* ============================================================================
   NetTopologySuite.Proofs.ArcRectifiable
   ----------------------------------------------------------------------------
   Issue #508 (M-LEN-ZOO) arc rung: r·θ IS the metric length — the circular
   arc satisfies the corpus-canonical curve-length spec of CurveLength.v.

   Before this file, `ArcLength.arc_length r θ := r*θ` was a definition with
   sandwich companions (`chord_le_arc_length`); the reopened triage row
   (M-LEN-CS / M-LEN-CC) records exactly that gap.  Here the circle
   parameterization  t ↦ O + r·(cos t, sin t)  is proven RECTIFIABLE with

       is_curve_length (circle_param O r) a b (r * (b - a)),

   i.e. r·θ (θ = b − a) is the least upper bound of the inscribed-polyline
   lengths.  Upper half: every chain edge is a chord `2r·|sin(gap/2)| ≤ r·gap`
   (half-angle identity + the 3-axiom Taylor bound `sin_le_x`), telescoping
   to r·(b−a).  Least half: the uniform n-partition polyline
   `n · 2r·sin(θ/(2n)) ≥ rθ − rθ³/(24n²)` (lower Taylor envelope
   `pre_sin_bound`), and an archimedean choice of n forces any upper bound M
   up to rθ — epsilon-free, no limits library.

   Deliberately NOT this file: the 3-point (start/mid/end) CircularArc model
   bridge — its sweep angle lives in the atan2 / `angle_between` 4-axiom
   exception lane (see ArcChordLength.v); connecting the two models is the
   next rung.  This file stays on the explicit parameterization and is
   3-axiom.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia List Rtrigo_alt.
From NTS.Proofs Require Import Distance CurveLength ArcLength.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The explicit circle parameterization.                                      *)
(* -------------------------------------------------------------------------- *)

Definition circle_pt (O : Point) (r t : R) : Point :=
  mkPoint (px O + r * cos t) (py O + r * sin t).

Definition circle_param (O : Point) (r : R) : Curve :=
  fun t => circle_pt O r t.

(* -------------------------------------------------------------------------- *)
(* The chord of a parameter gap, exactly.                                     *)
(* -------------------------------------------------------------------------- *)

Lemma circle_chord_dist : forall (O : Point) r s t,
  0 <= r ->
  dist (circle_pt O r s) (circle_pt O r t)
  = 2 * r * Rabs (sin ((t - s) / 2)).
Proof.
Qed.

(* |sin x| <= x for 0 <= x (3-axiom: ArcLength.sin_le_x + sin_ge_0/PI2_1). *)
Lemma Rabs_sin_le : forall x, 0 <= x -> Rabs (sin x) <= x.
Proof.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: r·θ satisfies the CurveLength spec.                              *)
(* -------------------------------------------------------------------------- *)

Theorem arc_r_theta_is_curve_length : forall (O : Point) r a b,
  0 <= r -> a <= b ->
  is_curve_length (circle_param O r) a b (r * (b - a)).
Proof.
Qed.

Corollary arc_rectifiable : forall (O : Point) r a b,
  0 <= r -> a <= b -> rectifiable (circle_param O r) a b.
Proof.
Qed.

(* r·θ agrees with ArcLength.arc_length on the shared regime. *)
Corollary arc_length_meets_spec : forall (O : Point) r a b,
  0 <= r -> a <= b ->
  is_curve_length (circle_param O r) a b (arc_length r (b - a)).
Proof.
Qed.

Print Assumptions arc_r_theta_is_curve_length.
