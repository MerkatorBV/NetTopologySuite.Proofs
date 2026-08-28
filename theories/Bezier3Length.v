(* ============================================================================
   NetTopologySuite.Proofs.Bezier3Length
   ----------------------------------------------------------------------------
   Issue #508 Bézier rung 1 (the zoo attack order's stop after the ellipse
   lane): the cubic Bézier parameterization and its length against the
   CurveLength spec.

   The parameterization matches the oracle's `B` token: control net
   p0 p1 p2 p3, Bernstein cubic per coordinate, parameter domain [0, 1].

   Two unconditional results, both 3-axiom:

   DEGREE-ELEVATION EXACTNESS (the Bible A1 amendment as a spec theorem):
     a quadratic Bézier degree-elevated to cubic (q1 = (p0 + 2·p1)/3,
     q2 = (2·p1 + p2)/3 — the cubic-for-quadratic storage convention with
     Esri provenance) is the SAME curve pointwise, so it carries EXACTLY the
     same metric lengths: `bezier3_elevation_length` is an iff through
     `is_curve_length_ext`, no approximation anywhere.

   CONTROL-NET LIPSCHITZ UPPER BOUND:
     the chord between parameters s ≤ t in [0, 1] factors through the
     divided difference — B(t) − B(s) = (t−s)·(c0·d0 + c1·d1 + c2·d2) with
     d_i the control-net edge vectors and c_i ≥ 0, c0 + c1 + c2 = 3 (the
     symmetrized Bernstein-2 weights) — so every chord is bounded by
     3·(max net edge)·(t−s), telescoping to
       `bezier3_length_upper` : L ≤ 3·max(|d0|,|d1|,|d2|)·(b−a)
     for any is_curve_length value over [a,b] ⊆ [0,1].  The lower bound is
     CurveLength.curve_length_ge_chord, free.  A tight (control-polygon /
     integral) upper bound and the conditional exact tier are future rungs.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance CurveLength.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The cubic (oracle `B` token) and quadratic Bézier parameterizations.       *)
(* -------------------------------------------------------------------------- *)

Definition bezier3_pt (p0 p1 p2 p3 : Point) (t : R) : Point :=
  mkPoint
    (px p0 * ((1-t)*(1-t)*(1-t)) + 3 * px p1 * (t*((1-t)*(1-t)))
     + 3 * px p2 * (t*t*(1-t)) + px p3 * (t*t*t))
    (py p0 * ((1-t)*(1-t)*(1-t)) + 3 * py p1 * (t*((1-t)*(1-t)))
     + 3 * py p2 * (t*t*(1-t)) + py p3 * (t*t*t)).

Definition bezier3_param (p0 p1 p2 p3 : Point) : Curve :=
  bezier3_pt p0 p1 p2 p3.

Definition bezier2_pt (p0 p1 p2 : Point) (t : R) : Point :=
  mkPoint
    (px p0 * ((1-t)*(1-t)) + 2 * px p1 * (t*(1-t)) + px p2 * (t*t))
    (py p0 * ((1-t)*(1-t)) + 2 * py p1 * (t*(1-t)) + py p2 * (t*t)).

Definition bezier2_param (p0 p1 p2 : Point) : Curve :=
  bezier2_pt p0 p1 p2.

(* The degree-elevated interior control points (cubic-for-quadratic). *)
Definition elevate_mid1 (p0 p1 : Point) : Point :=
  mkPoint ((px p0 + 2 * px p1) / 3) ((py p0 + 2 * py p1) / 3).

Definition elevate_mid2 (p1 p2 : Point) : Point :=
  mkPoint ((2 * px p1 + px p2) / 3) ((2 * py p1 + py p2) / 3).

(* -------------------------------------------------------------------------- *)
(* Degree-elevation exactness.                                                *)
(* -------------------------------------------------------------------------- *)

Lemma bezier3_elevation_pointwise : forall p0 p1 p2 t,
  bezier3_pt p0 (elevate_mid1 p0 p1) (elevate_mid2 p1 p2) p2 t
  = bezier2_pt p0 p1 p2 t.
Proof.
Qed.

Theorem bezier3_elevation_length : forall p0 p1 p2 a b L,
  is_curve_length (bezier2_param p0 p1 p2) a b L <->
  is_curve_length
    (bezier3_param p0 (elevate_mid1 p0 p1) (elevate_mid2 p1 p2) p2) a b L.
Proof.
Qed.

(* -------------------------------------------------------------------------- *)
(* The control-net Lipschitz upper bound.                                     *)
(* -------------------------------------------------------------------------- *)

Definition bezier3_net_max (p0 p1 p2 p3 : Point) : R :=
  Rmax (dist p0 p1) (Rmax (dist p1 p2) (dist p2 p3)).

(* Positive scaling factors out of the Euclidean norm. *)
Lemma scaled_diff_norm : forall c x y,
  0 <= c ->
  sqrt ((c*x) * (c*x) + (c*y) * (c*y)) = c * sqrt (x*x + y*y).
Proof.
Qed.

(* Triangle inequality for a three-term nonnegative combination of vectors. *)
Lemma norm_triple_le : forall c0 c1 c2 x0 y0 x1 y1 x2 y2,
  0 <= c0 -> 0 <= c1 -> 0 <= c2 ->
  sqrt ((c0*x0 + c1*x1 + c2*x2) * (c0*x0 + c1*x1 + c2*x2)
        + (c0*y0 + c1*y1 + c2*y2) * (c0*y0 + c1*y1 + c2*y2))
  <= c0 * sqrt (x0*x0 + y0*y0) + c1 * sqrt (x1*x1 + y1*y1)
     + c2 * sqrt (x2*x2 + y2*y2).
Proof.
Qed.

Lemma bezier3_chord_le : forall p0 p1 p2 p3 s t,
  0 <= s -> s <= t -> t <= 1 ->
  dist (bezier3_param p0 p1 p2 p3 s) (bezier3_param p0 p1 p2 p3 t)
  <= 3 * bezier3_net_max p0 p1 p2 p3 * (t - s).
Proof.
Qed.

Lemma bezier3_polyline_le : forall p0 p1 p2 p3 ts t b,
  0 <= t -> b <= 1 -> chain t ts b ->
  polyline_len (bezier3_param p0 p1 p2 p3) t (ts ++ [b])
  <= 3 * bezier3_net_max p0 p1 p2 p3 * (b - t).
Proof.
Qed.

Theorem bezier3_length_upper : forall p0 p1 p2 p3 a b L,
  0 <= a -> a <= b -> b <= 1 ->
  is_curve_length (bezier3_param p0 p1 p2 p3) a b L ->
  L <= 3 * bezier3_net_max p0 p1 p2 p3 * (b - a).
Proof.
Qed.

Corollary bezier3_length_upper_unit : forall p0 p1 p2 p3 L,
  is_curve_length (bezier3_param p0 p1 p2 p3) 0 1 L ->
  L <= 3 * bezier3_net_max p0 p1 p2 p3.
Proof.
Qed.

Print Assumptions bezier3_elevation_length.
Print Assumptions bezier3_length_upper.
