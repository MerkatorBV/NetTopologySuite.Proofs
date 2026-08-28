(* ============================================================================
   NetTopologySuite.Proofs.NurbsQuadraticLength
   ----------------------------------------------------------------------------
   Issue #508 NURBS rung 1 (the zoo attack order's last lane): the degree-2
   single-span `N` token — the RATIONAL QUADRATIC Bézier, the conic form
   engines actually store arcs in (the oracle's golden vector pins the
   w = √2/2 quarter circle at π/2) — against the CurveLength spec.

   The parameterization matches the oracle's `N` token at d = 2: control
   points p0 p1 p2 with weights w0 w1 w2, homogeneous Bernstein quadratic,
   parameter domain [0, 1]:

     C(t) = (Σ B_i(t)·w_i·P_i) / (Σ B_i(t)·w_i).

   Two unconditional results, both 3-axiom:

   EQUAL-WEIGHTS DEGENERATION (the N ⊃ B token inclusion as a spec theorem):
     with w0 = w1 = w2 = w ≠ 0 the denominator collapses (partition of
     unity) and the rational quadratic IS the polynomial quadratic
     pointwise, so `is_curve_length` transfers as an iff — and chains
     through Bezier3Length's elevation exactness to the stored cubic.

   WEIGHT-CONDITIONED CONTROL-NET LIPSCHITZ BOUND:
     the rational chord factors through the divided difference —
       C(t) − C(s) = (t−s) · Σ_{i<j} c_ij·w_i·w_j·(P_j − P_i) / (D(t)·D(s))
     where the antisymmetrized Bernstein products B_i(t)B_j(s) − B_i(s)B_j(t)
     all carry the factor (s−t) with cofactors
       c_01 = 2(1−s)(1−t),  c_02 = s + t − 2st,  c_12 = 2st,
     each ≥ 0 with c_01 + c_02 + c_12 ≤ 2 on [0,1]², and the denominator is
     bounded below by the least weight (partition of unity again).  With
     0 < wmin ≤ w_i ≤ wmax every chord is ≤ 2·(wmax/wmin)²·(max net
     edge)·(t−s), telescoping to
       `nurbs2_length_upper` : L ≤ 2·(wmax/wmin)²·nurbs2_net_max·(b−a)
     for any is_curve_length value over [a,b] ⊆ [0,1] — derivative-free.
     The chord lower bound is CurveLength.curve_length_ge_chord, free.
     General degree, knot spans, and the conditional exact tier (the
     rational arc-length primitive) are future rungs.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance CurveLength Bezier3Length.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The degree-2 single-span rational parameterization (oracle `N`, d = 2).   *)
(* -------------------------------------------------------------------------- *)

Definition bern2_0 (t : R) : R := (1-t)*(1-t).
Definition bern2_1 (t : R) : R := 2*(t*(1-t)).
Definition bern2_2 (t : R) : R := t*t.

Definition nurbs2_den (w0 w1 w2 t : R) : R :=
  bern2_0 t * w0 + bern2_1 t * w1 + bern2_2 t * w2.

Definition nurbs2_pt (p0 p1 p2 : Point) (w0 w1 w2 t : R) : Point :=
  mkPoint ((bern2_0 t * (w0 * px p0) + bern2_1 t * (w1 * px p1)
            + bern2_2 t * (w2 * px p2)) / nurbs2_den w0 w1 w2 t)
          ((bern2_0 t * (w0 * py p0) + bern2_1 t * (w1 * py p1)
            + bern2_2 t * (w2 * py p2)) / nurbs2_den w0 w1 w2 t).

Definition nurbs2_param (p0 p1 p2 : Point) (w0 w1 w2 : R) : Curve :=
  nurbs2_pt p0 p1 p2 w0 w1 w2.

Definition nurbs2_net_max (p0 p1 p2 : Point) : R :=
  Rmax (dist p0 p1) (Rmax (dist p0 p2) (dist p1 p2)).

(* -------------------------------------------------------------------------- *)
(* Partition of unity and the denominator's weight floor.                     *)
(* -------------------------------------------------------------------------- *)

Lemma nurbs2_den_lb : forall w0 w1 w2 wmin t,
  0 <= t -> t <= 1 -> 0 < wmin ->
  wmin <= w0 -> wmin <= w1 -> wmin <= w2 ->
  wmin <= nurbs2_den w0 w1 w2 t.
Proof.
Qed.

(* -------------------------------------------------------------------------- *)
(* Equal-weights degeneration: the rational quadratic IS the quadratic.       *)
(* -------------------------------------------------------------------------- *)

Lemma nurbs2_equal_weights_pt : forall p0 p1 p2 w t,
  w <> 0 ->
  nurbs2_pt p0 p1 p2 w w w t = bezier2_pt p0 p1 p2 t.
Proof.
Qed.

Theorem nurbs2_equal_weights_length : forall p0 p1 p2 w a b L,
  w <> 0 ->
  (is_curve_length (bezier2_param p0 p1 p2) a b L <->
   is_curve_length (nurbs2_param p0 p1 p2 w w w) a b L).
Proof.
Qed.

Corollary nurbs2_equal_weights_cubic : forall p0 p1 p2 w a b L,
  w <> 0 ->
  (is_curve_length (nurbs2_param p0 p1 p2 w w w) a b L <->
   is_curve_length
     (bezier3_param p0 (elevate_mid1 p0 p1) (elevate_mid2 p1 p2) p2) a b L).
Proof.
Qed.

(* -------------------------------------------------------------------------- *)
(* The weight-conditioned control-net Lipschitz bound.                        *)
(* -------------------------------------------------------------------------- *)

Lemma nurbs2_chord_le : forall p0 p1 p2 w0 w1 w2 wmin wmax s t,
  0 < wmin ->
  wmin <= w0 -> w0 <= wmax ->
  wmin <= w1 -> w1 <= wmax ->
  wmin <= w2 -> w2 <= wmax ->
  0 <= s -> s <= t -> t <= 1 ->
  dist (nurbs2_param p0 p1 p2 w0 w1 w2 s) (nurbs2_param p0 p1 p2 w0 w1 w2 t)
  <= 2 * ((wmax * wmax) / (wmin * wmin)) * nurbs2_net_max p0 p1 p2 * (t - s).
Proof.
Qed.

Theorem nurbs2_length_upper : forall p0 p1 p2 w0 w1 w2 wmin wmax a b L,
  0 < wmin ->
  wmin <= w0 -> w0 <= wmax ->
  wmin <= w1 -> w1 <= wmax ->
  wmin <= w2 -> w2 <= wmax ->
  0 <= a -> a <= b -> b <= 1 ->
  is_curve_length (nurbs2_param p0 p1 p2 w0 w1 w2) a b L ->
  L <= 2 * ((wmax * wmax) / (wmin * wmin)) * nurbs2_net_max p0 p1 p2 * (b - a).
Proof.
Qed.

Print Assumptions nurbs2_equal_weights_cubic.
Print Assumptions nurbs2_length_upper.
