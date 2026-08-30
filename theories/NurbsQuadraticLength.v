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
     each ≥ 0 on [0,1]², and the denominator is bounded below by the least
     weight (partition of unity again).  The (0,2) term regroups through
     P2 − P0 = (P1 − P0) + (P2 − P1) with c_01 + 2·c_02 + c_12 = 2 EXACTLY,
     so the net max needs only the CONSECUTIVE edges.  With
     0 < wmin ≤ w_i ≤ wmax every chord is ≤ 2·(wmax/wmin)²·max(|P1−P0|,
     |P2−P1|)·(t−s), telescoping to
       `nurbs2_length_upper` : L ≤ 2·(wmax/wmin)²·nurbs2_net_max·(b−a)
     for any is_curve_length value over [a,b] ⊆ [0,1] — derivative-free.
     At w = 1 this closes the polynomial quadratic too
     (`bezier2_length_upper`).  The chord lower bound is
     CurveLength.curve_length_ge_chord, free.

     The quarter-circle golden vector is MOTIVATION, not a theorem here:
     nothing in this file instantiates w = √2/2 or proves L = π/2 — the
     conic exact value is a later rung, alongside general degree, knot
     spans, and the conditional exact tier (the rational arc-length
     primitive through the engine).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Export BernsteinBasis.
From NTS.Proofs Require Import Distance CurveLength Bezier3Length.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* The degree-2 single-span rational parameterization (oracle `N`, d = 2).   *)
(* -------------------------------------------------------------------------- *)

Definition nurbs2_den (w0 w1 w2 t : R) : R :=
  bern2_0 t * w0 + bern2_1 t * w1 + bern2_2 t * w2.

Definition nurbs2_pt (p0 p1 p2 : Point) (w0 w1 w2 t : R) : Point :=
  mkPoint ((bern2_0 t * (w0 * px p0) + bern2_1 t * (w1 * px p1)
            + bern2_2 t * (w2 * px p2)) / nurbs2_den w0 w1 w2 t)
          ((bern2_0 t * (w0 * py p0) + bern2_1 t * (w1 * py p1)
            + bern2_2 t * (w2 * py p2)) / nurbs2_den w0 w1 w2 t).

Definition nurbs2_param (p0 p1 p2 : Point) (w0 w1 w2 : R) : Curve :=
  nurbs2_pt p0 p1 p2 w0 w1 w2.

(* CONSECUTIVE net edges only: the divided difference's (0,2) term regroups
   through P2 − P0 = (P1 − P0) + (P2 − P1), and c01 + 2·c02 + c12 = 2
   exactly, so the Lipschitz constant 2 needs no diagonal (review of #556:
   a free tightening — max(d01, d12) = 1 on the golden quarter circle,
   where the diagonal is √2). *)
Definition nurbs2_net_max (p0 p1 p2 : Point) : R :=
  Rmax (dist p0 p1) (dist p1 p2).

(* -------------------------------------------------------------------------- *)
(* Partition of unity and the denominator's weight floor.                     *)
(* -------------------------------------------------------------------------- *)

Lemma nurbs2_den_lb : forall w0 w1 w2 wmin t,
  0 <= t -> t <= 1 ->
  wmin <= w0 -> wmin <= w1 -> wmin <= w2 ->
  wmin <= nurbs2_den w0 w1 w2 t.
Proof.
  intros w0 w1 w2 wmin t Ht0 Ht1 Hw0 Hw1 Hw2.
  unfold nurbs2_den.
  apply bern2_weighted_den_lb; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Equal-weights degeneration: the rational quadratic IS the quadratic.       *)
(* -------------------------------------------------------------------------- *)

Lemma nurbs2_equal_weights_pt : forall p0 p1 p2 w t,
  w <> 0 ->
  nurbs2_pt p0 p1 p2 w w w t = bezier2_pt p0 p1 p2 t.
Proof.
  intros p0 p1 p2 w t Hw.
  assert (Hden : nurbs2_den w w w t = w)
    by (unfold nurbs2_den, bern2_0, bern2_1, bern2_2; ring).
  unfold nurbs2_pt, bezier2_pt. rewrite Hden.
  unfold bern2_0, bern2_1, bern2_2.
  f_equal; field; exact Hw.
Qed.

Theorem nurbs2_equal_weights_length : forall p0 p1 p2 w a b L,
  w <> 0 ->
  (is_curve_length (bezier2_param p0 p1 p2) a b L <->
   is_curve_length (nurbs2_param p0 p1 p2 w w w) a b L).
Proof.
  intros p0 p1 p2 w a b L Hw. split; intro H.
  - apply (is_curve_length_ext (bezier2_param p0 p1 p2)); [| exact H].
    intro t. symmetry. apply nurbs2_equal_weights_pt. exact Hw.
  - apply (is_curve_length_ext (nurbs2_param p0 p1 p2 w w w)); [| exact H].
    intro t. apply nurbs2_equal_weights_pt. exact Hw.
Qed.

(* WITNESS {"claimId":"nurbsquadraticlength-nurbs2-equal-weights-cubic","topic":"metric","lemma":"nurbs2_equal_weights_cubic","title":"Equal-weight rational quadratic carries the same is_curve_length values as the stored elevated cubic","file":"theories/NurbsQuadraticLength.v"} *)

Corollary nurbs2_equal_weights_cubic : forall p0 p1 p2 w a b L,
  w <> 0 ->
  (is_curve_length (nurbs2_param p0 p1 p2 w w w) a b L <->
   is_curve_length
     (bezier3_param p0 (elevate_mid1 p0 p1) (elevate_mid2 p1 p2) p2) a b L).
Proof.
  intros p0 p1 p2 w a b L Hw. split; intro H.
  - apply (proj1 (bezier3_elevation_length p0 p1 p2 a b L)).
    apply (proj2 (nurbs2_equal_weights_length p0 p1 p2 w a b L Hw)).
    exact H.
  - apply (proj1 (nurbs2_equal_weights_length p0 p1 p2 w a b L Hw)).
    apply (proj2 (bezier3_elevation_length p0 p1 p2 a b L)).
    exact H.
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
  intros p0 p1 p2 w0 w1 w2 wmin wmax s t
         Hw Hw0l Hw0u Hw1l Hw1u Hw2l Hw2u Hs Hst Ht1.
  assert (Hs1 : s <= 1) by lra.
  assert (Ht0 : 0 <= t) by lra.
  set (c01 := 2*((1-s)*(1-t))).
  set (c02 := s + t - 2*(s*t)).
  set (c12 := 2*(s*t)).
  set (x01 := px p1 - px p0). set (y01 := py p1 - py p0).
  set (x12 := px p2 - px p1). set (y12 := py p2 - py p1).
  set (M := nurbs2_net_max p0 p1 p2).
  set (Ds := nurbs2_den w0 w1 w2 s).
  set (Dt := nurbs2_den w0 w1 w2 t).
  (* cofactors: nonneg, and the REGROUPED mass c01 + 2·c02 + c12 is 2 exactly *)
  assert (Hc01 : 0 <= c01) by (unfold c01; nra).
  assert (Hc02 : 0 <= c02) by (unfold c02; nra).
  assert (Hc12 : 0 <= c12) by (unfold c12; nra).
  assert (Hcsum : c01 + 2*c02 + c12 = 2) by (unfold c01, c02, c12; ring).
  (* weight products *)
  assert (HW01 : 0 <= w0 * w1) by nra.
  assert (HW02 : 0 <= w0 * w2) by nra.
  assert (HW12 : 0 <= w1 * w2) by nra.
  assert (HWu01 : w0 * w1 <= wmax * wmax) by nra.
  assert (HWu02 : w0 * w2 <= wmax * wmax) by nra.
  assert (HWu12 : w1 * w2 <= wmax * wmax) by nra.
  (* denominator floors *)
  assert (HDs : wmin <= Ds)
    by (unfold Ds; apply nurbs2_den_lb; lra).
  assert (HDt : wmin <= Dt)
    by (unfold Dt; apply nurbs2_den_lb; lra).
  (* the divided-difference factorization, regrouped onto CONSECUTIVE edges:
     the (0,2) term splits through P2 − P0 = (P1 − P0) + (P2 − P1) *)
  set (C0 := c01*(w0*w1) + c02*(w0*w2)).
  set (C1 := c02*(w0*w2) + c12*(w1*w2)).
  set (qx := C0*x01 + C1*x12).
  set (qy := C0*y01 + C1*y12).
  assert (Hraw_s : 0 < (1-s)*(1-s)*w0 + 2*(s*(1-s))*w1 + s*s*w2).
  { pose proof (nurbs2_den_lb w0 w1 w2 wmin s Hs Hs1 Hw0l Hw1l Hw2l) as K.
    unfold nurbs2_den, bern2_0, bern2_1, bern2_2 in K. lra. }
  assert (Hraw_t : 0 < (1-t)*(1-t)*w0 + 2*(t*(1-t))*w1 + t*t*w2).
  { pose proof (nurbs2_den_lb w0 w1 w2 wmin t Ht0 Ht1 Hw0l Hw1l Hw2l) as K.
    unfold nurbs2_den, bern2_0, bern2_1, bern2_2 in K. lra. }
  assert (Hds : dist_sq (nurbs2_pt p0 p1 p2 w0 w1 w2 s)
                        (nurbs2_pt p0 p1 p2 w0 w1 w2 t)
                = Rsqr ((t - s) / (Ds * Dt)) * (qx*qx + qy*qy)).
  { unfold dist_sq, nurbs2_pt; cbn [px py].
    unfold Rsqr, qx, qy, C0, C1, c01, c02, c12, x01, y01, x12, y12.
    unfold Ds, Dt, nurbs2_den, bern2_0, bern2_1, bern2_2.
    field.
    repeat split; apply Rgt_not_eq; nra. }
  (* pass to dist *)
  assert (Hquot0 : 0 <= (t - s) / (Ds * Dt)).
  { unfold Rdiv. apply Rmult_le_pos; [lra |].
    left. apply Rinv_0_lt_compat. nra. }
  unfold nurbs2_param, dist. rewrite Hds.
  rewrite sqrt_mult;
    [| apply Rle_0_sqr
     | pose proof (sqr_nonneg qx); pose proof (sqr_nonneg qy); lra].
  rewrite sqrt_Rsqr by exact Hquot0.
  (* triangle inequality onto the consecutive net edges *)
  assert (HC0 : 0 <= C0) by (unfold C0; nra).
  assert (HC1 : 0 <= C1) by (unfold C1; nra).
  pose proof (norm_pair_le C0 C1 x01 y01 x12 y12 HC0 HC1) as Htri.
  assert (HD01 : sqrt (x01*x01 + y01*y01) = dist p0 p1).
  { unfold dist, dist_sq, x01, y01. f_equal. ring. }
  assert (HD12 : sqrt (x12*x12 + y12*y12) = dist p1 p2).
  { unfold dist, dist_sq, x12, y12. f_equal. ring. }
  rewrite HD01, HD12 in Htri.
  assert (HM01 : dist p0 p1 <= M).
  { unfold M, nurbs2_net_max. apply Rmax_l. }
  assert (HM12 : dist p1 p2 <= M).
  { unfold M, nurbs2_net_max. apply Rmax_r. }
  assert (HM0 : 0 <= M)
    by (pose proof (dist_nonneg p0 p1); lra).
  assert (HwM0 : 0 <= (wmax * wmax) * M) by nra.
  assert (Hd01n : 0 <= dist p0 p1) by apply dist_nonneg.
  assert (Hd12n : 0 <= dist p1 p2) by apply dist_nonneg.
  assert (Hq : sqrt (qx*qx + qy*qy) <= 2 * (wmax*wmax) * M).
  { unfold qx, qy. eapply Rle_trans; [exact Htri |].
    assert (HCsum : C0 + C1 <= 2 * (wmax * wmax)).
    { unfold C0, C1.
      replace (2 * (wmax * wmax)) with ((c01 + 2*c02 + c12) * (wmax * wmax))
        by (rewrite Hcsum; ring).
      nra. }
    assert (T0 : C0 * dist p0 p1 <= C0 * M)
      by (apply Rmult_le_compat_l; assumption).
    assert (T1 : C1 * dist p1 p2 <= C1 * M)
      by (apply Rmult_le_compat_l; assumption).
    nra. }
  (* assemble through the denominator floor *)
  eapply Rle_trans.
  { apply Rmult_le_compat_l; [exact Hquot0 | exact Hq]. }
  assert (Hinv : / (Ds * Dt) <= / (wmin * wmin)).
  { apply Rinv_le_contravar; nra. }
  assert (Hinv0 : 0 < / (wmin * wmin)).
  { apply Rinv_0_lt_compat. nra. }
  assert (HA : 0 <= 2 * (wmax*wmax) * M * (t - s)) by nra.
  unfold Rdiv. unfold Rdiv in Hinv.
  nra.
Qed.

(* WITNESS {"claimId":"nurbsquadraticlength-nurbs2-length-upper","topic":"metric","lemma":"nurbs2_length_upper","title":"Rational quadratic metric length <= 2*(wmax/wmin)^2 * max net edge * (b-a) on [0,1]","file":"theories/NurbsQuadraticLength.v"} *)

Theorem nurbs2_length_upper : forall p0 p1 p2 w0 w1 w2 wmin wmax a b L,
  0 < wmin ->
  wmin <= w0 -> w0 <= wmax ->
  wmin <= w1 -> w1 <= wmax ->
  wmin <= w2 -> w2 <= wmax ->
  0 <= a -> a <= b -> b <= 1 ->
  is_curve_length (nurbs2_param p0 p1 p2 w0 w1 w2) a b L ->
  L <= 2 * ((wmax * wmax) / (wmin * wmin)) * nurbs2_net_max p0 p1 p2 * (b - a).
Proof.
  intros p0 p1 p2 w0 w1 w2 wmin wmax a b L
         Hw Hw0l Hw0u Hw1l Hw1u Hw2l Hw2u Ha Hab Hb1 HL.
  set (K := 2 * ((wmax * wmax) / (wmin * wmin)) * nurbs2_net_max p0 p1 p2).
  replace (K * (b - a)) with (K * b - K * a) by ring.
  apply (curve_length_upper_of_chord_modulus (nurbs2_param p0 p1 p2 w0 w1 w2)
           (fun x => K * x) a b L); [| exact HL].
  intros s t Has Hst Htb. cbv beta.
  assert (Hs0 : 0 <= s) by lra.
  assert (Ht1 : t <= 1) by lra.
  pose proof (nurbs2_chord_le p0 p1 p2 w0 w1 w2 wmin wmax s t
                Hw Hw0l Hw0u Hw1l Hw1u Hw2l Hw2u Hs0 Hst Ht1) as Hc.
  fold K in Hc. lra.
Qed.

Corollary nurbs2_length_upper_unit : forall p0 p1 p2 w0 w1 w2 wmin wmax L,
  0 < wmin ->
  wmin <= w0 -> w0 <= wmax ->
  wmin <= w1 -> w1 <= wmax ->
  wmin <= w2 -> w2 <= wmax ->
  is_curve_length (nurbs2_param p0 p1 p2 w0 w1 w2) 0 1 L ->
  L <= 2 * ((wmax * wmax) / (wmin * wmin)) * nurbs2_net_max p0 p1 p2.
Proof.
  intros p0 p1 p2 w0 w1 w2 wmin wmax L
         Hw Hw0l Hw0u Hw1l Hw1u Hw2l Hw2u HL.
  assert (H : L <= 2 * ((wmax * wmax) / (wmin * wmin))
                   * nurbs2_net_max p0 p1 p2 * (1 - 0)).
  { apply (nurbs2_length_upper p0 p1 p2 w0 w1 w2 wmin wmax 0 1 L);
      try assumption; lra. }
  lra.
Qed.

(* Equal weights at w = 1 close the quadratic Lipschitz bound that the
   elevation iff left on the table (Bezier3Length only bound the cubic). *)
Corollary bezier2_length_upper : forall p0 p1 p2 a b L,
  0 <= a -> a <= b -> b <= 1 ->
  is_curve_length (bezier2_param p0 p1 p2) a b L ->
  L <= 2 * nurbs2_net_max p0 p1 p2 * (b - a).
Proof.
  intros p0 p1 p2 a b L Ha Hab Hb1 HL.
  assert (H1 : is_curve_length (nurbs2_param p0 p1 p2 1 1 1) a b L).
  { apply (proj1 (nurbs2_equal_weights_length p0 p1 p2 1 a b L R1_neq_R0)).
    exact HL. }
  pose proof (nurbs2_length_upper p0 p1 p2 1 1 1 1 1 a b L
                Rlt_0_1 (Rle_refl 1) (Rle_refl 1) (Rle_refl 1) (Rle_refl 1)
                (Rle_refl 1) (Rle_refl 1) Ha Hab Hb1 H1) as H.
  replace (1 * 1) with 1 in H by ring.
  unfold Rdiv in H. rewrite Rinv_1 in H.
  lra.
Qed.

Print Assumptions nurbs2_equal_weights_cubic.
Print Assumptions nurbs2_length_upper.
