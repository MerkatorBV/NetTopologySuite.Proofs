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
  intros p0 p1 p2 t.
  unfold bezier3_pt, bezier2_pt, elevate_mid1, elevate_mid2; cbn [px py].
  f_equal; field.
Qed.

(* WITNESS {"claimId":"bezier3length-bezier3-elevation-length","topic":"metric","lemma":"bezier3_elevation_length","title":"Degree elevation is exact: the elevated cubic carries the same is_curve_length values as the quadratic","file":"theories/Bezier3Length.v"} *)

Theorem bezier3_elevation_length : forall p0 p1 p2 a b L,
  is_curve_length (bezier2_param p0 p1 p2) a b L <->
  is_curve_length
    (bezier3_param p0 (elevate_mid1 p0 p1) (elevate_mid2 p1 p2) p2) a b L.
Proof.
  intros p0 p1 p2 a b L. split; intro H.
  - apply (is_curve_length_ext (bezier2_param p0 p1 p2)); [| exact H].
    intro t. symmetry. apply bezier3_elevation_pointwise.
  - apply (is_curve_length_ext
             (bezier3_param p0 (elevate_mid1 p0 p1) (elevate_mid2 p1 p2) p2));
      [| exact H].
    intro t. apply bezier3_elevation_pointwise.
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
  intros c x y Hc.
  replace ((c*x) * (c*x) + (c*y) * (c*y))
    with ((c*c) * (x*x + y*y)) by ring.
  rewrite sqrt_mult;
    [| pose proof (sqr_nonneg c); lra
     | pose proof (sqr_nonneg x); pose proof (sqr_nonneg y); lra].
  replace (c * c) with (Rsqr c) by (unfold Rsqr; ring).
  rewrite sqrt_Rsqr by exact Hc.
  reflexivity.
Qed.

(* Triangle inequality for a three-term nonnegative combination of vectors:
   two dist_triangle hops through the partial sums. *)
Lemma norm_triple_le : forall c0 c1 c2 x0 y0 x1 y1 x2 y2,
  0 <= c0 -> 0 <= c1 -> 0 <= c2 ->
  sqrt ((c0*x0 + c1*x1 + c2*x2) * (c0*x0 + c1*x1 + c2*x2)
        + (c0*y0 + c1*y1 + c2*y2) * (c0*y0 + c1*y1 + c2*y2))
  <= c0 * sqrt (x0*x0 + y0*y0) + c1 * sqrt (x1*x1 + y1*y1)
     + c2 * sqrt (x2*x2 + y2*y2).
Proof.
  intros c0 c1 c2 x0 y0 x1 y1 x2 y2 Hc0 Hc1 Hc2.
  set (A0 := mkPoint 0 0).
  set (A1 := mkPoint (c0*x0) (c0*y0)).
  set (A2 := mkPoint (c0*x0 + c1*x1) (c0*y0 + c1*y1)).
  set (A3 := mkPoint (c0*x0 + c1*x1 + c2*x2) (c0*y0 + c1*y1 + c2*y2)).
  assert (Hgoal : sqrt ((c0*x0 + c1*x1 + c2*x2) * (c0*x0 + c1*x1 + c2*x2)
                        + (c0*y0 + c1*y1 + c2*y2) * (c0*y0 + c1*y1 + c2*y2))
                  = dist A0 A3).
  { unfold dist, dist_sq, A0, A3; cbn [px py]. f_equal. ring. }
  assert (H01 : dist A0 A1 = c0 * sqrt (x0*x0 + y0*y0)).
  { rewrite <- (scaled_diff_norm c0 x0 y0 Hc0).
    unfold dist, dist_sq, A0, A1; cbn [px py]. f_equal. ring. }
  assert (H12 : dist A1 A2 = c1 * sqrt (x1*x1 + y1*y1)).
  { rewrite <- (scaled_diff_norm c1 x1 y1 Hc1).
    unfold dist, dist_sq, A1, A2; cbn [px py]. f_equal. ring. }
  assert (H23 : dist A2 A3 = c2 * sqrt (x2*x2 + y2*y2)).
  { rewrite <- (scaled_diff_norm c2 x2 y2 Hc2).
    unfold dist, dist_sq, A2, A3; cbn [px py]. f_equal. ring. }
  rewrite Hgoal, <- H01, <- H12, <- H23.
  pose proof (dist_triangle A0 A2 A3) as Ha.
  pose proof (dist_triangle A0 A1 A2) as Hb.
  lra.
Qed.

Lemma bezier3_chord_le : forall p0 p1 p2 p3 s t,
  0 <= s -> s <= t -> t <= 1 ->
  dist (bezier3_param p0 p1 p2 p3 s) (bezier3_param p0 p1 p2 p3 t)
  <= 3 * bezier3_net_max p0 p1 p2 p3 * (t - s).
Proof.
  intros p0 p1 p2 p3 s t Hs Hst Ht1.
  set (c0 := 3 - 3*(s+t) + (s*s + s*t + t*t)).
  set (c1 := 3*(s+t) - 2*(s*s + s*t + t*t)).
  set (c2 := s*s + s*t + t*t).
  set (x0 := px p1 - px p0). set (y0 := py p1 - py p0).
  set (x1 := px p2 - px p1). set (y1 := py p2 - py p1).
  set (x2 := px p3 - px p2). set (y2 := py p3 - py p2).
  set (M := bezier3_net_max p0 p1 p2 p3).
  (* the symmetrized Bernstein-2 weights are nonneg and sum to 3 on [0,1]² *)
  assert (Hc0 : 0 <= c0).
  { unfold c0.
    replace (3 - 3*(s+t) + (s*s + s*t + t*t))
      with ((1-s)*(1-s) + (1-s)*(1-t) + (1-t)*(1-t)) by ring.
    nra. }
  assert (Hc2 : 0 <= c2) by (unfold c2; nra).
  assert (Hc1 : 0 <= c1).
  { unfold c1. pose proof (sqr_nonneg (s - t)) as Hsq. nra. }
  assert (Hsum : c0 + c1 + c2 = 3) by (unfold c0, c1, c2; ring).
  (* the chord factors through the divided difference *)
  assert (Hfact :
    dist (bezier3_pt p0 p1 p2 p3 s) (bezier3_pt p0 p1 p2 p3 t)
    = sqrt (((t-s) * (c0*x0 + c1*x1 + c2*x2))
              * ((t-s) * (c0*x0 + c1*x1 + c2*x2))
            + ((t-s) * (c0*y0 + c1*y1 + c2*y2))
              * ((t-s) * (c0*y0 + c1*y1 + c2*y2)))).
  { unfold dist, dist_sq, bezier3_pt; cbn [px py].
    f_equal. unfold c0, c1, c2, x0, y0, x1, y1, x2, y2. ring. }
  unfold bezier3_param. rewrite Hfact.
  rewrite scaled_diff_norm by lra.
  (* the divided difference is a nonneg combination of net edges *)
  pose proof (norm_triple_le c0 c1 c2 x0 y0 x1 y1 x2 y2 Hc0 Hc1 Hc2) as Htri.
  assert (HD0 : sqrt (x0*x0 + y0*y0) = dist p0 p1).
  { unfold dist, dist_sq, x0, y0. f_equal. ring. }
  assert (HD1 : sqrt (x1*x1 + y1*y1) = dist p1 p2).
  { unfold dist, dist_sq, x1, y1. f_equal. ring. }
  assert (HD2 : sqrt (x2*x2 + y2*y2) = dist p2 p3).
  { unfold dist, dist_sq, x2, y2. f_equal. ring. }
  rewrite HD0, HD1, HD2 in Htri.
  (* every net edge is below the max *)
  assert (HM0 : dist p0 p1 <= M).
  { unfold M, bezier3_net_max. apply Rmax_l. }
  assert (HM1 : dist p1 p2 <= M).
  { unfold M, bezier3_net_max.
    eapply Rle_trans; [apply Rmax_l | apply Rmax_r]. }
  assert (HM2 : dist p2 p3 <= M).
  { unfold M, bezier3_net_max.
    eapply Rle_trans; [apply Rmax_r | apply Rmax_r]. }
  assert (Hq : sqrt ((c0*x0 + c1*x1 + c2*x2) * (c0*x0 + c1*x1 + c2*x2)
                     + (c0*y0 + c1*y1 + c2*y2) * (c0*y0 + c1*y1 + c2*y2))
               <= 3 * M).
  { eapply Rle_trans; [exact Htri |].
    assert (T0 : c0 * dist p0 p1 <= c0 * M)
      by (apply Rmult_le_compat_l; assumption).
    assert (T1 : c1 * dist p1 p2 <= c1 * M)
      by (apply Rmult_le_compat_l; assumption).
    assert (T2 : c2 * dist p2 p3 <= c2 * M)
      by (apply Rmult_le_compat_l; assumption).
    replace (3 * M) with (c0 * M + c1 * M + c2 * M)
      by (rewrite <- Hsum; ring).
    lra. }
  eapply Rle_trans.
  { apply Rmult_le_compat_l; [lra | exact Hq]. }
  apply Req_le. ring.
Qed.

Lemma bezier3_polyline_le : forall p0 p1 p2 p3 ts t b,
  0 <= t -> b <= 1 -> chain t ts b ->
  polyline_len (bezier3_param p0 p1 p2 p3) t (ts ++ [b])
  <= 3 * bezier3_net_max p0 p1 p2 p3 * (b - t).
Proof.
  intros p0 p1 p2 p3 ts t b Ht Hb1 Hch.
  set (M := bezier3_net_max p0 p1 p2 p3).
  replace (3 * M * (b - t)) with (3 * M * b - 3 * M * t) by ring.
  apply (polyline_le_of_chord_modulus (bezier3_param p0 p1 p2 p3)
           (fun x => 3 * M * x) t b ts t).
  - intros s u Hts Hsu Hub. cbv beta.
    assert (Hs0 : 0 <= s) by lra.
    assert (Hu1 : u <= 1) by lra.
    pose proof (bezier3_chord_le p0 p1 p2 p3 s u Hs0 Hsu Hu1) as Hc.
    fold M in Hc. lra.
  - lra.
  - exact Hch.
Qed.

(* WITNESS {"claimId":"bezier3length-bezier3-length-upper","topic":"metric","lemma":"bezier3_length_upper","title":"Cubic Bezier metric length <= 3 * max control-net edge * (b-a) on [0,1]","file":"theories/Bezier3Length.v"} *)

Theorem bezier3_length_upper : forall p0 p1 p2 p3 a b L,
  0 <= a -> a <= b -> b <= 1 ->
  is_curve_length (bezier3_param p0 p1 p2 p3) a b L ->
  L <= 3 * bezier3_net_max p0 p1 p2 p3 * (b - a).
Proof.
  intros p0 p1 p2 p3 a b L Ha Hab Hb1 HL.
  set (M := bezier3_net_max p0 p1 p2 p3).
  replace (3 * M * (b - a)) with (3 * M * b - 3 * M * a) by ring.
  apply (curve_length_upper_of_chord_modulus (bezier3_param p0 p1 p2 p3)
           (fun x => 3 * M * x) a b L);
    [| exact HL].
  intros s t Has Hst Htb. cbv beta.
  assert (Hs0 : 0 <= s) by lra.
  assert (Ht1 : t <= 1) by lra.
  pose proof (bezier3_chord_le p0 p1 p2 p3 s t Hs0 Hst Ht1) as Hc.
  fold M in Hc. lra.
Qed.

Corollary bezier3_length_upper_unit : forall p0 p1 p2 p3 L,
  is_curve_length (bezier3_param p0 p1 p2 p3) 0 1 L ->
  L <= 3 * bezier3_net_max p0 p1 p2 p3.
Proof.
  intros p0 p1 p2 p3 L HL.
  assert (H : L <= 3 * bezier3_net_max p0 p1 p2 p3 * (1 - 0)).
  { apply (bezier3_length_upper p0 p1 p2 p3 0 1 L);
      [lra | lra | lra | exact HL]. }
  lra.
Qed.

Print Assumptions bezier3_elevation_length.
Print Assumptions bezier3_length_upper.
