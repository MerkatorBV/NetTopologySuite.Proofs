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
     CurveLength.curve_length_ge_chord, free.  The shared factorization
     (`bezier3_chord_le_combo`, over the named weights bezier3_c0/c1/c2
     in BernsteinBasis.v) also feeds Bezier3Polygon.v's TIGHT
     control-polygon bound.  `bezier3_elevation_pointwise` is the n=2
     instance of `bern_elevate_2` (#562 / 508-f).  The conditional
     exact tier is a future rung.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Export BernsteinBasis.
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

Lemma bezier2_px_bern : forall p0 p1 p2 t,
  px (bezier2_pt p0 p1 p2 t)
  = bern2_0 t * px p0 + bern2_1 t * px p1 + bern2_2 t * px p2.
Proof.
  intros p0 p1 p2 t.
  unfold bezier2_pt, bern2_0, bern2_1, bern2_2; cbn [px py]. ring.
Qed.

Lemma bezier2_py_bern : forall p0 p1 p2 t,
  py (bezier2_pt p0 p1 p2 t)
  = bern2_0 t * py p0 + bern2_1 t * py p1 + bern2_2 t * py p2.
Proof.
  intros p0 p1 p2 t.
  unfold bezier2_pt, bern2_0, bern2_1, bern2_2; cbn [px py]. ring.
Qed.

Lemma bezier3_px_bern : forall p0 p1 p2 p3 t,
  px (bezier3_pt p0 p1 p2 p3 t)
  = bern3_0 t * px p0 + bern3_1 t * px p1
    + bern3_2 t * px p2 + bern3_3 t * px p3.
Proof.
  intros p0 p1 p2 p3 t.
  unfold bezier3_pt, bern3_0, bern3_1, bern3_2, bern3_3; cbn [px py]. ring.
Qed.

Lemma bezier3_py_bern : forall p0 p1 p2 p3 t,
  py (bezier3_pt p0 p1 p2 p3 t)
  = bern3_0 t * py p0 + bern3_1 t * py p1
    + bern3_2 t * py p2 + bern3_3 t * py p3.
Proof.
  intros p0 p1 p2 p3 t.
  unfold bezier3_pt, bern3_0, bern3_1, bern3_2, bern3_3; cbn [px py]. ring.
Qed.

Definition ctrl_x (p0 p1 p2 : Point) (i : nat) : R :=
  match i with O => px p0 | 1%nat => px p1 | _ => px p2 end.

Definition ctrl_y (p0 p1 p2 : Point) (i : nat) : R :=
  match i with O => py p0 | 1%nat => py p1 | _ => py p2 end.

Lemma elevate_mid1_px_ctrl : forall p0 p1 p2,
  px (elevate_mid1 p0 p1) = elevate_ctrl 2 (ctrl_x p0 p1 p2) 1%nat.
Proof.
  intros p0 p1 p2.
  rewrite elevate_ctrl_2_1. rewrite inr_1, inr_2, inr_3.
  unfold elevate_mid1, ctrl_x, Rdiv; cbn [px]. ring.
Qed.

Lemma elevate_mid1_py_ctrl : forall p0 p1 p2,
  py (elevate_mid1 p0 p1) = elevate_ctrl 2 (ctrl_y p0 p1 p2) 1%nat.
Proof.
  intros p0 p1 p2.
  rewrite elevate_ctrl_2_1. rewrite inr_1, inr_2, inr_3.
  unfold elevate_mid1, ctrl_y, Rdiv; cbn [py]. ring.
Qed.

Lemma elevate_mid2_px_ctrl : forall p0 p1 p2,
  px (elevate_mid2 p1 p2) = elevate_ctrl 2 (ctrl_x p0 p1 p2) 2%nat.
Proof.
  intros p0 p1 p2.
  rewrite elevate_ctrl_2_2. rewrite inr_1, inr_2, inr_3.
  unfold elevate_mid2, ctrl_x, Rdiv; cbn [px]. ring.
Qed.

Lemma elevate_mid2_py_ctrl : forall p0 p1 p2,
  py (elevate_mid2 p1 p2) = elevate_ctrl 2 (ctrl_y p0 p1 p2) 2%nat.
Proof.
  intros p0 p1 p2.
  rewrite elevate_ctrl_2_2. rewrite inr_1, inr_2, inr_3.
  unfold elevate_mid2, ctrl_y, Rdiv; cbn [py]. ring.
Qed.

Lemma elevate_end_px_ctrl : forall p0 p1 p2,
  px p2 = elevate_ctrl 2 (ctrl_x p0 p1 p2) 3%nat.
Proof.
  intros p0 p1 p2. unfold elevate_ctrl, ctrl_x. simpl. reflexivity.
Qed.

Lemma elevate_end_py_ctrl : forall p0 p1 p2,
  py p2 = elevate_ctrl 2 (ctrl_y p0 p1 p2) 3%nat.
Proof.
  intros p0 p1 p2. unfold elevate_ctrl, ctrl_y. simpl. reflexivity.
Qed.

Lemma elevate_start_px_ctrl : forall p0 p1 p2,
  px p0 = elevate_ctrl 2 (ctrl_x p0 p1 p2) 0%nat.
Proof.
  intros p0 p1 p2. unfold elevate_ctrl, ctrl_x. reflexivity.
Qed.

Lemma elevate_start_py_ctrl : forall p0 p1 p2,
  py p0 = elevate_ctrl 2 (ctrl_y p0 p1 p2) 0%nat.
Proof.
  intros p0 p1 p2. unfold elevate_ctrl, ctrl_y. reflexivity.
Qed.

(* Framework proof: the pointwise identity is bern_elevate_2 on each
   coordinate, with elevate_mid1/mid2 the n=2 instance of elevate_ctrl. *)
Lemma bezier3_elevation_pointwise : forall p0 p1 p2 t,
  bezier3_pt p0 (elevate_mid1 p0 p1) (elevate_mid2 p1 p2) p2 t
  = bezier2_pt p0 p1 p2 t.
Proof.
  intros p0 p1 p2 t.
  assert (Hx :
    px (bezier3_pt p0 (elevate_mid1 p0 p1) (elevate_mid2 p1 p2) p2 t)
    = px (bezier2_pt p0 p1 p2 t)).
  { rewrite bezier3_px_bern, bezier2_px_bern.
    rewrite (elevate_start_px_ctrl p0 p1 p2).
    rewrite (elevate_mid1_px_ctrl p0 p1 p2).
    rewrite (elevate_mid2_px_ctrl p0 p1 p2).
    rewrite (elevate_end_px_ctrl p0 p1 p2).
    symmetry. apply bern_elevate_2. }
  assert (Hy :
    py (bezier3_pt p0 (elevate_mid1 p0 p1) (elevate_mid2 p1 p2) p2 t)
    = py (bezier2_pt p0 p1 p2 t)).
  { rewrite bezier3_py_bern, bezier2_py_bern.
    rewrite (elevate_start_py_ctrl p0 p1 p2).
    rewrite (elevate_mid1_py_ctrl p0 p1 p2).
    rewrite (elevate_mid2_py_ctrl p0 p1 p2).
    rewrite (elevate_end_py_ctrl p0 p1 p2).
    symmetry. apply bern_elevate_2. }
  destruct (bezier3_pt p0 (elevate_mid1 p0 p1) (elevate_mid2 p1 p2) p2 t)
    as [x3 y3] eqn:E3.
  destruct (bezier2_pt p0 p1 p2 t) as [x2 y2] eqn:E2.
  cbn [px py] in Hx, Hy.
  rewrite Hx, Hy. reflexivity.
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

(* The SHARED chord bound both Bezier tiers consume: the divided-difference
   factorization + the framework vector triangle inequality
   (`chord_le_of_combo3`).  Cofactors bezier3_c0/c1/c2 live in
   BernsteinBasis.v.  The crude 3*max bound (below) and the tight
   control-polygon modulus (Bezier3Polygon.v) are one bounding step away. *)
Lemma bezier3_chord_le_combo : forall p0 p1 p2 p3 s t,
  0 <= s -> s <= t -> t <= 1 ->
  dist (bezier3_param p0 p1 p2 p3 s) (bezier3_param p0 p1 p2 p3 t)
  <= (t - s) * (bezier3_c0 s t * dist p0 p1
                + bezier3_c1 s t * dist p1 p2
                + bezier3_c2 s t * dist p2 p3).
Proof.
  intros p0 p1 p2 p3 s t Hs Hst Ht1.
  set (c0 := bezier3_c0 s t).
  set (c1 := bezier3_c1 s t).
  set (c2 := bezier3_c2 s t).
  set (x0 := px p1 - px p0). set (y0 := py p1 - py p0).
  set (x1 := px p2 - px p1). set (y1 := py p2 - py p1).
  set (x2 := px p3 - px p2). set (y2 := py p3 - py p2).
  destruct (bezier3_c_nonneg s t Hs Hst Ht1) as (Hc0 & Hc1 & Hc2).
  assert (Hfact :
    dist (bezier3_pt p0 p1 p2 p3 s) (bezier3_pt p0 p1 p2 p3 t)
    = sqrt (((t-s) * (c0*x0 + c1*x1 + c2*x2))
              * ((t-s) * (c0*x0 + c1*x1 + c2*x2))
            + ((t-s) * (c0*y0 + c1*y1 + c2*y2))
              * ((t-s) * (c0*y0 + c1*y1 + c2*y2)))).
  { unfold dist, dist_sq, bezier3_pt, c0, c1, c2,
           bezier3_c0, bezier3_c1, bezier3_c2; cbn [px py].
    f_equal. unfold x0, y0, x1, y1, x2, y2. ring. }
  unfold bezier3_param. rewrite Hfact.
  rewrite scaled_diff_norm by lra.
  pose proof (norm_triple_le c0 c1 c2 x0 y0 x1 y1 x2 y2 Hc0 Hc1 Hc2) as Htri.
  assert (HD0 : sqrt (x0*x0 + y0*y0) = dist p0 p1).
  { unfold dist, dist_sq, x0, y0. f_equal. ring. }
  assert (HD1 : sqrt (x1*x1 + y1*y1) = dist p1 p2).
  { unfold dist, dist_sq, x1, y1. f_equal. ring. }
  assert (HD2 : sqrt (x2*x2 + y2*y2) = dist p2 p3).
  { unfold dist, dist_sq, x2, y2. f_equal. ring. }
  rewrite HD0, HD1, HD2 in Htri.
  eapply Rle_trans.
  { apply Rmult_le_compat_l; [lra | exact Htri]. }
  apply Req_le. ring.
Qed.

Lemma bezier3_chord_le : forall p0 p1 p2 p3 s t,
  0 <= s -> s <= t -> t <= 1 ->
  dist (bezier3_param p0 p1 p2 p3 s) (bezier3_param p0 p1 p2 p3 t)
  <= 3 * bezier3_net_max p0 p1 p2 p3 * (t - s).
Proof.
  intros p0 p1 p2 p3 s t Hs Hst Ht1.
  eapply Rle_trans; [apply bezier3_chord_le_combo; assumption |].
  destruct (bezier3_c_nonneg s t Hs Hst Ht1) as (Hc0 & Hc1 & Hc2).
  pose proof (bezier3_c_sum s t) as Hsum.
  set (M := bezier3_net_max p0 p1 p2 p3).
  assert (HM0 : dist p0 p1 <= M).
  { unfold M, bezier3_net_max. apply Rmax_l. }
  assert (HM1 : dist p1 p2 <= M).
  { unfold M, bezier3_net_max.
    eapply Rle_trans; [apply Rmax_l | apply Rmax_r]. }
  assert (HM2 : dist p2 p3 <= M).
  { unfold M, bezier3_net_max.
    eapply Rle_trans; [apply Rmax_r | apply Rmax_r]. }
  assert (Hcomb : bezier3_c0 s t * dist p0 p1 + bezier3_c1 s t * dist p1 p2
                  + bezier3_c2 s t * dist p2 p3 <= 3 * M).
  { replace (3 * M)
      with ((bezier3_c0 s t + bezier3_c1 s t + bezier3_c2 s t) * M)
      by (rewrite Hsum; ring).
    nra. }
  assert (Hts : 0 <= t - s) by lra.
  nra.
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
