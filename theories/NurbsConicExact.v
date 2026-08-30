(* ============================================================================
   NetTopologySuite.Proofs.NurbsConicExact
   ----------------------------------------------------------------------------
   Issue #559 / claimId 508-a: the oracle's golden rational-quadratic N
   vector — P0=(1,0) w=1, P1=(1,1) w=√2/2, P2=(0,1) w=1 on [0,1] — traces
   the unit quarter circle, so its metric length is exactly π/2.

   NurbsQuadraticLength.v left this as motivation.  The map is the
   Weierstrass substitution with the closed form (not 2·atan(t)):

     u(t) = t / (√2 + (1-√2)·t)
     φ(t) = 2 · atan(u(t))

   so φ : [0,1] → [0, π/2], with explicit preimages
     t = tan(θ/2)·√2 / (1 + tan(θ/2)·(√2-1)).
   Pointwise `circle_pt origin 1 (φ t) = nurbs2_pt golden t` on [0,1]
   is a field identity plus cos/sin of 2·atan.  Then:

     arc_r_theta_is_curve_length  →  length of the unit circle on [0, π/2]
     is_curve_length_reparam      →  transport along φ
     is_curve_length_ext_on       →  land on the golden nurbs2_param

   Stdlib `atan` is unavoidable for the explicit preimage (the reparam
   contract forbids IVT).  That pulls Classical_Prop.classic; this file
   is Category C in docs/audit-exceptions.txt, same atan lineage as
   ArcParamBridge.v.  The CurveLength / ArcRectifiable engines stay
   3-axiom in their own files.  No CurveSegment growth, no ADR-0004
   remint, no new 64-a r·θ.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Ratan List.
From NTS.Proofs Require Import
  Distance CurveLength ArcRectifiable NurbsQuadraticLength.
Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Oracle golden vector (red_length_unified_zoo_tests.py nurbs_arc).          *)
(* -------------------------------------------------------------------------- *)

Definition golden_p0 : Point := mkPoint 1 0.
Definition golden_p1 : Point := mkPoint 1 1.
Definition golden_p2 : Point := mkPoint 0 1.
Definition golden_w0 : R := 1.
Definition golden_w1 : R := sqrt 2 / 2.
Definition golden_w2 : R := 1.
Definition golden_origin : Point := mkPoint 0 0.

Definition golden_param : Curve :=
  nurbs2_param golden_p0 golden_p1 golden_p2 golden_w0 golden_w1 golden_w2.

(* Weierstrass half-angle coordinate and the angular reparameterization. *)
Definition golden_uden (t : R) : R := sqrt 2 + (1 - sqrt 2) * t.
Definition golden_u (t : R) : R := t / golden_uden t.
Definition golden_phi (t : R) : R := 2 * atan (golden_u t).

(* Inverse of golden_u, used as the explicit preimage of φ. *)
Definition golden_pre_u (w : R) : R :=
  w * sqrt 2 / (1 + w * (sqrt 2 - 1)).

Lemma point_ext : forall p q : Point, px p = px q -> py p = py q -> p = q.
Proof.
  intros [xp yp] [xq yq]; simpl; intros; subst; reflexivity.
Qed.

Lemma sqrt2_sqr : sqrt 2 * sqrt 2 = 2.
Proof. apply sqrt_sqrt. lra. Qed.

Lemma sqrt2_pos : 0 < sqrt 2.
Proof. apply sqrt_lt_R0. lra. Qed.

Lemma sqrt2_gt_1 : 1 < sqrt 2.
Proof. rewrite <- sqrt_1. apply sqrt_lt_1; lra. Qed.

Lemma sqrt2_lt_2 : sqrt 2 < 2.
Proof.
  rewrite <- (sqrt_square 2) at 2 by lra.
  apply sqrt_lt_1; lra.
Qed.

Lemma sqrt2_neq_0 : sqrt 2 <> 0.
Proof. apply Rgt_not_eq, sqrt2_pos. Qed.

Lemma atan_le : forall x y, x <= y -> atan x <= atan y.
Proof.
  intros x y [Hlt | Heq].
  - apply Rlt_le, atan_increasing. exact Hlt.
  - subst. apply Rle_refl.
Qed.

Lemma tan_PI4 : tan (PI / 4) = 1.
Proof. rewrite <- atan_1. apply tan_atan. Qed.

Lemma cos_atan_pos : forall x, 0 < cos (atan x).
Proof.
  intro x. rewrite cos_atan.
  apply Rdiv_lt_0_compat; [lra |].
  apply sqrt_lt_R0.
  apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr].
Qed.

(* -------------------------------------------------------------------------- *)
(* Windowed extensionality: the spec only samples [a,b].                      *)
(* -------------------------------------------------------------------------- *)

Lemma polyline_len_ext_on :
  forall (g1 g2 : Curve) a b ts t,
    (forall u, a <= u -> u <= b -> g1 u = g2 u) ->
    a <= t -> chain t ts b ->
    polyline_len g1 t (ts ++ [b]) = polyline_len g2 t (ts ++ [b]).
Proof.
  intros g1 g2 a b ts; induction ts as [|u tl IH];
    intros t Hg Hat Hch; simpl.
  - assert (Htb : t <= b) by exact Hch.
    assert (Hab : a <= b) by lra.
    rewrite (Hg t Hat Htb), (Hg b Hab (Rle_refl b)).
    reflexivity.
  - destruct Hch as [Htu Hch].
    pose proof (chain_le tl u b Hch) as Hub.
    assert (Hau : a <= u) by lra.
    rewrite (Hg t Hat ltac:(lra)), (Hg u Hau Hub).
    rewrite (IH u Hg Hau Hch).
    reflexivity.
Qed.

Lemma is_curve_length_ext_on : forall (g1 g2 : Curve) a b L,
  (forall t, a <= t -> t <= b -> g1 t = g2 t) ->
  is_curve_length g1 a b L -> is_curve_length g2 a b L.
Proof.
  intros g1 g2 a b L Hg [Hub Hlst].
  split.
  - intros l (ts & Hch & Hl). subst l.
    apply Hub. exists ts. split; [exact Hch |].
    rewrite <- (polyline_len_ext_on g1 g2 a b ts a Hg (Rle_refl a) Hch).
    reflexivity.
  - intros M HM. apply Hlst. intros l (ts & Hch & Hl). subst l.
    apply HM. exists ts. split; [exact Hch |].
    rewrite (polyline_len_ext_on g1 g2 a b ts a Hg (Rle_refl a) Hch).
    reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Denominator floors on [0,1].                                               *)
(* -------------------------------------------------------------------------- *)

Lemma golden_w1_pos : 0 < golden_w1.
Proof.
  unfold golden_w1.
  apply Rdiv_lt_0_compat; [exact sqrt2_pos | lra].
Qed.

Lemma golden_w1_le_1 : golden_w1 <= 1.
Proof.
  unfold golden_w1.
  apply (Rmult_le_reg_r 2); [lra |].
  unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
  rewrite Rmult_1_l.
  apply Rlt_le, sqrt2_lt_2.
Qed.

Lemma golden_den_pos : forall t,
  0 <= t -> t <= 1 ->
  0 < nurbs2_den golden_w0 golden_w1 golden_w2 t.
Proof.
  intros t Ht0 Ht1.
  apply Rlt_le_trans with (r2 := golden_w1).
  - exact golden_w1_pos.
  - apply (nurbs2_den_lb golden_w0 golden_w1 golden_w2 golden_w1 t
            Ht0 Ht1).
    + unfold golden_w0. exact golden_w1_le_1.
    + apply Rle_refl.
    + unfold golden_w2. exact golden_w1_le_1.
Qed.

Lemma golden_uden_pos : forall t,
  0 <= t -> t <= 1 -> 0 < golden_uden t.
Proof.
  intros t Ht0 Ht1. unfold golden_uden.
  pose proof sqrt2_gt_1. nra.
Qed.

Lemma golden_uden_neq_0 : forall t,
  0 <= t -> t <= 1 -> golden_uden t <> 0.
Proof. intros t Ht0 Ht1. apply Rgt_not_eq, golden_uden_pos; assumption. Qed.

(* -------------------------------------------------------------------------- *)
(* Double-angle identities for atan.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma one_plus_sq_pos : forall x, 0 < 1 + x * x.
Proof.
  intro x. apply Rplus_lt_le_0_compat; [lra | apply Rle_0_sqr].
Qed.

Lemma one_plus_sq_neq : forall x, 1 + x * x <> 0.
Proof. intro x. apply Rgt_not_eq, one_plus_sq_pos. Qed.

Lemma one_plus_tan2 : forall a,
  cos a <> 0 ->
  1 + tan a * tan a = / (cos a * cos a).
Proof.
  intros a Hc.
  unfold tan, Rdiv.
  assert (Hc2 : cos a * cos a <> 0)
    by (apply Rmult_integral_contrapositive_currified; exact Hc).
  replace ((sin a * / cos a) * (sin a * / cos a))
    with (sin a * sin a * / (cos a * cos a))
    by (field; exact Hc).
  rewrite <- (Rinv_r (cos a * cos a) Hc2) at 1.
  rewrite <- Rmult_plus_distr_r.
  replace (cos a * cos a + sin a * sin a) with 1.
  2: { pose proof (sin2_cos2 a) as Hsc. unfold Rsqr in Hsc. lra. }
  rewrite Rmult_1_l. reflexivity.
Qed.

Lemma cos2_of_atan : forall x,
  cos (atan x) * cos (atan x) = / (1 + x * x).
Proof.
  intro x.
  assert (Hc : cos (atan x) <> 0) by (apply Rgt_not_eq, cos_atan_pos).
  pose proof (one_plus_tan2 (atan x) Hc) as Hsec.
  rewrite tan_atan in Hsec.
  apply (f_equal Rinv) in Hsec.
  rewrite Rinv_inv in Hsec.
  symmetry. exact Hsec.
Qed.

Lemma cos_2_atan : forall x,
  cos (2 * atan x) = (1 - x * x) / (1 + x * x).
Proof.
  intro x.
  set (a := atan x).
  assert (Htan : tan a = x) by (unfold a; apply tan_atan).
  assert (Hcos : 0 < cos a) by (unfold a; apply cos_atan_pos).
  assert (Hcos0 : cos a <> 0) by lra.
  rewrite cos_2a.
  replace (cos a * cos a - sin a * sin a)
    with (cos a * cos a * (1 - tan a * tan a))
    by (unfold tan; field; exact Hcos0).
  rewrite Htan.
  unfold a. rewrite cos2_of_atan.
  unfold Rdiv. ring.
Qed.

Lemma sin_2_atan : forall x,
  sin (2 * atan x) = (2 * x) / (1 + x * x).
Proof.
  intro x.
  set (a := atan x).
  assert (Htan : tan a = x) by (unfold a; apply tan_atan).
  assert (Hcos : 0 < cos a) by (unfold a; apply cos_atan_pos).
  assert (Hcos0 : cos a <> 0) by lra.
  rewrite sin_2a.
  replace (2 * sin a * cos a)
    with (2 * tan a * (cos a * cos a))
    by (unfold tan; field; exact Hcos0).
  rewrite Htan.
  unfold a. rewrite cos2_of_atan.
  unfold Rdiv. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Algebraic Weierstrass identities.                                          *)
(* -------------------------------------------------------------------------- *)

Definition golden_numx (t : R) : R :=
  bern2_0 t * (golden_w0 * px golden_p0)
  + bern2_1 t * (golden_w1 * px golden_p1)
  + bern2_2 t * (golden_w2 * px golden_p2).

Definition golden_numy (t : R) : R :=
  bern2_0 t * (golden_w0 * py golden_p0)
  + bern2_1 t * (golden_w1 * py golden_p1)
  + bern2_2 t * (golden_w2 * py golden_p2).

(* Cancel the weight √2/2. The only denominator is 2. *)
Lemma twice_half_sqrt2 : forall x,
  2 * x * (sqrt 2 / 2) = x * sqrt 2.
Proof. intro x. field; try lra. Qed.

Lemma twice_half_sqrt2_1 : forall x,
  2 * x * (sqrt 2 / 2 * 1) = x * sqrt 2.
Proof. intro x. field; try lra. Qed.

Lemma golden_numx_poly : forall t,
  golden_numx t = (1 - t) * (1 - t) + t * (1 - t) * sqrt 2.
Proof.
  intro t.
  unfold golden_numx, golden_w0, golden_w1, golden_w2,
         golden_p0, golden_p1, golden_p2, bern2_0, bern2_1, bern2_2.
  cbn [px py].
  rewrite (twice_half_sqrt2_1 (t * (1 - t))).
  ring.
Qed.

Lemma golden_numy_poly : forall t,
  golden_numy t = t * (1 - t) * sqrt 2 + t * t.
Proof.
  intro t.
  unfold golden_numy, golden_w0, golden_w1, golden_w2,
         golden_p0, golden_p1, golden_p2, bern2_0, bern2_1, bern2_2.
  cbn [px py].
  rewrite (twice_half_sqrt2_1 (t * (1 - t))).
  ring.
Qed.

Lemma nurbs2_den_golden_poly : forall t,
  nurbs2_den golden_w0 golden_w1 golden_w2 t
  = (1 - t) * (1 - t) + t * (1 - t) * sqrt 2 + t * t.
Proof.
  intro t.
  unfold nurbs2_den, golden_w0, golden_w1, golden_w2,
         bern2_0, bern2_1, bern2_2.
  rewrite (twice_half_sqrt2 (t * (1 - t))).
  ring.
Qed.

Lemma two_numx_uden : forall t,
  2 * golden_numx t = golden_uden t * golden_uden t - t * t.
Proof.
  intro t.
  rewrite golden_numx_poly.
  unfold golden_uden.
  set (s := sqrt 2).
  assert (Hs : s * s = 2) by (unfold s; apply sqrt2_sqr).
  replace (s + (1 - s) * t) with (s * (1 - t) + t) by ring.
  replace ((s * (1 - t) + t) * (s * (1 - t) + t) - t * t)
    with (s * s * ((1 - t) * (1 - t)) + 2 * s * (1 - t) * t)
    by ring.
  rewrite Hs.
  ring.
Qed.

Lemma two_den_uden : forall t,
  2 * nurbs2_den golden_w0 golden_w1 golden_w2 t
  = golden_uden t * golden_uden t + t * t.
Proof.
  intro t.
  rewrite nurbs2_den_golden_poly.
  unfold golden_uden.
  set (s := sqrt 2).
  assert (Hs : s * s = 2) by (unfold s; apply sqrt2_sqr).
  replace (s + (1 - s) * t) with (s * (1 - t) + t) by ring.
  replace ((s * (1 - t) + t) * (s * (1 - t) + t) + t * t)
    with (s * s * ((1 - t) * (1 - t)) + 2 * s * (1 - t) * t
          + 2 * (t * t))
    by ring.
  rewrite Hs.
  ring.
Qed.

Lemma two_numy_uden : forall t,
  2 * golden_numy t = 2 * t * golden_uden t.
Proof.
  intro t.
  rewrite golden_numy_poly.
  unfold golden_uden.
  ring.
Qed.

Lemma golden_weierstrass_x : forall t,
  0 <= t -> t <= 1 ->
  golden_numx t / nurbs2_den golden_w0 golden_w1 golden_w2 t
  = (1 - golden_u t * golden_u t) / (1 + golden_u t * golden_u t).
Proof.
  intros t Ht0 Ht1.
  set (D := nurbs2_den golden_w0 golden_w1 golden_w2 t).
  set (U := golden_uden t).
  assert (HD : 0 < D) by (unfold D; apply golden_den_pos; assumption).
  assert (HU : 0 < U) by (unfold U; apply golden_uden_pos; assumption).
  unfold golden_u. fold U. fold D.
  replace ((1 - (t / U) * (t / U)) / (1 + (t / U) * (t / U)))
    with ((U * U - t * t) / (U * U + t * t))
    by (field; nra).
  pose proof (two_numx_uden t) as Hx.
  pose proof (two_den_uden t) as Hd.
  fold D in Hd. fold U in Hx, Hd.
  replace (golden_numx t / D) with ((2 * golden_numx t) / (2 * D))
    by (field; lra).
  rewrite Hx, Hd. reflexivity.
Qed.

Lemma golden_weierstrass_y : forall t,
  0 <= t -> t <= 1 ->
  golden_numy t / nurbs2_den golden_w0 golden_w1 golden_w2 t
  = (2 * golden_u t) / (1 + golden_u t * golden_u t).
Proof.
  intros t Ht0 Ht1.
  set (D := nurbs2_den golden_w0 golden_w1 golden_w2 t).
  set (U := golden_uden t).
  assert (HD : 0 < D) by (unfold D; apply golden_den_pos; assumption).
  assert (HU : 0 < U) by (unfold U; apply golden_uden_pos; assumption).
  unfold golden_u. fold U. fold D.
  replace ((2 * (t / U)) / (1 + (t / U) * (t / U)))
    with ((2 * t * U) / (U * U + t * t))
    by (field; nra).
  pose proof (two_numy_uden t) as Hy.
  pose proof (two_den_uden t) as Hd.
  fold D in Hd. fold U in Hy, Hd.
  replace (golden_numy t / D) with ((2 * golden_numy t) / (2 * D))
    by (field; lra).
  rewrite Hy, Hd. reflexivity.
Qed.

Lemma golden_pt_on_circle : forall t,
  0 <= t -> t <= 1 ->
  nurbs2_pt golden_p0 golden_p1 golden_p2 golden_w0 golden_w1 golden_w2 t
  = circle_pt golden_origin 1 (golden_phi t).
Proof.
  intros t Ht0 Ht1.
  unfold nurbs2_pt, circle_pt, golden_phi, golden_origin.
  apply point_ext; cbn [px py].
  - (* Do not rewrite Rmult_1_l on the whole goal: the first 1* is
       golden_w0 · px, not the circle's r=1. Pin it to the cosine. *)
    rewrite Rplus_0_l.
    rewrite (Rmult_1_l (cos (2 * atan (golden_u t)))).
    rewrite cos_2_atan.
    fold (golden_numx t).
    apply golden_weierstrass_x; assumption.
  - rewrite Rplus_0_l.
    rewrite (Rmult_1_l (sin (2 * atan (golden_u t)))).
    rewrite sin_2_atan.
    fold (golden_numy t).
    apply golden_weierstrass_y; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Endpoints, monotonicity, explicit preimages of φ.                          *)
(* -------------------------------------------------------------------------- *)

Lemma golden_u_0 : golden_u 0 = 0.
Proof.
  unfold golden_u, golden_uden.
  field. exact sqrt2_neq_0.
Qed.

Lemma golden_u_1 : golden_u 1 = 1.
Proof.
  unfold golden_u, golden_uden.
  field. pose proof sqrt2_gt_1. lra.
Qed.

Lemma golden_phi_0 : golden_phi 0 = 0.
Proof. unfold golden_phi. rewrite golden_u_0, atan_0. lra. Qed.

Lemma golden_phi_1 : golden_phi 1 = PI / 2.
Proof. unfold golden_phi. rewrite golden_u_1, atan_1. lra. Qed.

Lemma golden_u_mono : forall s t,
  0 <= s -> s <= t -> t <= 1 -> golden_u s <= golden_u t.
Proof.
  intros s t Hs Hst Ht.
  assert (Hs1 : s <= 1) by lra.
  assert (Ht0 : 0 <= t) by lra.
  unfold golden_u, Rdiv.
  apply (Rmult_le_reg_r (golden_uden s * golden_uden t)).
  { apply Rmult_lt_0_compat; apply golden_uden_pos; assumption. }
  replace (s * / golden_uden s * (golden_uden s * golden_uden t))
    with (s * golden_uden t)
    by (field; apply golden_uden_neq_0; assumption).
  replace (t * / golden_uden t * (golden_uden s * golden_uden t))
    with (t * golden_uden s)
    by (field; apply golden_uden_neq_0; assumption).
  unfold golden_uden.
  assert (Hdiff :
      t * (sqrt 2 + (1 - sqrt 2) * s)
      - s * (sqrt 2 + (1 - sqrt 2) * t)
      = (t - s) * sqrt 2) by ring.
  assert (0 <= (t - s) * sqrt 2)
    by (apply Rmult_le_pos; [lra | apply Rlt_le, sqrt2_pos]).
  lra.
Qed.

Lemma golden_phi_mono : forall s t,
  0 <= s -> s <= t -> t <= 1 -> golden_phi s <= golden_phi t.
Proof.
  intros s t Hs Hst Ht.
  unfold golden_phi.
  apply Rmult_le_compat_l; [lra |].
  apply atan_le, golden_u_mono; assumption.
Qed.

Lemma tan_ge_0_on_0_PI4 : forall x,
  0 <= x -> x <= PI / 4 -> 0 <= tan x.
Proof.
  intros x Hx0 Hx1.
  destruct Hx0 as [Hlt | Heq].
  - rewrite <- tan_0. apply Rlt_le.
    pose proof PI_RGT_0.
    apply tan_increasing_1; lra.
  - subst. rewrite tan_0. lra.
Qed.

Lemma tan_le_1_on_0_PI4 : forall x,
  0 <= x -> x <= PI / 4 -> tan x <= 1.
Proof.
  intros x Hx0 Hx1.
  rewrite <- tan_PI4.
  destruct Hx1 as [Hlt | Heq].
  - apply Rlt_le.
    pose proof PI_RGT_0.
    apply tan_increasing_1; lra.
  - subst. apply Rle_refl.
Qed.

Lemma golden_pre_u_range : forall w,
  0 <= w -> w <= 1 ->
  0 <= golden_pre_u w <= 1.
Proof.
  intros w Hw0 Hw1.
  unfold golden_pre_u.
  assert (Hden : 0 < 1 + w * (sqrt 2 - 1)).
  { apply Rplus_lt_le_0_compat; [lra |].
    apply Rmult_le_pos; [exact Hw0 |].
    apply Rlt_le. pose proof sqrt2_gt_1. lra. }
  split.
  - unfold Rdiv.
    apply Rmult_le_pos.
    + apply Rmult_le_pos; [exact Hw0 | apply Rlt_le, sqrt2_pos].
    + apply Rlt_le, Rinv_0_lt_compat. exact Hden.
  - apply (Rmult_le_reg_r (1 + w * (sqrt 2 - 1))); [exact Hden |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
    replace (1 * (1 + w * (sqrt 2 - 1)))
      with (1 - w + w * sqrt 2) by ring.
    (*  w·√2 ≤ 1−w + w·√2  is  0 ≤ 1−w.  Do not apply
        Rplus_le_compat_r: the left side is not a sum. *)
    lra.
Qed.

Lemma golden_u_pre : forall w,
  0 <= w -> w <= 1 ->
  golden_u (golden_pre_u w) = w.
Proof.
  intros w Hw0 Hw1.
  unfold golden_u, golden_uden, golden_pre_u.
  field.
  pose proof sqrt2_gt_1.
  repeat split; try exact sqrt2_neq_0; nra.
Qed.

Lemma golden_phi_surj : forall v,
  golden_phi 0 <= v -> v <= golden_phi 1 ->
  exists u, 0 <= u /\ u <= 1 /\ golden_phi u = v.
Proof.
  intros v Hv0 Hv1.
  rewrite golden_phi_0 in Hv0.
  rewrite golden_phi_1 in Hv1.
  pose proof PI_RGT_0 as Hpi.
  set (w := tan (v / 2)).
  set (u := golden_pre_u w).
  assert (Hv2 : 0 <= v / 2 <= PI / 4) by lra.
  assert (Hw0 : 0 <= w) by (unfold w; apply tan_ge_0_on_0_PI4; lra).
  assert (Hw1 : w <= 1) by (unfold w; apply tan_le_1_on_0_PI4; lra).
  pose proof (golden_pre_u_range w Hw0 Hw1) as [Hu0 Hu1].
  exists u. split; [exact Hu0 | split; [exact Hu1 |]].
  unfold golden_phi, u.
  rewrite golden_u_pre by assumption.
  unfold w.
  rewrite atan_tan; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: the golden quarter circle has metric length π/2.                 *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"508-a","topic":"arc,metric","lemma":"nurbs2_golden_quarter_length","title":"Oracle golden rational quadratic quarter circle has metric length π/2","file":"theories/NurbsConicExact.v","witness":"508-a-golden-quarter","board":"#559"} *)

Theorem nurbs2_golden_quarter_length :
  is_curve_length golden_param 0 1 (PI / 2).
Proof.
  apply (is_curve_length_ext_on
           (fun t => circle_param golden_origin 1 (golden_phi t))).
  { intros t Ht0 Ht1. unfold circle_param, golden_param, nurbs2_param.
    symmetry. apply golden_pt_on_circle; assumption. }
  apply (is_curve_length_reparam
           (circle_param golden_origin 1) golden_phi 0 1 (PI / 2)).
  - lra.
  - apply golden_phi_mono.
  - apply golden_phi_surj.
  - rewrite golden_phi_0, golden_phi_1.
    replace (PI / 2) with (1 * (PI / 2 - 0)) by lra.
    apply arc_r_theta_is_curve_length; pose proof PI_RGT_0; lra.
Qed.

Print Assumptions nurbs2_golden_quarter_length.
