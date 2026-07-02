(* ==========================================================================
   CornerSamples.v

   [H-bridge attack, rung C-3b, step 3] Concrete face-side corner samples,
   their sector certificates, ball-sized hop points, and sup-norm bounds --
   the pure-algebra half of the two-dart corner connector.

   Per the machine-checked orientation (`NextOrientationWitness.v`), the
   face walk keeps its face on the RIGHT of each dart, and the corner
   sector at a shared vertex `v` is the CCW gap from `u1 := ddir (twin x)`
   (pointing from `v` back along the arriving dart) to `u2 := ddir y`
   (pointing from `v` along the departing dart).  Relative to `v`:

     - the right-of-arriving-dart sample is
         `corner_sample_in u1 rho delta := rho*u1 + delta*perpL(u1)`
       (right of `x` = CCW of `u1` = the perpL offset), and the
       right-of-departing-dart sample is
         `corner_sample_out u2 rho delta := rho*u2 - delta*perpL(u2)`
       (right of `y` = CW of `u2`);
     - their NEAR-WALL certificates are unconditional pure algebra:
       `vcross u1 (sample_in) = delta*|u1|^2 > 0` and
       `vcross (sample_out) u2 = delta*|u2|^2 > 0` -- exactly the two
       half-certificates `SectorPath.sector_path_reflex` consumes;
     - in a CONVEX gap the kernel needs the FAR-WALL certificates too;
       they hold under an explicit smallness inequality
       (`delta * |cross(perp, wall)| < rho * cross(u1,u2)`);
     - the reflex three-hop polyline must fit inside a vertex clearance
       ball, so the hop points are SCALED: `sigma*perpL(u1)` and
       `sigma*(-u1)` -- the certificates are scale-invariant, and the
       scaled hop lemmas below mirror `SectorPath`'s unscaled ones;
     - `vaffine_bound_x`/`_y` bound every chord point's sup-norm by its
       endpoints', and the sample/hop bounds are explicit linear
       expressions in `rho`, `delta`, `sigma` -- so the ring-side assembly
       (next step) can size everything into `RingClearance`'s ball.

   Pure Vec/R algebra; no `Admitted` / `Axiom` / `Parameter`; allowlist
   axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Vec SectorPath.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  More cross-product plumbing.                                            *)
(* -------------------------------------------------------------------------- *)

Lemma vcross_add_r :
  forall u a b, vcross u (vadd a b) = vcross u a + vcross u b.
Proof. intros u a b. unfold vcross, vadd. cbn. ring. Qed.

Lemma vcross_add_l :
  forall u a b, vcross (vadd a b) u = vcross a u + vcross b u.
Proof. intros u a b. unfold vcross, vadd. cbn. ring. Qed.

Lemma vcross_scale_l :
  forall u v c, vcross (vscale c u) v = c * vcross u v.
Proof. intros u v c. unfold vcross, vscale. cbn. ring. Qed.

Lemma vcross_self : forall u, vcross u u = 0.
Proof. intros u. unfold vcross. ring. Qed.

Lemma vcross_perpL_l :
  forall u, vcross (vperpL u) u = - (vx u * vx u + vy u * vy u).
Proof. intros u. unfold vcross, vperpL. cbn. ring. Qed.

(* -a <= a-abs bridge used in the far-wall certificates. *)
Lemma neg_abs_le : forall a : R, - Rabs a <= a.
Proof.
  intro a. pose proof (Rle_abs (- a)) as H. rewrite Rabs_Ropp in H. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The concrete samples and their near-wall certificates.                  *)
(* -------------------------------------------------------------------------- *)

(* Right of the ARRIVING dart, near the corner: `u1` points from the vertex
   back along the dart, and "right of the dart" is the CCW side of `u1`. *)
Definition corner_sample_in (u1 : Vec) (rho delta : R) : Vec :=
  vadd (vscale rho u1) (vscale delta (vperpL u1)).

(* Right of the DEPARTING dart, near the corner: `u2` points from the vertex
   along the dart, and "right of the dart" is the CW side of `u2`. *)
Definition corner_sample_out (u2 : Vec) (rho delta : R) : Vec :=
  vadd (vscale rho u2) (vscale delta (vneg (vperpL u2))).

Lemma corner_sample_in_cert :
  forall u1 rho delta,
    u1 <> vzero -> 0 < delta ->
    0 < vcross u1 (corner_sample_in u1 rho delta).
Proof.
  intros u1 rho delta Hu Hd.
  unfold corner_sample_in.
  rewrite vcross_add_r, !vcross_scale_r, vcross_self.
  pose proof (vperpL_cross_pos u1 Hu). nra.
Qed.

Lemma corner_sample_out_cert :
  forall u2 rho delta,
    u2 <> vzero -> 0 < delta ->
    0 < vcross (corner_sample_out u2 rho delta) u2.
Proof.
  intros u2 rho delta Hu Hd.
  unfold corner_sample_out.
  rewrite vcross_add_l, !vcross_scale_l, vcross_self.
  rewrite vcross_neg_l, vcross_perpL_l.
  pose proof (vperpL_cross_pos u2 Hu).
  rewrite vcross_perpL in H. nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Far-wall certificates for the CONVEX gap (explicit smallness).          *)
(* -------------------------------------------------------------------------- *)

Lemma corner_sample_in_cert_far :
  forall u1 u2 rho delta,
    0 < vcross u1 u2 -> 0 < rho -> 0 <= delta ->
    delta * Rabs (vcross (vperpL u1) u2) < rho * vcross u1 u2 ->
    0 < vcross (corner_sample_in u1 rho delta) u2.
Proof.
  intros u1 u2 rho delta Hc Hr Hd Hsmall.
  unfold corner_sample_in.
  rewrite vcross_add_l, !vcross_scale_l.
  pose proof (neg_abs_le (vcross (vperpL u1) u2)).
  pose proof (Rabs_pos (vcross (vperpL u1) u2)).
  nra.
Qed.

Lemma corner_sample_out_cert_far :
  forall u1 u2 rho delta,
    0 < vcross u1 u2 -> 0 < rho -> 0 <= delta ->
    delta * Rabs (vcross u1 (vperpL u2)) < rho * vcross u1 u2 ->
    0 < vcross u1 (corner_sample_out u2 rho delta).
Proof.
  intros u1 u2 rho delta Hc Hr Hd Hsmall.
  unfold corner_sample_out.
  rewrite vcross_add_r, !vcross_scale_r, vcross_neg_r.
  pose proof (neg_abs_le (- vcross u1 (vperpL u2))).
  rewrite Rabs_Ropp in H.
  pose proof (Rabs_pos (vcross u1 (vperpL u2))).
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Scaled reflex hops: the polyline fits inside any clearance ball.        *)
(* -------------------------------------------------------------------------- *)

Lemma sector_path_reflex_hop1_scaled :
  forall u1 u2 w1 sigma,
    vcross u1 u2 < 0 -> u1 <> vzero -> 0 < sigma ->
    0 < vcross u1 w1 ->
    forall t, 0 <= t <= 1 ->
      in_open_sector u1 u2 (vaffine t w1 (vscale sigma (vperpL u1))).
Proof.
  intros u1 u2 w1 sigma Hc Hu Hs H1 t Ht.
  right. split; [ exact Hc | left ].
  rewrite vcross_affine_r, vcross_scale_r.
  pose proof (vperpL_cross_pos u1 Hu) as Hpos.
  assert (Hsp : 0 < sigma * vcross u1 (vperpL u1)) by nra.
  set (S := sigma * vcross u1 (vperpL u1)) in *.
  nra.
Qed.

Lemma sector_path_reflex_hop2_scaled :
  forall u1 u2 sigma,
    vcross u1 u2 < 0 -> u1 <> vzero -> 0 < sigma ->
    forall t, 0 <= t <= 1 ->
      in_open_sector u1 u2
        (vaffine t (vscale sigma (vperpL u1)) (vscale sigma (vneg u1))).
Proof.
  intros u1 u2 sigma Hc Hu Hs t Ht.
  right. split; [ exact Hc | ].
  destruct (Rlt_dec t 1) as [Ht1 | Ht1].
  - left. rewrite vcross_affine_r, !vcross_scale_r, vcross_neg_r, vcross_self.
    pose proof (vperpL_cross_pos u1 Hu) as Hpos.
    assert (Hsp : 0 < sigma * vcross u1 (vperpL u1)) by nra.
    set (S := sigma * vcross u1 (vperpL u1)) in *.
    nra.
  - right.
    assert (Ht1' : t = 1) by lra. subst t.
    rewrite vaffine_1, vcross_scale_l, vcross_neg_l. nra.
Qed.

Lemma sector_path_reflex_hop3_scaled :
  forall u1 u2 w2 sigma,
    vcross u1 u2 < 0 -> 0 < sigma ->
    0 < vcross w2 u2 ->
    forall t, 0 <= t <= 1 ->
      in_open_sector u1 u2 (vaffine t (vscale sigma (vneg u1)) w2).
Proof.
  intros u1 u2 w2 sigma Hc Hs H2 t Ht.
  right. split; [ exact Hc | right ].
  rewrite vcross_affine_l, vcross_scale_l, vcross_neg_l.
  assert (Hsp : 0 < sigma * - vcross u1 u2) by nra.
  set (S := sigma * - vcross u1 u2) in *.
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Sup-norm bounds for ball sizing.                                        *)
(* -------------------------------------------------------------------------- *)

(* A chord point's coordinates are bounded by its endpoints'. *)
Lemma vaffine_bound_x :
  forall a b t, 0 <= t <= 1 ->
    Rabs (vx (vaffine t a b)) <= Rmax (Rabs (vx a)) (Rabs (vx b)).
Proof.
  intros a b t Ht.
  unfold vaffine, vadd, vscale. cbn.
  pose proof (Rmax_l (Rabs (vx a)) (Rabs (vx b))).
  pose proof (Rmax_r (Rabs (vx a)) (Rabs (vx b))).
  eapply Rle_trans; [ apply Rabs_triang | ].
  rewrite !Rabs_mult.
  rewrite (Rabs_right (1 - t)) by lra.
  rewrite (Rabs_right t) by lra.
  pose proof (Rabs_pos (vx a)). pose proof (Rabs_pos (vx b)).
  nra.
Qed.

Lemma vaffine_bound_y :
  forall a b t, 0 <= t <= 1 ->
    Rabs (vy (vaffine t a b)) <= Rmax (Rabs (vy a)) (Rabs (vy b)).
Proof.
  intros a b t Ht.
  unfold vaffine, vadd, vscale. cbn.
  pose proof (Rmax_l (Rabs (vy a)) (Rabs (vy b))).
  pose proof (Rmax_r (Rabs (vy a)) (Rabs (vy b))).
  eapply Rle_trans; [ apply Rabs_triang | ].
  rewrite !Rabs_mult.
  rewrite (Rabs_right (1 - t)) by lra.
  rewrite (Rabs_right t) by lra.
  pose proof (Rabs_pos (vy a)). pose proof (Rabs_pos (vy b)).
  nra.
Qed.

(* The samples' coordinates are explicit linear expressions in rho, delta. *)
Lemma corner_sample_in_bound :
  forall u1 rho delta, 0 <= rho -> 0 <= delta ->
    Rabs (vx (corner_sample_in u1 rho delta))
      <= rho * Rabs (vx u1) + delta * Rabs (vy u1) /\
    Rabs (vy (corner_sample_in u1 rho delta))
      <= rho * Rabs (vy u1) + delta * Rabs (vx u1).
Proof.
  intros u1 rho delta Hr Hd.
  unfold corner_sample_in, vadd, vscale, vperpL. cbn.
  split.
  - eapply Rle_trans; [ apply Rabs_triang | ].
    rewrite !Rabs_mult, Rabs_Ropp.
    rewrite (Rabs_right rho) by lra. rewrite (Rabs_right delta) by lra.
    lra.
  - eapply Rle_trans; [ apply Rabs_triang | ].
    rewrite !Rabs_mult.
    rewrite (Rabs_right rho) by lra. rewrite (Rabs_right delta) by lra.
    lra.
Qed.

Lemma corner_sample_out_bound :
  forall u2 rho delta, 0 <= rho -> 0 <= delta ->
    Rabs (vx (corner_sample_out u2 rho delta))
      <= rho * Rabs (vx u2) + delta * Rabs (vy u2) /\
    Rabs (vy (corner_sample_out u2 rho delta))
      <= rho * Rabs (vy u2) + delta * Rabs (vx u2).
Proof.
  intros u2 rho delta Hr Hd.
  unfold corner_sample_out, vadd, vscale, vneg, vperpL. cbn.
  split.
  - eapply Rle_trans; [ apply Rabs_triang | ].
    rewrite !Rabs_mult, !Rabs_Ropp.
    rewrite (Rabs_right rho) by lra. rewrite (Rabs_right delta) by lra.
    lra.
  - eapply Rle_trans; [ apply Rabs_triang | ].
    rewrite !Rabs_mult, !Rabs_Ropp.
    rewrite (Rabs_right rho) by lra. rewrite (Rabs_right delta) by lra.
    lra.
Qed.

(* The scaled hop points' coordinates. *)
Lemma hop_perpL_bound :
  forall u1 sigma, 0 <= sigma ->
    Rabs (vx (vscale sigma (vperpL u1))) <= sigma * Rabs (vy u1) /\
    Rabs (vy (vscale sigma (vperpL u1))) <= sigma * Rabs (vx u1).
Proof.
  intros u1 sigma Hs.
  unfold vscale, vperpL. cbn.
  split; rewrite Rabs_mult, ?Rabs_Ropp, (Rabs_right sigma) by lra; lra.
Qed.

Lemma hop_neg_bound :
  forall u1 sigma, 0 <= sigma ->
    Rabs (vx (vscale sigma (vneg u1))) <= sigma * Rabs (vx u1) /\
    Rabs (vy (vscale sigma (vneg u1))) <= sigma * Rabs (vy u1).
Proof.
  intros u1 sigma Hs.
  unfold vscale, vneg. cbn.
  split; rewrite Rabs_mult, ?Rabs_Ropp, (Rabs_right sigma) by lra; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Pure Vec/R algebra; allowlist axioms only.                    *)
(* -------------------------------------------------------------------------- *)

Print Assumptions corner_sample_in_cert.
Print Assumptions corner_sample_out_cert.
Print Assumptions sector_path_reflex_hop2_scaled.
Print Assumptions vaffine_bound_x.
