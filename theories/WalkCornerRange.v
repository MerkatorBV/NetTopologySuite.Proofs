(* ==========================================================================
   WalkCornerRange.v

   [H-bridge attack, C-3f discharge rung E-1] The RANGE-FORM corner
   threshold: the D-2 corner threshold pins `rho = rho_factor * delta`
   exactly, but composing corners with the D-1 rides needs `rho` FREE
   in a band -- the ride's in-span smallness `|delta * vx| < rho * |vy|`
   bounds rho BELOW (relative to delta), while the corner's clearance
   bounds cap it ABOVE.  Fortunately the corner tolerates exactly that:

     - the far-wall smallness `delta * C_i < rho * gap` is MONOTONE in
       rho (a lower bound `rho >= rho_factor * delta` suffices);
     - the clearance-ball bounds are monotone the other way (an upper
       cap `rho < t` suffices, same `t` as delta's).

   So `walk_corner_threshold_range`: under the same vertex-side
   hypotheses, there are `t > 0` and `rho_factor > 0` with the corner
   connected at EVERY `(rho, delta)` satisfying
   `0 < delta < t`, `rho_factor * delta <= rho < t`.
   The D-2 point form is the special case `rho := rho_factor * delta`
   (for small enough delta).

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Arith Lia.
From NTS.Proofs Require Import JordanRingKit.
From NTS.Proofs Require Import OverlayGraph Vec Azimuth Direction Dart
                               DartAngularOrder JCTHugStep RingClearance
                               SectorPath CornerSamples CornerConnector
                               FanGapSector FanCorner WalkCorners.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Band-form bound plumbing.                                               *)
(* -------------------------------------------------------------------------- *)

Lemma band_bound_lt :
  forall (rho delta ax ay M t eps : R),
    0 < delta -> delta < t -> 0 <= rho -> rho < t -> 1 <= M ->
    0 <= ax -> 0 <= ay -> ax <= M - 1 -> ay <= M - 1 ->
    t * (2 * M) <= eps ->
    rho * ax + delta * ay < eps.
Proof.
  intros rho delta ax ay M t eps Hd Hdt Hr Hrt HM Hax0 Hay0 Hax Hay Hkey.
  assert (H1 : rho * ax <= rho * (M - 1))
    by (apply Rmult_le_compat_l; lra).
  assert (H2 : delta * ay <= delta * (M - 1))
    by (apply Rmult_le_compat_l; lra).
  assert (H3 : rho * (M - 1) < t * (M - 1) \/ rho * (M - 1) <= t * (M - 1)).
  { right. apply Rmult_le_compat_r; lra. }
  assert (H4 : rho * (M - 1) <= t * (M - 1))
    by (apply Rmult_le_compat_r; lra).
  assert (H5 : delta * (M - 1) < t * (M - 1) + t)
    by nra.
  nra.
Qed.

Lemma band_bound_single :
  forall (delta ax M t eps : R),
    0 < delta -> delta < t -> 1 <= M ->
    0 <= ax -> ax <= M - 1 ->
    t * (2 * M) <= eps ->
    delta * ax < eps.
Proof.
  intros delta ax M t eps Hd Hdt HM Hax0 Hax Hkey.
  assert (H1 : delta * ax <= delta * (M - 1))
    by (apply Rmult_le_compat_l; lra).
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The range-form threshold.                                               *)
(* -------------------------------------------------------------------------- *)

Theorem walk_corner_threshold_range :
  forall (r : Ring) (v a b : Point) (u1 u2 : Vec),
    no_horizontal_edges r ->
    (forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
       ~ on_edge f v) ->
    ~ in_open_sector u1 u2 (point_diff a v) ->
    ~ in_open_sector u1 u2 (point_diff b v) ->
    vcross u1 u2 <> 0 ->
    exists t rho_factor : R,
      0 < t /\ 0 < rho_factor /\
      forall delta rho,
        0 < delta < t -> rho_factor * delta <= rho -> rho < t ->
        connected_in_complement_cont r
          (point_at v (corner_sample_in u1 rho delta))
          (point_at v (corner_sample_out u2 rho delta)).
Proof.
  intros r v a b u1 u2 Hnoh Hoffv Hma Hmb Hcne.
  destruct (vertex_pruned_clearance r v (a, v) (v, b) Hnoh Hoffv)
    as [eps [Heps Hball]].
  set (M := Rmax (Rmax (Rabs (vx u1)) (Rabs (vy u1)))
                 (Rmax (Rabs (vx u2)) (Rabs (vy u2))) + 1).
  assert (HM : Rmax (Rmax (Rabs (vx u1)) (Rabs (vy u1)))
                    (Rmax (Rabs (vx u2)) (Rabs (vy u2))) = M - 1)
    by (unfold M; ring).
  assert (Hb1x : Rabs (vx u1) <= M - 1)
    by (rewrite <- HM; eapply Rle_trans; [ apply Rmax_l | apply Rmax_l ]).
  assert (Hb1y : Rabs (vy u1) <= M - 1)
    by (rewrite <- HM; eapply Rle_trans; [ apply Rmax_r | apply Rmax_l ]).
  assert (Hb2x : Rabs (vx u2) <= M - 1)
    by (rewrite <- HM; eapply Rle_trans; [ apply Rmax_l | apply Rmax_r ]).
  assert (Hb2y : Rabs (vy u2) <= M - 1)
    by (rewrite <- HM; eapply Rle_trans; [ apply Rmax_r | apply Rmax_r ]).
  assert (HM1 : 1 <= M).
  { pose proof (Rle_trans _ _ _ (Rabs_pos (vx u1)) Hb1x). lra. }
  set (t := eps / (2 * M)).
  assert (Ht : 0 < t) by (unfold t; apply Rdiv_lt_0_compat; lra).
  assert (Hkey : t * (2 * M) <= eps)
    by (unfold t; unfold Rdiv; right; field; lra).
  destruct (Rdichotomy _ _ Hcne) as [Hneg | Hgt].
  - (* REFLEX gap: any rho in the band works; sigma := delta *)
    exists t, 1.
    split; [ exact Ht | split; [ lra | ] ].
    intros delta rho Hd Hlo Hhi.
    assert (Hrpos : 0 < rho) by nra.
    apply (fan_corner_connected_reflex r v a b u1 u2 eps
             rho delta delta Hball Hma Hmb Hneg);
      try lra;
      try (apply (band_bound_lt rho delta _ _ M t eps);
           solve [ lra | apply Rabs_pos | assumption ]);
      try (apply (band_bound_single delta _ M t eps);
           solve [ lra | apply Rabs_pos | assumption ]).
  - (* CONVEX gap: the lower band edge makes the far wall identical *)
    assert (Hpos : 0 < vcross u1 u2) by lra.
    set (C1 := Rabs (vcross (vperpL u1) u2)).
    set (C2 := Rabs (vcross u1 (vperpL u2))).
    assert (HC1 : 0 <= C1) by apply Rabs_pos.
    assert (HC2 : 0 <= C2) by apply Rabs_pos.
    set (F := (C1 + C2 + 1) / vcross u1 u2).
    assert (HF : 0 < F)
      by (unfold F; apply Rdiv_lt_0_compat; lra).
    assert (HFgap : F * vcross u1 u2 = C1 + C2 + 1)
      by (unfold F; field; lra).
    exists t, F.
    split; [ exact Ht | split; [ exact HF | ] ].
    intros delta rho Hd Hlo Hhi.
    assert (Hrpos : 0 < rho) by nra.
    apply (fan_corner_connected_convex r v a b u1 u2 eps
             rho delta Hball Hma Hmb Hpos);
      try lra;
      try (apply (band_bound_lt rho delta _ _ M t eps);
           solve [ lra | apply Rabs_pos | assumption ]).
    + (* delta * C1 < rho * gap: monotone in rho above the band edge *)
      fold C1.
      assert (HA : 0 <= delta * C2) by nra.
      assert (HB : F * delta * vcross u1 u2
                     = delta * C1 + delta * C2 + delta).
      { replace (F * delta * vcross u1 u2)
          with (F * vcross u1 u2 * delta) by ring.
        rewrite HFgap. ring. }
      assert (HC : F * delta * vcross u1 u2 <= rho * vcross u1 u2).
      { replace (F * delta * vcross u1 u2)
          with ((F * delta) * vcross u1 u2) by ring.
        apply Rmult_le_compat_r; lra. }
      lra.
    + fold C2.
      assert (HA : 0 <= delta * C1) by nra.
      assert (HB : F * delta * vcross u1 u2
                     = delta * C1 + delta * C2 + delta).
      { replace (F * delta * vcross u1 u2)
          with (F * vcross u1 u2 * delta) by ring.
        rewrite HFgap. ring. }
      assert (HC : F * delta * vcross u1 u2 <= rho * vcross u1 u2).
      { replace (F * delta * vcross u1 u2)
          with ((F * delta) * vcross u1 u2) by ring.
        apply Rmult_le_compat_r; lra. }
      lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Band arithmetic; allowlist axioms only.                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions band_bound_lt.
Print Assumptions walk_corner_threshold_range.
