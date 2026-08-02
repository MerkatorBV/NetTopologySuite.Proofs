(* ============================================================================
   NetTopologySuite.Proofs.BufferMiterClip
   ----------------------------------------------------------------------------
   GREEN for micro-claim 65-d: when the unrestricted miter apex overshoots
   the configured limit sphere of radius L·d (L ≥ 1, d > 0), the emitted
   join vertex is the ray-scale clip — at Euclidean distance exactly L·d
   from the corner V, and on the segment from V through the unrestricted
   apex (not beyond the limit, not left at the raw apex).

   BufferMiter.v ships the unrestricted apex (`miter_apex`) and the limit
   *decision* (`miter_within_limit_iff`).  This file defines the clipped
   emitter `limited_miter_apex` and proves the 65-d contract under the
   overshoot hypothesis.

   Proof structure (refactor): a point-level core `ray_scale_to_radius`
   (scale M about V to length a under a² < dist_sq V M) carries the
   algebra; the headline instantiates it at a = L·d and M = miter_apex.

   Mirrors eval/Claim65d.v (same WITNESS tag).

   No `Admitted`, no `Axiom`, no `Parameter`.  Pure-R three-axiom footprint.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Vec Distance Segment BufferMiter.
Open Scope R_scope.

(* WITNESS {"claimId":"65-d","topic":"buffer","lemma":"miter_clipped_at_limit_distance","title":"Mitre join vertex is clipped at limit distance L·d when unrestricted apex overshoots"} *)

(* Limit-clipped join vertex: ray from V through the unrestricted apex,
   scaled to length L·d. *)
Definition limited_miter_apex (V : Point) (ein eout : Vec) (d L : R) : Point :=
  let M := miter_apex V ein eout d in
  let dx := px M - px V in
  let dy := py M - py V in
  let r := sqrt (dx * dx + dy * dy) in
  mkPoint (px V + (L * d) * dx / r) (py V + (L * d) * dy / r).

(* Point-level core: Q is V advanced a distance a along V→M. *)
Definition ray_scale_point (V M : Point) (a : R) : Point :=
  let dx := px M - px V in
  let dy := py M - py V in
  let r := sqrt (dx * dx + dy * dy) in
  mkPoint (px V + a * dx / r) (py V + a * dy / r).

Lemma limited_miter_apex_is_ray_scale :
  forall V ein eout d L,
    limited_miter_apex V ein eout d L =
    ray_scale_point V (miter_apex V ein eout d) (L * d).
Proof. intros. reflexivity. Qed.

(* Core algebra: under a > 0 and a² < |M−V|², ray-scale to length a sits
   at dist_sq = a² and on the segment V—M. *)
Lemma ray_scale_to_radius :
  forall (V M : Point) (a : R),
    0 < a ->
    a * a < dist_sq V M ->
    dist_sq V (ray_scale_point V M a) = a * a /\
    between V M (ray_scale_point V M a).
Proof.
  intros V M a Ha Hover.
  set (dx := px M - px V).
  set (dy := py M - py V).
  set (r := sqrt (dx * dx + dy * dy)).
  assert (Hnn : 0 <= dx * dx + dy * dy).
  { apply Rplus_le_le_0_compat;
      [ pose proof (Rle_0_sqr dx) as H; unfold Rsqr in H; exact H
      | pose proof (Rle_0_sqr dy) as H; unfold Rsqr in H; exact H ]. }
  assert (Hr2 : r * r = dx * dx + dy * dy)
    by (unfold r; apply sqrt_sqrt; exact Hnn).
  assert (Hdist : dist_sq V M = dx * dx + dy * dy).
  { unfold dist_sq, dx, dy.
    replace (px V - px M) with (- (px M - px V)) by ring.
    replace (py V - py M) with (- (py M - py V)) by ring.
    ring. }
  assert (Hover' : a * a < r * r)
    by (rewrite Hr2, <- Hdist; exact Hover).
  assert (Hrpos : 0 < r).
  { assert (Hrne : r <> 0).
    { intro Hz. rewrite Hz in Hover'. rewrite Rmult_0_l in Hover'. nra. }
    pose proof (sqrt_pos (dx * dx + dy * dy)) as Hge.
    change (0 <= r) in Hge. lra. }
  assert (Hr0 : r <> 0) by (apply Rgt_not_eq; exact Hrpos).
  assert (Har : a < r).
  { apply Rsqr_incrst_0; try nra. unfold Rsqr. nra. }
  set (s := a / r).
  assert (Hs0 : 0 < s).
  { unfold s, Rdiv. apply Rmult_lt_0_compat; [ exact Ha | ].
    apply Rinv_0_lt_compat. exact Hrpos. }
  assert (Hs1 : s < 1).
  { unfold s. apply (Rmult_lt_reg_r r); [ exact Hrpos | ].
    replace (a / r * r) with a by (field; exact Hr0). lra. }
  assert (Hlim : ray_scale_point V M a =
                 mkPoint (px V + a * dx / r) (py V + a * dy / r)).
  { unfold ray_scale_point, dx, dy, r. reflexivity. }
  split.
  - rewrite Hlim. unfold dist_sq; simpl.
    replace (px V - (px V + a * dx / r)) with (- (a * dx / r)) by ring.
    replace (py V - (py V + a * dy / r)) with (- (a * dy / r)) by ring.
    replace ((- (a * dx / r)) * (- (a * dx / r))
             + (- (a * dy / r)) * (- (a * dy / r)))
      with ((a * dx / r) * (a * dx / r) + (a * dy / r) * (a * dy / r))
      by ring.
    transitivity (a * a * (dx * dx + dy * dy) / (r * r)).
    { field; exact Hr0. }
    rewrite <- Hr2. field; exact Hr0.
  - rewrite Hlim. unfold between.
    exists s. repeat split; [ lra | lra | | ].
    + unfold s. fold dx.
      replace (px V + a * dx / r)
        with ((1 - a / r) * px V + (a / r) * px M).
      2: { unfold dx. field; exact Hr0. }
      reflexivity.
    + unfold s. fold dy.
      replace (py V + a * dy / r)
        with ((1 - a / r) * py V + (a / r) * py M).
      2: { unfold dy. field; exact Hr0. }
      reflexivity.
Qed.

Theorem miter_clipped_at_limit_distance :
  forall (V : Point) (ein eout : Vec) (d L : R),
    0 < d ->
    1 <= L ->
    ein <> vzero ->
    eout <> vzero ->
    miter_det ein eout <> 0 ->
    (L * d) * (L * d) < dist_sq V (miter_apex V ein eout d) ->
    dist_sq V (limited_miter_apex V ein eout d L) = (L * d) * (L * d) /\
    between V (miter_apex V ein eout d)
              (limited_miter_apex V ein eout d L).
Proof.
  intros V ein eout d L Hd HL _Hin _Hout _Hdet Hover.
  rewrite limited_miter_apex_is_ray_scale.
  apply ray_scale_to_radius; [ nra | exact Hover ].
Qed.

Print Assumptions miter_clipped_at_limit_distance.
