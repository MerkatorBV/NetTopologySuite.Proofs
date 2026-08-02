(* ============================================================================
   nts-eval micro unit — claimId 65-d (GREEN)
   Red planted 2026-08-02 · Green closed 2026-08-02 · Refactor 2026-08-02
   ----------------------------------------------------------------------------
   When a mitre join's unrestricted apex length exceeds the configured
   mitre limit L·d (L ≥ 1, d > 0), the emitted join vertex is the
   LIMIT-CLIPPED point on the mitre ray: distance exactly L·d from V and
   on the segment V — unrestricted miter_apex.

   GREEN.  Headline closed via the point-level core `ray_scale_to_radius`
   (same factoring as production `theories/BufferMiterClip.v`).  WITNESS
   tag shared.  Board plan text said "65-b"; that id is already round-endcap
   Green — this clip obligation is 65-d.

   Rational witness pins (Qed at Red): unit right-angle corner
   V=(0,0), ein=(1,0), eout=(0,1), d=1, L=1 → apex (−1,1), dist_sq=2>1;
   mismatch probes reject raw apex and beyond-limit ray points.

   WITNESS claimId: 65-d
   Lemma: miter_clipped_at_limit_distance
   ========================================================================== *)

(* WITNESS {"claimId":"65-d","topic":"buffer","lemma":"miter_clipped_at_limit_distance","title":"Mitre join vertex is clipped at limit distance L·d when unrestricted apex overshoots"} *)

From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

Record Point : Type := mkPoint { px : R; py : R }.
Record Vec   : Type := mkVec   { vx : R; vy : R }.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

Definition vmag_sq (v : Vec) : R := vx v * vx v + vy v * vy v.
Definition vmag (v : Vec) : R := sqrt (vmag_sq v).
Definition vzero : Vec := mkVec 0 0.

Definition miter_det (ein eout : Vec) : R :=
  vx ein * vy eout - vy ein * vx eout.

Definition miter_apex (V : Point) (ein eout : Vec) (d : R) : Point :=
  mkPoint
    (px V + d * (vmag ein * vx eout - vmag eout * vx ein) / miter_det ein eout)
    (py V + d * (vmag ein * vy eout - vmag eout * vy ein) / miter_det ein eout).

(* Point-level clip (production: BufferMiterClip.ray_scale_point). *)
Definition ray_scale_point (V M : Point) (a : R) : Point :=
  let dx := px M - px V in
  let dy := py M - py V in
  let r := sqrt (dx * dx + dy * dy) in
  mkPoint (px V + a * dx / r) (py V + a * dy / r).

Definition limited_miter_apex (V : Point) (ein eout : Vec) (d L : R) : Point :=
  ray_scale_point V (miter_apex V ein eout d) (L * d).

Definition between (V M Q : Point) : Prop :=
  exists s : R, 0 <= s /\ s <= 1 /\
    px Q = (1 - s) * px V + s * px M /\
    py Q = (1 - s) * py V + s * py M.

Definition miter_clipped_at_limit_distance_claim : Prop :=
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

(* Core algebra (shared with production BufferMiterClip.ray_scale_to_radius). *)
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

Lemma miter_clipped_at_limit_distance :
  miter_clipped_at_limit_distance_claim.
Proof.
  unfold miter_clipped_at_limit_distance_claim, limited_miter_apex.
  intros V ein eout d L Hd HL _Hin _Hout _Hdet Hover.
  apply ray_scale_to_radius; [ nra | exact Hover ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Rational witness pins.                                                     *)
(* Unit right-angle corner: V=(0,0), ein=(1,0), eout=(0,1), d=1, L=1.         *)
(* -------------------------------------------------------------------------- *)

Definition w_V : Point := mkPoint 0 0.
Definition w_ein  : Vec := mkVec 1 0.
Definition w_eout : Vec := mkVec 0 1.
Definition w_d : R := 1.
Definition w_L : R := 1.
Definition w_apex : Point := miter_apex w_V w_ein w_eout w_d.

Lemma w_vmag_unit : vmag w_ein = 1 /\ vmag w_eout = 1.
Proof.
  unfold vmag, vmag_sq, w_ein, w_eout; simpl.
  split; (replace (_ + _) with 1 by ring; exact sqrt_1).
Qed.

Lemma w_apex_eq : w_apex = mkPoint (-1) 1.
Proof.
  unfold w_apex, miter_apex, w_V, w_d.
  destruct w_vmag_unit as [Hei Heo]. rewrite Hei, Heo.
  unfold w_ein, w_eout, miter_det; cbn [vx vy px py].
  f_equal; field.
Qed.

Lemma w_unlimited_dist_sq : dist_sq w_V w_apex = 2.
Proof. rewrite w_apex_eq. unfold dist_sq, w_V; simpl. lra. Qed.

Lemma w_overshoots_limit :
  (w_L * w_d) * (w_L * w_d) < dist_sq w_V w_apex.
Proof. unfold w_L, w_d. rewrite w_unlimited_dist_sq. lra. Qed.

Lemma w_claim_hyps :
  0 < w_d /\ 1 <= w_L /\
  w_ein <> vzero /\ w_eout <> vzero /\
  miter_det w_ein w_eout <> 0 /\
  (w_L * w_d) * (w_L * w_d) < dist_sq w_V w_apex.
Proof.
  unfold w_d, w_L, w_ein, w_eout, vzero, miter_det; simpl.
  repeat split; try lra;
    [ intros H; inversion H; lra
    | intros H; inversion H; lra
    | exact w_overshoots_limit ].
Qed.

(* MISMATCH PROBE 1: raw apex is not at the limit distance. *)
Lemma w_probe_unlimited_not_at_limit :
  dist_sq w_V w_apex <> (w_L * w_d) * (w_L * w_d).
Proof. unfold w_L, w_d. rewrite w_unlimited_dist_sq. lra. Qed.

(* MISMATCH PROBE 2: beyond-limit ray point is not the clip. *)
Definition w_beyond : Point := mkPoint (-2) 2.

Lemma w_beyond_on_ray : between w_V w_beyond w_apex.
Proof.
  unfold between, w_V, w_beyond. rewrite w_apex_eq; simpl.
  exists (1 / 2). repeat split; lra.
Qed.

Lemma w_probe_beyond_not_at_limit :
  dist_sq w_V w_beyond <> (w_L * w_d) * (w_L * w_d).
Proof. unfold dist_sq, w_V, w_beyond, w_L, w_d; simpl. lra. Qed.

Lemma w_limit_radius_sq : (w_L * w_d) * (w_L * w_d) = 1.
Proof. unfold w_L, w_d. lra. Qed.
