(* ============================================================================
   nts-eval micro unit — claimId 65-d (GREEN)
   Red planted 2026-08-02 · Green closed 2026-08-02
   ----------------------------------------------------------------------------
   When a mitre join's unrestricted apex length exceeds the configured
   mitre limit L·d (L ≥ 1, d > 0), the emitted join vertex is the
   LIMIT-CLIPPED point on the mitre ray: it lies on the segment from the
   corner V through the unrestricted miter_apex, at Euclidean distance
   exactly L·d from V — not beyond the limit sphere, and not left at the
   unrestricted apex.

   Board note: plan text said "subtask 65-b", but claimId 65-b is already
   GREEN as `round_endcap_is_forward_semicircle`.  This mitre-limit clip
   obligation is 65-d.

   GREEN.  The headline is stated (`miter_clipped_at_limit_distance_claim`)
   and CLOSED here (`miter_clipped_at_limit_distance`, Qed) — ray-scale
   algebra under the overshoot hypothesis.  Production home:
   `theories/BufferMiterClip.v`, same WITNESS tag, over corpus
   `BufferMiter.miter_apex` / `Segment.between`.

   Proof: with M = miter_apex, r = |M−V|, overshoot ⇒ (L·d)² < r² and
   L·d > 0 ⇒ 0 < L·d < r.  Clipped = V + ((L·d)/r)·(M−V) has
   |clipped−V| = L·d and is the segment point at parameter s = (L·d)/r ∈ (0,1).

   Rational witness pins (Qed at Red, kept): unit right-angle corner
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

(* Cramer's-rule unrestricted mitre apex — matches BufferMiter.miter_apex. *)
Definition miter_det (ein eout : Vec) : R :=
  vx ein * vy eout - vy ein * vx eout.

Definition miter_apex (V : Point) (ein eout : Vec) (d : R) : Point :=
  mkPoint
    (px V + d * (vmag ein * vx eout - vmag eout * vx ein) / miter_det ein eout)
    (py V + d * (vmag ein * vy eout - vmag eout * vy ein) / miter_det ein eout).

(* Limit-clipped join vertex: ray from V through the unrestricted apex,
   scaled to length L·d.  (Operational model of "clip at the mitre limit";
   when the unrestricted apex is already inside the limit sphere the emitter
   keeps it — Green may case-split on the overshoot hypothesis below.) *)
Definition limited_miter_apex (V : Point) (ein eout : Vec) (d L : R) : Point :=
  let M := miter_apex V ein eout d in
  let dx := px M - px V in
  let dy := py M - py V in
  let r := sqrt (dx * dx + dy * dy) in
  mkPoint (px V + (L * d) * dx / r) (py V + (L * d) * dy / r).

(* Q lies on the closed segment V—M (parametric). *)
Definition between (V M Q : Point) : Prop :=
  exists s : R, 0 <= s /\ s <= 1 /\
    px Q = (1 - s) * px V + s * px M /\
    py Q = (1 - s) * py V + s * py M.

(* -------------------------------------------------------------------------- *)
(* The 65-d claim (closed below by miter_clipped_at_limit_distance).          *)
(* When the unrestricted mitre apex overshoots the limit sphere of radius     *)
(* L·d about V, the emitted (clipped) join vertex is:                         *)
(*   (i)  at squared distance exactly (L·d)² from V, and                      *)
(*   (ii) on the segment V — unrestricted apex  (the clip segment).           *)
(* -------------------------------------------------------------------------- *)

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

(* GREEN: ray-scale identity under overshoot. *)
Lemma miter_clipped_at_limit_distance :
  miter_clipped_at_limit_distance_claim.
Proof.
  unfold miter_clipped_at_limit_distance_claim.
  intros V ein eout d L Hd HL _Hin _Hout _Hdet Hover.
  assert (HLd : 0 < L * d) by nra.
  set (M := miter_apex V ein eout d).
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
  assert (Hover' : (L * d) * (L * d) < r * r).
  { rewrite Hr2, <- Hdist. unfold M in Hover |- *. exact Hover. }
  assert (Hrpos : 0 < r).
  { assert (Hr0 : r <> 0).
    { intro Hz. rewrite Hz in Hover'. rewrite Rmult_0_l in Hover'. nra. }
    pose proof (sqrt_pos (dx * dx + dy * dy)) as Hge.
    change (0 <= r) in Hge. lra. }
  assert (Hr0 : r <> 0) by (apply Rgt_not_eq; exact Hrpos).
  assert (HLdr : L * d < r).
  { apply Rsqr_incrst_0; try nra.
    unfold Rsqr. nra. }
  set (s := (L * d) / r).
  assert (Hs0 : 0 < s).
  { unfold s, Rdiv. apply Rmult_lt_0_compat; [ exact HLd | ].
    apply Rinv_0_lt_compat. exact Hrpos. }
  assert (Hs1 : s < 1).
  { unfold s. apply (Rmult_lt_reg_r r); [ exact Hrpos | ].
    replace ((L * d) / r * r) with (L * d) by (field; exact Hr0).
    lra. }
  assert (Hs01 : 0 <= s <= 1) by lra.
  (* limited_miter_apex unfolds to V + (L·d)·(dx,dy)/r *)
  assert (Hlim :
    limited_miter_apex V ein eout d L =
    mkPoint (px V + (L * d) * dx / r) (py V + (L * d) * dy / r)).
  { unfold limited_miter_apex, M, dx, dy, r. reflexivity. }
  split.
  - (* dist_sq = (L·d)² ; dist_sq uses (V − Q) so signs flip twice *)
    rewrite Hlim. unfold dist_sq; simpl.
    set (a := L * d).
    replace (px V - (px V + a * dx / r)) with (- (a * dx / r))
      by (unfold a; ring).
    replace (py V - (py V + a * dy / r)) with (- (a * dy / r))
      by (unfold a; ring).
    replace ((- (a * dx / r)) * (- (a * dx / r))
             + (- (a * dy / r)) * (- (a * dy / r)))
      with ((a * dx / r) * (a * dx / r) + (a * dy / r) * (a * dy / r))
      by ring.
    transitivity (a * a * (dx * dx + dy * dy) / (r * r)).
    { field; exact Hr0. }
    rewrite <- Hr2. field; exact Hr0.
  - (* between V M clipped, parameter s = (L·d)/r *)
    rewrite Hlim. unfold between.
    exists s. repeat split; [ lra | lra | | ].
    + (* px clipped = (1−s)·px V + s·px M *)
      unfold s. fold dx.
      replace (px V + (L * d) * dx / r)
        with ((1 - (L * d) / r) * px V + ((L * d) / r) * px M).
      2: { unfold dx. field; exact Hr0. }
      reflexivity.
    + unfold s. fold dy.
      replace (py V + (L * d) * dy / r)
        with ((1 - (L * d) / r) * py V + ((L * d) / r) * py M).
      2: { unfold dy. field; exact Hr0. }
      reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Rational witness pins (Qed at Red; kept under Green).                      *)
(* Unit right-angle corner: V=(0,0), ein=(1,0), eout=(0,1), d=1, L=1.         *)
(* Unrestricted apex = (−1,1), dist_sq = 2 > 1 = (L·d)² — clip is active.     *)
(* -------------------------------------------------------------------------- *)

Definition w_V : Point := mkPoint 0 0.
Definition w_ein  : Vec := mkVec 1 0.
Definition w_eout : Vec := mkVec 0 1.
Definition w_d : R := 1.
Definition w_L : R := 1.

Definition w_apex : Point := miter_apex w_V w_ein w_eout w_d.
Definition w_clipped : Point := limited_miter_apex w_V w_ein w_eout w_d w_L.

Lemma w_d_pos : 0 < w_d.
Proof. unfold w_d. lra. Qed.

Lemma w_L_ge_1 : 1 <= w_L.
Proof. unfold w_L. lra. Qed.

Lemma w_ein_ne : w_ein <> vzero.
Proof. unfold w_ein, vzero. intros H. inversion H. lra. Qed.

Lemma w_eout_ne : w_eout <> vzero.
Proof. unfold w_eout, vzero. intros H. inversion H. lra. Qed.

Lemma w_det_ne : miter_det w_ein w_eout <> 0.
Proof. unfold miter_det, w_ein, w_eout; simpl. lra. Qed.

Lemma w_vmag_ein : vmag w_ein = 1.
Proof.
  unfold vmag, vmag_sq, w_ein; simpl.
  replace (1 * 1 + 0 * 0) with 1 by ring.
  exact sqrt_1.
Qed.

Lemma w_vmag_eout : vmag w_eout = 1.
Proof.
  unfold vmag, vmag_sq, w_eout; simpl.
  replace (0 * 0 + 1 * 1) with 1 by ring.
  exact sqrt_1.
Qed.

(* Unrestricted apex is exactly (−1, 1) — pure rational. *)
Lemma w_apex_eq : w_apex = mkPoint (-1) 1.
Proof.
  unfold w_apex, miter_apex, w_V, w_d.
  rewrite w_vmag_ein, w_vmag_eout.
  unfold w_ein, w_eout, miter_det; cbn [vx vy px py].
  f_equal; field.
Qed.

(* dist_sq(V, apex) = 2, strictly above (L·d)² = 1 — overshoot, clip active. *)
Lemma w_unlimited_dist_sq : dist_sq w_V w_apex = 2.
Proof.
  rewrite w_apex_eq. unfold dist_sq, w_V; simpl. lra.
Qed.

Lemma w_overshoots_limit :
  (w_L * w_d) * (w_L * w_d) < dist_sq w_V w_apex.
Proof.
  unfold w_L, w_d. rewrite w_unlimited_dist_sq. lra.
Qed.

(* Claim hypotheses all hold at the witness (so Green cannot dodge by
   vacuity on this corner). *)
Lemma w_claim_hyps :
  0 < w_d /\
  1 <= w_L /\
  w_ein <> vzero /\
  w_eout <> vzero /\
  miter_det w_ein w_eout <> 0 /\
  (w_L * w_d) * (w_L * w_d) < dist_sq w_V w_apex.
Proof.
  repeat split;
    [ exact w_d_pos | exact w_L_ge_1 | exact w_ein_ne
    | exact w_eout_ne | exact w_det_ne | exact w_overshoots_limit ].
Qed.

(* MISMATCH PROBE 1: the unrestricted apex is NOT at distance L·d —
   refutes "emit the raw miter_apex even when over limit". *)
Lemma w_probe_unlimited_not_at_limit :
  dist_sq w_V w_apex <> (w_L * w_d) * (w_L * w_d).
Proof.
  unfold w_L, w_d. rewrite w_unlimited_dist_sq. lra.
Qed.

(* MISMATCH PROBE 2: a point beyond the limit sphere on the same ray
   (scale factor 2 from V toward the apex direction) is also not the
   clip — refutes "any point on the mitre ray is fine". *)
Definition w_beyond : Point := mkPoint (-2) 2.

Lemma w_beyond_on_ray :
  between w_V w_beyond w_apex.
Proof.
  (* apex = (−1,1) = midpoint of V=(0,0) and beyond=(−2,2): s = 1/2 *)
  unfold between, w_V, w_beyond. rewrite w_apex_eq; simpl.
  exists (1 / 2). repeat split; lra.
Qed.

Lemma w_probe_beyond_not_at_limit :
  dist_sq w_V w_beyond <> (w_L * w_d) * (w_L * w_d).
Proof.
  unfold dist_sq, w_V, w_beyond, w_L, w_d; simpl. lra.
Qed.

(* Expected clip distance (the Green residual for this witness): L·d = 1.
   Stated as a named constant so the matcher / mutation suite can see the
   target squared length without closing the claim. *)
Lemma w_limit_radius_sq : (w_L * w_d) * (w_L * w_d) = 1.
Proof. unfold w_L, w_d. lra. Qed.
