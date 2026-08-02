(* ============================================================================
   nts-eval micro unit — claimId 65-d (RED)
   Red planted 2026-08-02 · Green pending
   ----------------------------------------------------------------------------
   When a mitre join's unrestricted apex length exceeds the configured
   mitre limit L·d (L ≥ 1, d > 0), the emitted join vertex is the
   LIMIT-CLIPPED point on the mitre ray: it lies on the segment from the
   corner V through the unrestricted miter_apex, at Euclidean distance
   exactly L·d from V — not beyond the limit sphere, and not left at the
   unrestricted apex.

   Board note: the plan text called this "subtask 65-b", but claimId 65-b
   is already GREEN as `round_endcap_is_forward_semicircle` (Claim65b.v).
   This mitre-limit clip obligation is therefore planted as 65-d.

   RED SURFACE.  The headline is STATED below
   (`miter_clipped_at_limit_distance_claim`) and deliberately NOT proved —
   no `Admitted`, no `Axiom`; the claim is a named `Definition ... : Prop`,
   so the Eval → Qed matcher finds no Qed of this statement here or in
   production and reports 65-d red.  Green target:
     Lemma miter_clipped_at_limit_distance :
       miter_clipped_at_limit_distance_claim.
   Production home suggested: theories/BufferMiter.v neighbourhood (next to
   `miter_within_limit_iff` / `BufferMiterAngle.miter_cap_iff_sin_half`),
   same WITNESS tag.  The algebraic ray-scale identity is short; the Green
   content is packaging it as the emitted-join contract under the overshoot
   hypothesis (and optionally bridging to JTS bevel-vs-limited-miter policy).

   What IS Qed here: rational witness pins for the unit right-angle corner
   (exact Q coordinates, no trig residual):
     V = (0,0), ein = (1,0), eout = (0,1), d = 1, L = 1
     unrestricted apex = (−1, 1), dist_sq = 2 > 1 = (L·d)²  (overshoot)
     so the clip is active; the claimed clipped distance is L·d = 1.
   Mismatch probes: the unrestricted apex is NOT at distance L·d; a point
   beyond the limit sphere on the same ray is also rejected.

   Neighbouring #65 surface: `BufferMiter.miter_apex` / `miter_within_limit_iff`
   (decision only — does not yet emit the clipped vertex).  Claim 65-c
   (aborted) showed raw mitre artifacts can exit expandBy(d); this claim
   is the positive clip-at-limit obligation for the join emitter.

   WITNESS claimId: 65-d
   Lemma (Green target): miter_clipped_at_limit_distance
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
(* The 65-d claim (RED: stated, not closed).                                  *)
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

(* RED: no proof of the claim in this unit or in production.  Green must Qed
   `miter_clipped_at_limit_distance` with this statement (micro-kernel) and
   its production mirror next to BufferMiter.miter_within_limit_iff. *)

(* -------------------------------------------------------------------------- *)
(* Rational witness pins (Qed at Red).                                        *)
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
