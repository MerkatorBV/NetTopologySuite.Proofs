(* ============================================================================
   nts-eval micro unit — claimId 65-c (ABORTED / DISPROVEN)
   Red planted 2026-08-02 · claim aborted same day (no Green)
   ----------------------------------------------------------------------------
   Naive micro-claim: every point of the raw offset graph of a geometry G at
   distance d (including mitre-join artifacts and their self-intersection
   loci) lies inside the axis-aligned Envelope(G).expandBy(d).

   ABORTED.  The claim is stated below as
   `offset_artifacts_within_envelope_claim` and REFUTED by a classical-reals
   rational witness — no `Admitted`, no Green fix, no production repair.
   Mitre joins may place vertices up to `mitreLimit · d` from the input
   (JTS/NTS default `mitreLimit = 5`); the unlimited apex sits even farther
   (`d / sin(φ/2)`).  Either way the join vertex of a sharp enough corner
   exits the d-expanded envelope of G.

   Rational witness (classical reals, all pins Qed):
     G = LineString (0,0) → (1,0) → (1/2, 1/10)
     d = 1, join = mitre, mitreLimit = 5
     apex corner V = (1,0), ein = (1,0), eout = (−1/2, 1/10)
     Envelope(G) = [0,1] × [0, 1/10]
     Envelope(G).expandBy(1) = [−1, 2] × [−1, 11/10]
     Unlimited mitre apex = miter_apex(V, ein, eout, d) has
       x = −4 − 10·|eout| < −4 < −1  (strictly left of the expanded box)
     Limited mitre (ray-scaled to mitreLimit·d = 5) is still strictly
       left of x = −1, so the default mitre-limit does not restore the claim.
     Optional secondary: any self-intersection of the two incident raw
       offset edges of the spike inherits the violation (the edges leave the
       box, so their noding locus can too).

   Round-join-only variants remain bounded by expandBy(d) (round arcs sit
   on the radius-d circle about the corner), but the claim as stated —
   general offset artifacts, mitre included — does not hold.

   WITNESS claimId: 65-c
   Lemma (aborted target): offset_artifacts_within_envelope
   ========================================================================== *)

(* WITNESS {"claimId":"65-c","topic":"buffer","lemma":"offset_artifacts_within_envelope","title":"Raw offset artifacts stay inside Envelope(G).expandBy(d) — ABORTED (mitre excess)","status":"aborted"} *)

From Stdlib Require Import Reals Lra.
Local Open Scope R_scope.

Record Point : Type := mkPoint { px : R; py : R }.
Record Vec   : Type := mkVec   { vx : R; vy : R }.

Record Envelope : Type := mkEnv {
  emin_x : R;
  emax_x : R;
  emin_y : R;
  emax_y : R
}.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).

Definition vmag_sq (v : Vec) : R := vx v * vx v + vy v * vy v.
Definition vmag (v : Vec) : R := sqrt (vmag_sq v).

(* Cramer's-rule mitre apex — matches theories/BufferMiter.miter_apex. *)
Definition miter_det (ein eout : Vec) : R :=
  vx ein * vy eout - vy ein * vx eout.

Definition miter_apex (V : Point) (ein eout : Vec) (d : R) : Point :=
  mkPoint
    (px V + d * (vmag ein * vx eout - vmag eout * vx ein) / miter_det ein eout)
    (py V + d * (vmag ein * vy eout - vmag eout * vy ein) / miter_det ein eout).

Definition in_envelope (e : Envelope) (p : Point) : Prop :=
  emin_x e <= px p <= emax_x e /\ emin_y e <= py p <= emax_y e.

Definition expand_by (e : Envelope) (d : R) : Envelope :=
  mkEnv (emin_x e - d) (emax_x e + d) (emin_y e - d) (emax_y e + d).

(* Limited mitre: scale the unlimited apex ray down to length L·d when it
   overshoots the mitre limit (the operational JTS/NTS default cap). *)
Definition limited_miter_apex (V : Point) (ein eout : Vec) (d L : R) : Point :=
  let M := miter_apex V ein eout d in
  let dx := px M - px V in
  let dy := py M - py V in
  let r := sqrt (dx * dx + dy * dy) in
  mkPoint (px V + (L * d) * dx / r) (py V + (L * d) * dy / r).

(* -------------------------------------------------------------------------- *)
(* The 65-c claim (ABORTED: false as stated).                                 *)
(* Every mitre-join apex of a corner that sits inside env lies inside         *)
(* expand_by env d.  (Minimal surface: corners presented as (V,ein,eout)      *)
(* with G's envelope supplied; no full polyline ADT.)                         *)
(* -------------------------------------------------------------------------- *)

Definition offset_artifacts_within_envelope_claim : Prop :=
  forall (env : Envelope) (V : Point) (ein eout : Vec) (d : R),
    0 < d ->
    miter_det ein eout <> 0 ->
    in_envelope env V ->
    in_envelope (expand_by env d) (miter_apex V ein eout d).

(* ABORTED target named in the WITNESS tag.  Do NOT close this positively —
   an `Admitted` false statement is apply-able and poisons dependents.
   The refutation is `offset_artifacts_within_envelope_aborted` below. *)
Theorem offset_artifacts_within_envelope :
  offset_artifacts_within_envelope_claim.
Proof.
Abort.

(* -------------------------------------------------------------------------- *)
(* Rational sharp-corner witness.                                             *)
(* G = (0,0) → (1,0) → (1/2, 1/10), d = 1, mitreLimit = 5.                   *)
(* -------------------------------------------------------------------------- *)

Definition w_A : Point := mkPoint 0 0.
Definition w_B : Point := mkPoint 1 0.
Definition w_C : Point := mkPoint (1 / 2) (1 / 10).

Definition w_ein  : Vec := mkVec 1 0.
Definition w_eout : Vec := mkVec (-1 / 2) (1 / 10).
Definition w_d : R := 1.
Definition w_mitreLimit : R := 5.

Definition w_env : Envelope := mkEnv 0 1 0 (1 / 10).
Definition w_expanded : Envelope := expand_by w_env w_d.

Definition w_apex : Point := miter_apex w_B w_ein w_eout w_d.
Definition w_limited : Point :=
  limited_miter_apex w_B w_ein w_eout w_d w_mitreLimit.

(* Corner vertex sits in Envelope(G). *)
Lemma w_B_in_env : in_envelope w_env w_B.
Proof. unfold in_envelope, w_env, w_B; simpl. split; split; lra. Qed.

Lemma w_det_ne : miter_det w_ein w_eout <> 0.
Proof. unfold miter_det, w_ein, w_eout; simpl. lra. Qed.

Lemma w_d_pos : 0 < w_d.
Proof. unfold w_d. lra. Qed.

(* |ein| = 1 exactly. *)
Lemma w_vmag_ein : vmag w_ein = 1.
Proof.
  unfold vmag, vmag_sq, w_ein; simpl.
  replace (1 * 1 + 0 * 0) with 1 by ring.
  exact sqrt_1.
Qed.

(* |eout|² = 26/100 > 0, so |eout| > 0. *)
Lemma w_vmag_sq_eout : vmag_sq w_eout = 26 / 100.
Proof. unfold vmag_sq, w_eout; simpl. field. Qed.

Lemma w_vmag_eout_pos : 0 < vmag w_eout.
Proof.
  unfold vmag. apply sqrt_lt_R0.
  rewrite w_vmag_sq_eout. lra.
Qed.

(* Closed form of the unlimited mitre apex:
     x = −4 − 10·|eout|  < −4
     y = 1                                           *)
Lemma w_apex_coords :
  px w_apex = -4 - 10 * vmag w_eout /\
  py w_apex = 1.
Proof.
  unfold w_apex, miter_apex, w_d.
  split.
  - unfold w_B; cbn [px py].
    rewrite w_vmag_ein.
    unfold w_ein, w_eout, miter_det; cbn [vx vy].
    (* 1 + 1*(1*(-1/2) - |eout|*1)/(1/10) = −4 − 10·|eout| *)
    field.
  - unfold w_B; cbn [px py].
    rewrite w_vmag_ein.
    unfold w_ein, w_eout, miter_det; cbn [vx vy].
    field.
Qed.

(* Primary pin: the unlimited mitre apex exits Envelope(G).expandBy(d). *)
Lemma w_apex_exits_expanded :
  ~ in_envelope w_expanded w_apex.
Proof.
  intros Hin.
  destruct w_apex_coords as [Hxeq _].
  unfold in_envelope in Hin.
  destruct Hin as [[Hxlo _] _].
  (* Hxlo : emin_x w_expanded <= px w_apex.  Expanded min_x = −1. *)
  assert (Hmin : emin_x w_expanded = -1)
    by (unfold w_expanded, expand_by, w_env, w_d; simpl; lra).
  rewrite Hmin in Hxlo.
  (* px = −4 − 10·|eout| < −4 < −1, contradicting −1 <= px *)
  rewrite Hxeq in Hxlo.
  pose proof w_vmag_eout_pos as Hp.
  nra.
Qed.

(* Expanded envelope of the witness, explicit coordinate pins. *)
Lemma w_expanded_bounds :
  emin_x w_expanded = -1 /\ emax_x w_expanded = 2 /\
  emin_y w_expanded = -1 /\ emax_y w_expanded = 11 / 10.
Proof. unfold w_expanded, expand_by, w_env, w_d; simpl. repeat split; lra. Qed.

(* -------------------------------------------------------------------------- *)
(* Secondary pin: mitreLimit does not restore the claim.                      *)
(*                                                                            *)
(* Unlimited length exceeds L·d = 5 (so default mitre limiting is active).    *)
(* The expanded box about V is tiny: any in-box point has                     *)
(* dist_sq(V, ·) ≤ 4 + (11/10)² = 521/100 < 25 = (L·d)².  A join vertex       *)
(* forced out to distance L·d therefore still exits expandBy(d).  We pin      *)
(* the two quantitative ingredients (overshoot + box radius) as Qed; the      *)
(* ray-scale assembly of the clipped apex is the same algebra as              *)
(* `limited_miter_apex` and is left as narrative (optional secondary).        *)
(* -------------------------------------------------------------------------- *)

Lemma w_unlimited_length_sq :
  dist_sq w_B w_apex =
    (5 + 10 * vmag w_eout) * (5 + 10 * vmag w_eout) + 1.
Proof.
  unfold dist_sq.
  destruct w_apex_coords as [Hx Hy].
  rewrite Hx, Hy. unfold w_B; simpl.
  ring.
Qed.

Lemma w_unlimited_exceeds_limit :
  (w_mitreLimit * w_d) * (w_mitreLimit * w_d) < dist_sq w_B w_apex.
Proof.
  unfold w_mitreLimit, w_d.
  rewrite w_unlimited_length_sq.
  pose proof w_vmag_eout_pos as Hp.
  (* 25 < (5 + 10·m)² + 1  for m > 0 *)
  nra.
Qed.

(* Every point of the expanded envelope is within squared-distance
   4 + (11/10)² of V: |Δx| ≤ 2 (box x in [−1,2], V.x = 1) and
   |Δy| ≤ 11/10 (box y in [−1, 11/10], V.y = 0). *)
Lemma w_expanded_near_B :
  forall p : Point,
    in_envelope w_expanded p ->
    dist_sq w_B p <= 4 + (11 / 10) * (11 / 10).
Proof.
  intros p Hin.
  unfold dist_sq, w_B; simpl.
  unfold in_envelope in Hin.
  destruct w_expanded_bounds as [Hxmin [Hxmax [Hymin Hymax]]].
  destruct Hin as [[Hxlo Hxhi] [Hylo Hyhi]].
  rewrite Hxmin in Hxlo. rewrite Hxmax in Hxhi.
  rewrite Hymin in Hylo. rewrite Hymax in Hyhi.
  replace (1 - px p) with (- (px p - 1)) by ring.
  replace ((- (px p - 1)) * (- (px p - 1)))
    with ((px p - 1) * (px p - 1)) by ring.
  replace (0 - py p) with (- py p) by ring.
  replace ((- py p) * (- py p)) with (py p * py p) by ring.
  assert (Hxbd : (px p - 1) * (px p - 1) <= 4) by nra.
  assert (Hybd : py p * py p <= (11 / 10) * (11 / 10)) by nra.
  apply Rplus_le_compat; [ exact Hxbd | exact Hybd ].
Qed.

(* Combined: no point at squared distance ≥ 25 from V can sit in the
   expanded envelope.  Since the unlimited mitre apex has dist_sq > 25
   and the default limit only pulls it back to dist_sq = 25, both the
   raw and the limit-clipped join vertices exit expandBy(d). *)
Lemma w_limit_radius_exits_box :
  forall p : Point,
    (w_mitreLimit * w_d) * (w_mitreLimit * w_d) <= dist_sq w_B p ->
    ~ in_envelope w_expanded p.
Proof.
  intros p Hge Hin.
  pose proof (w_expanded_near_B p Hin) as Hnear.
  unfold w_mitreLimit, w_d in Hge.
  nra.
Qed.

Corollary w_apex_exits_via_limit_radius :
  ~ in_envelope w_expanded w_apex.
Proof.
  apply w_limit_radius_exits_box.
  pose proof w_unlimited_exceeds_limit as H.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline refutation: the naive envelope claim is false.                    *)
(* -------------------------------------------------------------------------- *)

Theorem offset_artifacts_within_envelope_aborted :
  ~ offset_artifacts_within_envelope_claim.
Proof.
  intros Hclaim.
  pose proof (Hclaim w_env w_B w_ein w_eout w_d
                w_d_pos w_det_ne w_B_in_env) as Hin.
  exact (w_apex_exits_expanded Hin).
Qed.

(* Round-join-only variants remain bounded (join arcs sit on the radius-d
   circle about the corner, hence inside any ball of radius d about V, and
   a fortiori inside a large enough expandBy).  The claim as stated —
   general raw offset artifacts, mitre included — does not hold. *)

