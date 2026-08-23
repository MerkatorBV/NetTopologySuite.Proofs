(* ==========================================================================
   WalkCorners.v

   [H-bridge attack, C-3f discharge rung D-2] The PER-VERTEX CORNER
   THRESHOLD and the WALK THRESHOLD FOLD.

   The orbit chain consumes one fan corner per step at a PRESCRIBED
   delta (fixed globally by the premise's `ef` through
   `corner_delta_for_ef_*`), with the per-vertex rho free.  The
   explicit-parameter corner theorems (`fan_corner_connected_reflex`/
   `_convex`) demand six/eight smallness bounds against that vertex's
   clearance ball -- so what the discharge needs is not ONE parameter
   pair (the `_auto` wrappers' existential) but a THRESHOLD: all small
   deltas work, with rho tied linearly to delta.

     - `walk_corner_threshold`: under the same vertex-side hypotheses
       as `fan_corner_connected` (clearance, germ exclusions,
       nondegenerate gap), there are `t > 0` and `rho_factor > 0` such
       that for EVERY `0 < delta < t` the corner connects at
       `(rho_factor * delta, delta)`.  Reflex gaps take
       `rho_factor = 1`; convex gaps take
       `rho_factor = (C1 + C2 + 1) / gap`, which makes the far-wall
       smallness `delta * C_i < rho * gap` hold IDENTICALLY -- so the
       threshold only has to control the clearance-ball bounds, and
       everything scales linearly in delta.
     - `nat_threshold_fold`: finitely many positive per-step
       thresholds fold into one positive walk threshold (the
       nat-indexed analogue of `JCTWallClear.clear_fold`).

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
                               FanGapSector FanCorner.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Bound plumbing (triple products atomized for nra).                      *)
(* -------------------------------------------------------------------------- *)

Lemma scaled_bound_lt :
  forall (F delta ax ay M eps : R),
    0 <= F -> 0 < delta -> 1 <= M ->
    0 <= ax -> 0 <= ay -> ax <= M - 1 -> ay <= M - 1 ->
    delta * (2 * (F + 1) * M) < eps ->
    F * delta * ax + delta * ay < eps.
Proof.
  intros F delta ax ay M eps HF Hd HM Hax0 Hay0 Hax Hay Hkey.
  assert (H1 : F * delta * ax <= F * delta * (M - 1))
    by (apply Rmult_le_compat_l; nra).
  assert (H2 : delta * ay <= delta * (M - 1))
    by (apply Rmult_le_compat_l; nra).
  assert (H3 : 0 <= delta * (F + 1) * (M + 1))
    by (apply Rmult_le_pos; nra).
  nra.
Qed.

Lemma scaled_bound_single :
  forall (F delta ax M eps : R),
    0 <= F -> 0 < delta -> 1 <= M ->
    0 <= ax -> ax <= M - 1 ->
    delta * (2 * (F + 1) * M) < eps ->
    delta * ax < eps.
Proof.
  intros F delta ax M eps HF Hd HM Hax0 Hax Hkey.
  assert (H1 : delta * ax <= delta * (M - 1))
    by (apply Rmult_le_compat_l; lra).
  assert (H2 : 0 <= delta * (2 * F + 1)) by nra.
  assert (H3 : 0 <= delta * (2 * F + 1) * M)
    by (apply Rmult_le_pos; lra).
  nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The per-vertex corner threshold.                                        *)
(* -------------------------------------------------------------------------- *)

Theorem walk_corner_threshold :
  forall (r : Ring) (v a b : Point) (u1 u2 : Vec),
    no_horizontal_edges r ->
    (forall f, In f (ring_edges r) -> f <> (a, v) -> f <> (v, b) ->
       ~ on_edge f v) ->
    ~ in_open_sector u1 u2 (point_diff a v) ->
    ~ in_open_sector u1 u2 (point_diff b v) ->
    vcross u1 u2 <> 0 ->
    exists t rho_factor : R,
      0 < t /\ 0 < rho_factor /\
      forall delta, 0 < delta < t ->
        connected_in_complement_cont r
          (point_at v (corner_sample_in u1 (rho_factor * delta) delta))
          (point_at v (corner_sample_out u2 (rho_factor * delta) delta)).
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
  destruct (Rdichotomy _ _ Hcne) as [Hneg | Hgt].
  - (* REFLEX gap: rho_factor = 1, sigma := delta *)
    exists (eps / (2 * (1 + 1) * M)), 1.
    assert (Ht : 0 < eps / (2 * (1 + 1) * M))
      by (apply Rdiv_lt_0_compat; lra).
    split; [ exact Ht | split; [ lra | ] ].
    intros delta Hd.
    assert (Hkey : delta * (2 * (1 + 1) * M) < eps).
    { apply Rmult_lt_reg_r with (/ (2 * (1 + 1) * M));
        [ apply Rinv_0_lt_compat; lra | ].
      unfold Rdiv in Hd.
      replace (delta * (2 * (1 + 1) * M) * / (2 * (1 + 1) * M))
        with delta by (field; lra).
      lra. }
    apply (fan_corner_connected_reflex r v a b u1 u2 eps
             (1 * delta) delta delta Hball Hma Hmb Hneg);
      try lra;
      try (apply (scaled_bound_lt 1 delta _ _ M eps);
           solve [ lra | apply Rabs_pos | assumption ]);
      try (apply (scaled_bound_single 1 delta _ M eps);
           solve [ lra | apply Rabs_pos | assumption ]).
  - (* CONVEX gap: rho_factor makes the far-wall smallness identical *)
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
    exists (eps / (2 * (F + 1) * M)), F.
    assert (Ht : 0 < eps / (2 * (F + 1) * M))
      by (apply Rdiv_lt_0_compat; nra).
    split; [ exact Ht | split; [ exact HF | ] ].
    intros delta Hd.
    assert (Hkey : delta * (2 * (F + 1) * M) < eps).
    { apply Rmult_lt_reg_r with (/ (2 * (F + 1) * M));
        [ apply Rinv_0_lt_compat; nra | ].
      unfold Rdiv in Hd.
      replace (delta * (2 * (F + 1) * M) * / (2 * (F + 1) * M))
        with delta by (field; nra).
      lra. }
    apply (fan_corner_connected_convex r v a b u1 u2 eps
             (F * delta) delta Hball Hma Hmb Hpos);
      try nra;
      try (apply (scaled_bound_lt F delta _ _ M eps);
           solve [ lra | apply Rabs_pos | assumption ]).
    + (* delta * C1 < rho * gap = delta * (C1 + C2 + 1) *)
      fold C1.
      assert (Hrg : F * delta * vcross u1 u2 = delta * (C1 + C2 + 1))
        by nra.
      nra.
    + fold C2.
      assert (Hrg : F * delta * vcross u1 u2 = delta * (C1 + C2 + 1))
        by nra.
      nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Folding the per-step thresholds into one walk threshold.                *)
(* -------------------------------------------------------------------------- *)

Lemma nat_threshold_fold :
  forall (k : nat) (t : nat -> R),
    (forall i, (i < k)%nat -> 0 < t i) ->
    exists t0, 0 < t0 /\ forall i, (i < k)%nat -> t0 <= t i.
Proof.
  induction k as [| k IH]; intros t Hall.
  - exists 1. split; [ lra | intros i Hi; lia ].
  - destruct (IH t (fun i Hi => Hall i (Nat.lt_lt_succ_r _ _ Hi)))
      as [t0 [Ht0 Hb]].
    exists (Rmin t0 (t k)).
    split.
    + apply Rmin_glb_lt; [ exact Ht0 | apply Hall; lia ].
    + intros i Hi.
      destruct (Nat.lt_ge_cases i k) as [Hik | Hik].
      * eapply Rle_trans; [ apply Rmin_l | exact (Hb i Hik) ].
      * assert (Hieq : i = k) by lia. subst i.
        apply Rmin_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Threshold arithmetic; allowlist axioms only.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions walk_corner_threshold.
Print Assumptions nat_threshold_fold.
