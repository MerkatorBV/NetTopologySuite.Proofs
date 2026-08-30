(* ============================================================================
   NetTopologySuite.Proofs.BernsteinBasis
   ----------------------------------------------------------------------------
   Issue #562 / claimId 508-f: one Bernstein / rational framework for the
   Bézier and NURBS length lanes.

   Three files used to carry parallel copies of the same plumbing
   (Bezier3Length.v, NurbsQuadraticLength.v, NurbsGeneralLength.v).
   This module owns:

     - bern n i t via the de Casteljau recurrence
     - partition of unity (sum_f_R0) and non-negativity on [0,1]
     - closed-form aliases bern2_* / bern3_* (unfold-compatible)
     - degree-elevation control remap elevate_ctrl, instantiated at
       n = 2 (the cubic-for-quadratic storage convention)
     - divided-difference vector bounds (scaled_diff_norm,
       norm_pair_le, norm_triple_le, chord_le_of_combo3)
     - the cubic cofactors bezier3_c0/c1/c2
     - rational denominator floor bern2_weighted_den_lb

   Lane files re-base on these names. Public statement set does not
   shrink — compatibility Definitions keep the old identifiers.

   No `Admitted`, no `Axiom`, no `Parameter`.  3-axiom.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia Arith.
From NTS.Proofs Require Import Distance.
Local Open Scope R_scope.

(* Flocq 4.2.1 [nra] cannot find a witness on the cubic / mixed
   products below (CI death on 48a5c3f, L195). Pin with
   [Rmult_le_pos] / [Rplus_le_le_0_compat] / [lra] / [ring] —
   same class as SpeedIntegral. Do not reintroduce [nra] here. *)

(* -------------------------------------------------------------------------- *)
(* Bernstein basis: de Casteljau recurrence.                                  *)
(* -------------------------------------------------------------------------- *)

Fixpoint bern (n i : nat) (t : R) : R :=
  match n with
  | O => match i with O => 1 | _ => 0 end
  | S n' =>
      (1 - t) * bern n' i t
      + t * match i with O => 0 | S i' => bern n' i' t end
  end.

Lemma bern_gt : forall n i t,
  (n < i)%nat -> bern n i t = 0.
Proof.
  induction n as [|n IH]; intros i t Hlt.
  - destruct i as [|i']; [lia | simpl; reflexivity].
  - simpl.
    rewrite (IH i t) by lia.
    destruct i as [|i']; [lia |].
    rewrite (IH i' t) by lia.
    ring.
Qed.

Lemma bern_nonneg : forall n i t,
  0 <= t -> t <= 1 -> 0 <= bern n i t.
Proof.
  induction n as [|n IH]; intros i t Ht0 Ht1.
  - destruct i as [|i']; simpl; lra.
  - simpl.
    pose proof (IH i t Ht0 Ht1) as Hi.
    assert (Hprev : 0 <= match i with O => 0 | S i' => bern n i' t end).
    { destruct i as [|i']; [lra | apply IH; assumption]. }
    assert (H1t : 0 <= 1 - t) by lra.
    apply Rplus_le_le_0_compat.
    - apply Rmult_le_pos; [exact H1t | exact Hi].
    - apply Rmult_le_pos; [exact Ht0 | exact Hprev].
Qed.

Lemma sum_f_R0_0 : forall f, sum_f_R0 f 0 = f 0%nat.
Proof.
  intros f. reflexivity.
Qed.

Lemma sum_f_R0_S : forall f n,
  sum_f_R0 f (S n) = sum_f_R0 f n + f (S n).
Proof.
  intros f n. simpl. ring.
Qed.

Lemma bern_Sn : forall n i t,
  bern (S n) i t
  = (1 - t) * bern n i t
    + t * match i with O => 0 | S i' => bern n i' t end.
Proof.
  intros n i t. simpl. reflexivity.
Qed.

(* sum_{i=0}^{S m} prev_i = sum_{k=0}^{m} bern n k, where prev 0 = 0
   and prev (S k) = bern n k. Do not rewrite a reflexivity lemma —
   Rocq 9.2 rejects a rewrite that leaves the goal unchanged. *)
Lemma sum_f_R0_prev_bern : forall n m t,
  sum_f_R0 (fun i => match i with O => 0 | S i' => bern n i' t end) (S m)
  = sum_f_R0 (fun i => bern n i t) m.
Proof.
  intros n m t. induction m as [|m IH].
  - rewrite sum_f_R0_S. simpl. ring.
  - rewrite (sum_f_R0_S (fun i => match i with O => 0 | S i' => bern n i' t end) (S m)).
    rewrite IH.
    rewrite (sum_f_R0_S (fun i => bern n i t) m).
    apply f_equal. reflexivity.
Qed.

Lemma bern_Sn_sum_upto : forall n k t,
  sum_f_R0 (fun i => bern (S n) i t) k
  = (1 - t) * sum_f_R0 (fun i => bern n i t) k
    + t * sum_f_R0 (fun i => match i with O => 0 | S i' => bern n i' t end) k.
Proof.
  intros n k t. induction k as [|k IH].
  - rewrite (sum_f_R0_0 (fun i => bern (S n) i t)).
    rewrite (sum_f_R0_0 (fun i => bern n i t)).
    rewrite (sum_f_R0_0 (fun i => match i with O => 0 | S i' => bern n i' t end)).
    rewrite (bern_Sn n 0%nat t).
    ring.
  - rewrite (sum_f_R0_S (fun i => bern (S n) i t) k).
    rewrite (bern_Sn n (S k) t).
    rewrite IH.
    rewrite (sum_f_R0_S (fun i => bern n i t) k).
    rewrite (sum_f_R0_S (fun i => match i with O => 0 | S i' => bern n i' t end) k).
    ring.
Qed.

(* WITNESS {"claimId":"508-f-bern-partition","topic":"metric","lemma":"bern_partition","title":"Bernstein basis of degree n is a partition of unity","file":"theories/BernsteinBasis.v","witness":"508-f-bernstein","board":"#562"} *)

Theorem bern_partition : forall n t,
  sum_f_R0 (fun i => bern n i t) n = 1.
Proof.
  induction n as [|n IH]; intro t.
  - simpl. reflexivity.
  - rewrite bern_Sn_sum_upto.
    rewrite (sum_f_R0_S (fun i => bern n i t) n).
    rewrite IH.
    rewrite (bern_gt n (S n) t) by lia.
    rewrite (sum_f_R0_prev_bern n n t).
    rewrite IH.
    ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Closed-form aliases — unfold-compatible with the lane files.               *)
(* -------------------------------------------------------------------------- *)

Definition bern2_0 (t : R) : R := (1 - t) * (1 - t).
Definition bern2_1 (t : R) : R := 2 * (t * (1 - t)).
Definition bern2_2 (t : R) : R := t * t.

Definition bern3_0 (t : R) : R := (1 - t) * (1 - t) * (1 - t).
Definition bern3_1 (t : R) : R := 3 * (t * ((1 - t) * (1 - t))).
Definition bern3_2 (t : R) : R := 3 * ((t * t) * (1 - t)).
Definition bern3_3 (t : R) : R := t * t * t.

Lemma bern2_0_bern : forall t, bern2_0 t = bern 2 0 t.
Proof. intros t. unfold bern2_0. simpl. ring. Qed.
Lemma bern2_1_bern : forall t, bern2_1 t = bern 2 1 t.
Proof. intros t. unfold bern2_1. simpl. ring. Qed.
Lemma bern2_2_bern : forall t, bern2_2 t = bern 2 2 t.
Proof. intros t. unfold bern2_2. simpl. ring. Qed.

Lemma bern3_0_bern : forall t, bern3_0 t = bern 3 0 t.
Proof. intros t. unfold bern3_0. simpl. ring. Qed.
Lemma bern3_1_bern : forall t, bern3_1 t = bern 3 1 t.
Proof. intros t. unfold bern3_1. simpl. ring. Qed.
Lemma bern3_2_bern : forall t, bern3_2 t = bern 3 2 t.
Proof. intros t. unfold bern3_2. simpl. ring. Qed.
Lemma bern3_3_bern : forall t, bern3_3 t = bern 3 3 t.
Proof. intros t. unfold bern3_3. simpl. ring. Qed.

Lemma bern2_partition : forall t,
  bern2_0 t + bern2_1 t + bern2_2 t = 1.
Proof.
  intros t. unfold bern2_0, bern2_1, bern2_2. ring.
Qed.

Lemma bern3_partition : forall t,
  bern3_0 t + bern3_1 t + bern3_2 t + bern3_3 t = 1.
Proof.
  intros t. unfold bern3_0, bern3_1, bern3_2, bern3_3. ring.
Qed.

Lemma bern2_nonneg : forall t,
  0 <= t -> t <= 1 ->
  0 <= bern2_0 t /\ 0 <= bern2_1 t /\ 0 <= bern2_2 t.
Proof.
  intros t Ht0 Ht1. unfold bern2_0, bern2_1, bern2_2.
  assert (H1t : 0 <= 1 - t) by lra.
  split; [| split].
  - apply Rmult_le_pos; [exact H1t | exact H1t].
  - apply Rmult_le_pos.
    + lra.
    + apply Rmult_le_pos; [exact Ht0 | exact H1t].
  - apply Rmult_le_pos; [exact Ht0 | exact Ht0].
Qed.

Lemma bern3_nonneg : forall t,
  0 <= t -> t <= 1 ->
  0 <= bern3_0 t /\ 0 <= bern3_1 t /\ 0 <= bern3_2 t /\ 0 <= bern3_3 t.
Proof.
  intros t Ht0 Ht1. unfold bern3_0, bern3_1, bern3_2, bern3_3.
  assert (H1t : 0 <= 1 - t) by lra.
  assert (H3 : 0 <= 3) by lra.
  repeat split.
  - apply Rmult_le_pos; [apply Rmult_le_pos; [exact H1t | exact H1t] | exact H1t].
  - apply Rmult_le_pos.
    + exact H3.
    + apply Rmult_le_pos.
      * exact Ht0.
      * apply Rmult_le_pos; [exact H1t | exact H1t].
  - apply Rmult_le_pos.
    + exact H3.
    + apply Rmult_le_pos.
      * apply Rmult_le_pos; [exact Ht0 | exact Ht0].
      * exact H1t.
  - apply Rmult_le_pos; [apply Rmult_le_pos; [exact Ht0 | exact Ht0] | exact Ht0].
Qed.

(* -------------------------------------------------------------------------- *)
(* Degree elevation: P'_0 = P_0, P'_{n+1} = P_n,                              *)
(* P'_i = (i/(n+1)) P_{i-1} + ((n+1-i)/(n+1)) P_i.                            *)
(* -------------------------------------------------------------------------- *)

Definition elevate_ctrl (n : nat) (P : nat -> R) (i : nat) : R :=
  match i with
  | O => P O
  | S i' =>
      if Nat.eq_dec i (S n)
      then P n
      else (INR i / INR (S n)) * P i'
           + (INR (S n - i) / INR (S n)) * P i
  end.

Lemma S_INR_neq_0 : forall n, INR (S n) <> 0.
Proof.
  intros n. apply not_0_INR. lia.
Qed.

(* WITNESS {"claimId":"508-f-elevate-2","topic":"metric","lemma":"bern_elevate_2","title":"Degree elevation n=2 is exact on coordinates: elevated cubic Bernstein combo equals the quadratic","file":"theories/BernsteinBasis.v","witness":"508-f-bernstein","board":"#562"} *)

Lemma elevate_ctrl_2_0 : forall P, elevate_ctrl 2 P 0%nat = P 0%nat.
Proof. intros P. unfold elevate_ctrl. reflexivity. Qed.

Lemma elevate_ctrl_2_3 : forall P, elevate_ctrl 2 P 3%nat = P 2%nat.
Proof.
  intros P. unfold elevate_ctrl.
  destruct (Nat.eq_dec 3 3) as [E|E]; [reflexivity | lia].
Qed.

Lemma elevate_ctrl_2_1 : forall P,
  elevate_ctrl 2 P 1%nat
  = (INR 1 / INR 3) * P 0%nat + (INR 2 / INR 3) * P 1%nat.
Proof.
  intros P. unfold elevate_ctrl.
  destruct (Nat.eq_dec 1 3) as [E|E]; [lia |].
  simpl. field. apply (S_INR_neq_0 2).
Qed.

Lemma elevate_ctrl_2_2 : forall P,
  elevate_ctrl 2 P 2%nat
  = (INR 2 / INR 3) * P 1%nat + (INR 1 / INR 3) * P 2%nat.
Proof.
  intros P. unfold elevate_ctrl.
  destruct (Nat.eq_dec 2 3) as [E|E]; [lia |].
  simpl. field. apply (S_INR_neq_0 2).
Qed.

Theorem bern_elevate_2 : forall (P : nat -> R) t,
  bern2_0 t * P 0%nat + bern2_1 t * P 1%nat + bern2_2 t * P 2%nat
  =
  bern3_0 t * elevate_ctrl 2 P 0%nat
  + bern3_1 t * elevate_ctrl 2 P 1%nat
  + bern3_2 t * elevate_ctrl 2 P 2%nat
  + bern3_3 t * elevate_ctrl 2 P 3%nat.
Proof.
  intros P t.
  rewrite elevate_ctrl_2_0, elevate_ctrl_2_1, elevate_ctrl_2_2, elevate_ctrl_2_3.
  unfold bern2_0, bern2_1, bern2_2, bern3_0, bern3_1, bern3_2, bern3_3.
  field.
  apply (S_INR_neq_0 2).
Qed.

(* -------------------------------------------------------------------------- *)
(* Divided-difference vector bounds.                                          *)
(* -------------------------------------------------------------------------- *)

Lemma scaled_diff_norm : forall c x y,
  0 <= c ->
  sqrt ((c * x) * (c * x) + (c * y) * (c * y)) = c * sqrt (x * x + y * y).
Proof.
  intros c x y Hc.
  replace ((c * x) * (c * x) + (c * y) * (c * y))
    with ((c * c) * (x * x + y * y)) by ring.
  rewrite sqrt_mult;
    [| pose proof (sqr_nonneg c); lra
     | pose proof (sqr_nonneg x); pose proof (sqr_nonneg y); lra].
  replace (c * c) with (Rsqr c) by (unfold Rsqr; ring).
  rewrite sqrt_Rsqr by exact Hc.
  reflexivity.
Qed.

Lemma norm_triple_le : forall c0 c1 c2 x0 y0 x1 y1 x2 y2,
  0 <= c0 -> 0 <= c1 -> 0 <= c2 ->
  sqrt ((c0 * x0 + c1 * x1 + c2 * x2) * (c0 * x0 + c1 * x1 + c2 * x2)
        + (c0 * y0 + c1 * y1 + c2 * y2) * (c0 * y0 + c1 * y1 + c2 * y2))
  <= c0 * sqrt (x0 * x0 + y0 * y0) + c1 * sqrt (x1 * x1 + y1 * y1)
     + c2 * sqrt (x2 * x2 + y2 * y2).
Proof.
  intros c0 c1 c2 x0 y0 x1 y1 x2 y2 Hc0 Hc1 Hc2.
  set (A0 := mkPoint 0 0).
  set (A1 := mkPoint (c0 * x0) (c0 * y0)).
  set (A2 := mkPoint (c0 * x0 + c1 * x1) (c0 * y0 + c1 * y1)).
  set (A3 := mkPoint (c0 * x0 + c1 * x1 + c2 * x2)
                     (c0 * y0 + c1 * y1 + c2 * y2)).
  assert (Hgoal :
    sqrt ((c0 * x0 + c1 * x1 + c2 * x2) * (c0 * x0 + c1 * x1 + c2 * x2)
          + (c0 * y0 + c1 * y1 + c2 * y2) * (c0 * y0 + c1 * y1 + c2 * y2))
    = dist A0 A3).
  { unfold dist, dist_sq, A0, A3; cbn [px py]. f_equal. ring. }
  assert (H01 : dist A0 A1 = c0 * sqrt (x0 * x0 + y0 * y0)).
  { rewrite <- (scaled_diff_norm c0 x0 y0 Hc0).
    unfold dist, dist_sq, A0, A1; cbn [px py]. f_equal. ring. }
  assert (H12 : dist A1 A2 = c1 * sqrt (x1 * x1 + y1 * y1)).
  { rewrite <- (scaled_diff_norm c1 x1 y1 Hc1).
    unfold dist, dist_sq, A1, A2; cbn [px py]. f_equal. ring. }
  assert (H23 : dist A2 A3 = c2 * sqrt (x2 * x2 + y2 * y2)).
  { rewrite <- (scaled_diff_norm c2 x2 y2 Hc2).
    unfold dist, dist_sq, A2, A3; cbn [px py]. f_equal. ring. }
  rewrite Hgoal, <- H01, <- H12, <- H23.
  pose proof (dist_triangle A0 A2 A3) as Ha.
  pose proof (dist_triangle A0 A1 A2) as Hb.
  lra.
Qed.

Lemma norm_pair_le : forall c0 c1 x0 y0 x1 y1,
  0 <= c0 -> 0 <= c1 ->
  sqrt ((c0 * x0 + c1 * x1) * (c0 * x0 + c1 * x1)
        + (c0 * y0 + c1 * y1) * (c0 * y0 + c1 * y1))
  <= c0 * sqrt (x0 * x0 + y0 * y0) + c1 * sqrt (x1 * x1 + y1 * y1).
Proof.
  intros c0 c1 x0 y0 x1 y1 Hc0 Hc1.
  pose proof (norm_triple_le c0 c1 0 x0 y0 x1 y1 0 0
                Hc0 Hc1 (Rle_refl 0)) as H.
  replace (0 * 0 + 0 * 0) with 0 in H by ring.
  rewrite sqrt_0 in H.
  assert (Heq :
    sqrt ((c0 * x0 + c1 * x1) * (c0 * x0 + c1 * x1)
          + (c0 * y0 + c1 * y1) * (c0 * y0 + c1 * y1))
    = sqrt ((c0 * x0 + c1 * x1 + 0 * 0) * (c0 * x0 + c1 * x1 + 0 * 0)
            + (c0 * y0 + c1 * y1 + 0 * 0) * (c0 * y0 + c1 * y1 + 0 * 0)))
    by (f_equal; ring).
  rewrite Heq. lra.
Qed.

(* Generic divided-difference chord bound both cubic combo and the
   rational pair specialize: |Δ| = ds · |Σ c_i v_i| ≤ ds · Σ c_i |v_i|. *)
Lemma chord_le_of_combo3 : forall ds c0 c1 c2 x0 y0 x1 y1 x2 y2,
  0 <= ds -> 0 <= c0 -> 0 <= c1 -> 0 <= c2 ->
  sqrt ((ds * (c0 * x0 + c1 * x1 + c2 * x2))
          * (ds * (c0 * x0 + c1 * x1 + c2 * x2))
        + (ds * (c0 * y0 + c1 * y1 + c2 * y2))
          * (ds * (c0 * y0 + c1 * y1 + c2 * y2)))
  <= ds * (c0 * sqrt (x0 * x0 + y0 * y0)
           + c1 * sqrt (x1 * x1 + y1 * y1)
           + c2 * sqrt (x2 * x2 + y2 * y2)).
Proof.
  intros ds c0 c1 c2 x0 y0 x1 y1 x2 y2 Hds Hc0 Hc1 Hc2.
  rewrite scaled_diff_norm by exact Hds.
  apply Rmult_le_compat_l; [exact Hds |].
  apply norm_triple_le; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Cubic divided-difference cofactors (shared with Bezier3Polygon.v).         *)
(* -------------------------------------------------------------------------- *)

Definition bezier3_c0 (s t : R) : R :=
  3 - 3 * (s + t) + (s * s + s * t + t * t).
Definition bezier3_c1 (s t : R) : R :=
  3 * (s + t) - 2 * (s * s + s * t + t * t).
Definition bezier3_c2 (s t : R) : R :=
  s * s + s * t + t * t.

Lemma bezier3_c_nonneg : forall s t,
  0 <= s -> s <= t -> t <= 1 ->
  0 <= bezier3_c0 s t /\ 0 <= bezier3_c1 s t /\ 0 <= bezier3_c2 s t.
Proof.
  intros s t Hs Hst Ht1.
  assert (Ht0 : 0 <= t) by lra.
  assert (H1s : 0 <= 1 - s) by lra.
  assert (H1t : 0 <= 1 - t) by lra.
  unfold bezier3_c0, bezier3_c1, bezier3_c2.
  split.
  { replace (3 - 3 * (s + t) + (s * s + s * t + t * t))
      with ((1 - s) * (1 - s) + (1 - s) * (1 - t) + (1 - t) * (1 - t))
      by ring.
    apply Rplus_le_le_0_compat.
    - apply Rplus_le_le_0_compat.
      + apply Rmult_le_pos; [exact H1s | exact H1s].
      + apply Rmult_le_pos; [exact H1s | exact H1t].
    - apply Rmult_le_pos; [exact H1t | exact H1t]. }
  split.
  { replace (3 * (s + t) - 2 * (s * s + s * t + t * t))
      with (2 * s * (1 - s) + 2 * t * (1 - t) + s * (1 - t) + t * (1 - s))
      by ring.
    apply Rplus_le_le_0_compat.
    - apply Rplus_le_le_0_compat.
      + apply Rplus_le_le_0_compat.
        * apply Rmult_le_pos; [apply Rmult_le_pos; [lra | exact Hs] | exact H1s].
        * apply Rmult_le_pos; [apply Rmult_le_pos; [lra | exact Ht0] | exact H1t].
      + apply Rmult_le_pos; [exact Hs | exact H1t].
    - apply Rmult_le_pos; [exact Ht0 | exact H1s]. }
  apply Rplus_le_le_0_compat.
  - apply Rplus_le_le_0_compat.
    + apply Rmult_le_pos; [exact Hs | exact Hs].
    + apply Rmult_le_pos; [exact Hs | exact Ht0].
  - apply Rmult_le_pos; [exact Ht0 | exact Ht0].
Qed.

Lemma bezier3_c_sum : forall s t,
  bezier3_c0 s t + bezier3_c1 s t + bezier3_c2 s t = 3.
Proof.
  intros s t. unfold bezier3_c0, bezier3_c1, bezier3_c2. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Rational layer: denominator floor from partition of unity.                 *)
(* -------------------------------------------------------------------------- *)

Lemma bern2_weighted_den_lb : forall w0 w1 w2 wmin t,
  0 <= t -> t <= 1 ->
  wmin <= w0 -> wmin <= w1 -> wmin <= w2 ->
  wmin <= bern2_0 t * w0 + bern2_1 t * w1 + bern2_2 t * w2.
Proof.
  intros w0 w1 w2 wmin t Ht0 Ht1 Hw0 Hw1 Hw2.
  destruct (bern2_nonneg t Ht0 Ht1) as (Hb0 & Hb1 & Hb2).
  pose proof (bern2_partition t) as Hp.
  replace wmin with (wmin * (bern2_0 t + bern2_1 t + bern2_2 t))
    by (rewrite Hp; ring).
  replace (wmin * (bern2_0 t + bern2_1 t + bern2_2 t))
    with (bern2_0 t * wmin + bern2_1 t * wmin + bern2_2 t * wmin)
    by ring.
  apply Rplus_le_compat.
  - apply Rplus_le_compat.
    + apply Rmult_le_compat_l; [exact Hb0 | exact Hw0].
    + apply Rmult_le_compat_l; [exact Hb1 | exact Hw1].
  - apply Rmult_le_compat_l; [exact Hb2 | exact Hw2].
Qed.

Print Assumptions bern_partition.
Print Assumptions bern_elevate_2.
Print Assumptions chord_le_of_combo3.
Print Assumptions bern2_weighted_den_lb.
