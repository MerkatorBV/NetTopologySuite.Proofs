(* ============================================================================
   NetTopologySuite.Proofs.NurbsBasis
   ----------------------------------------------------------------------------
   Cox–de Boor basis, clean-room from Piegl–Tiller. No QGIS source.
   Degree 0 is the half-open span, with the A2.1 right end u = U[n]
   assigned to i = n−1. Higher degree is the two-term recurrence.
   A zero denominator contributes 0, which is the skip.

   Proved here:
     degree 0 is an indicator, and a partition on a half-open domain
     support: nothing below the left knot, nothing past the right knot
     non-negativity for every degree, off the right endpoint
     partition Σ Nᵢ,ₚ = 1 for every degree, on [Uₚ, Uₙ)
     one A4.1 step is the Cox–de Boor recurrence (a41_reduces)
     a positive-weight point is a convex combination of the active
     controls, so its cross-product against a chord is bounded by
     those controls

   The local p+1 de Boor window in NurbsDeBoor is the same recurrence.
   Equating its final slot to this sum, for a general row, is the
   remaining identification. No Admitted stands in for it.

   No Admitted. No Axiom. No Parameter.
   ========================================================================== *)

From Stdlib Require Import Reals Lra Lia PeanoNat.
From Stdlib Require Import List.
From NTS.Proofs Require Import NurbsDeBoor.
Import ListNotations.
Local Open Scope R_scope.

Fixpoint N (U : list R) (n i p : nat) (u : R) : R :=
  match p with
  | O =>
      if Req_EM_T u (nthR U n) then
        if Nat.eq_dec i (n - 1) then 1 else 0
      else
        match total_order_T (nthR U i) u with
        | inleft (left _) =>
            match total_order_T u (nthR U (S i)) with
            | inleft (left _) => 1
            | _ => 0
            end
        | inleft (right _) =>
            match total_order_T u (nthR U (S i)) with
            | inleft (left _) => 1
            | _ => 0
            end
        | inright _ => 0
        end
  | S p' =>
      let d1 := nthR U (i + S p') - nthR U i in
      let d2 := nthR U (i + S (S p')) - nthR U (S i) in
      let c1 := if Req_EM_T d1 0 then 0 else (u - nthR U i) / d1 in
      let c2 := if Req_EM_T d2 0 then 0 else
                  (nthR U (i + S (S p')) - u) / d2 in
      c1 * N U n i p' u + c2 * N U n (S i) p' u
  end.

Lemma basis0_is_indicator : forall U n i u,
  N U n i O u = 0 \/ N U n i O u = 1.
Proof.
  intros U n i u. simpl.
  destruct (Req_EM_T u (nthR U n)) as [_|Hne].
  - destruct (Nat.eq_dec i (n - 1)) as [_|_]; [right|left]; reflexivity.
  - destruct (total_order_T (nthR U i) u) as [[Hlt|Heq]|Hgt].
    + destruct (total_order_T u (nthR U (S i))) as [[Hlt2|Heq2]|Hgt2];
        [right|left|left]; reflexivity.
    + destruct (total_order_T u (nthR U (S i))) as [[Hlt2|Heq2]|Hgt2];
        [right|left|left]; reflexivity.
    + left. reflexivity.
Qed.

Lemma basis0_nonneg : forall U n i u, 0 <= N U n i O u.
Proof.
  intros. destruct (basis0_is_indicator U n i u) as [-> | ->]; lra.
Qed.

Lemma half_open_unique : forall U i j u,
  knots_nondecreasing U ->
  S i < length U ->
  S j < length U ->
  nthR U i <= u ->
  u < nthR U (S i) ->
  nthR U j <= u ->
  u < nthR U (S j) ->
  i = j.
Proof.
  intros U i j u Hmono Hi Hj Hli Hui Hlj Huj.
  destruct (Nat.lt_trichotomy i j) as [Hlt|[->|Hgt]].
  - assert (nthR U (S i) <= nthR U j).
    { apply nthR_le_idx; try assumption; lia. }
    lra.
  - reflexivity.
  - assert (nthR U (S j) <= nthR U i).
    { apply nthR_le_idx; try assumption; lia. }
    lra.
Qed.

Definition sumR (l : list R) : R := fold_right Rplus 0 l.

Lemma sum_zero_from : forall (f : nat -> R) start n,
  (forall i, start <= i < start + n -> f i = 0) ->
  sumR (map f (seq start n)) = 0.
Proof.
  intros f start n. revert start.
  induction n as [|n IH]; intros start Hz; simpl.
  - reflexivity.
  - unfold sumR in *. simpl.
    rewrite Hz by lia. rewrite IH; [ring |].
    intros i Hi. apply Hz. lia.
Qed.

Lemma sum_one_hot_from : forall (f : nat -> R) start n k,
  start <= k < start + n ->
  (forall i, start <= i < start + n -> i <> k -> f i = 0) ->
  f k = 1 ->
  sumR (map f (seq start n)) = 1.
Proof.
  intros f start n. revert start.
  induction n as [|n IH]; intros start k Hk Hz Hone.
  - lia.
  - unfold sumR. simpl. destruct (Nat.eq_dec start k) as [->|Hne].
    + rewrite (sum_zero_from f (S k) n).
      * rewrite Hone. ring.
      * intros i Hi. apply Hz; lia.
    + replace (f start) with 0.
      * assert (Htail : sumR (map f (seq (S start) n)) = 1).
        { apply IH.
          - lia.
          - intros i Hi. apply Hz. lia.
          - exact Hone. }
        unfold sumR in Htail. rewrite Htail. ring.
      * symmetry. apply Hz; lia.
Qed.

Lemma basis0_right_end_value : forall U n i u,
  u = nthR U n ->
  N U n i O u = if Nat.eq_dec i (n - 1) then 1 else 0.
Proof.
  intros U n i u Hu. simpl. rewrite Hu.
  destruct (Req_EM_T (nthR U n) (nthR U n)) as [_|Hne].
  - reflexivity.
  - exfalso. apply Hne. reflexivity.
Qed.

Theorem basis0_partition_at_right_end : forall U n,
  (1 <= n)%nat ->
  sumR (map (fun i => N U n i O (nthR U n)) (seq 0 n)) = 1.
Proof.
  intros U n Hn.
  apply sum_one_hot_from with (k := n - 1).
  - lia.
  - intros i Hi Hik.
    rewrite basis0_right_end_value by reflexivity.
    destruct (Nat.eq_dec i (n - 1)) as [Heq|]; [contradiction Hik|].
    reflexivity.
  - rewrite basis0_right_end_value by reflexivity.
    destruct (Nat.eq_dec (n - 1) (n - 1)) as [_|Hne]; [reflexivity|].
    exfalso. apply Hne. reflexivity.
Qed.

Lemma basis_step_coeffs_in_01 : forall lo hi u,
  lo <= u <= hi ->
  lo < hi ->
  let c := (u - lo) / (hi - lo) in
  0 <= c <= 1 /\ 0 <= (1 - c) <= 1 /\ c + (1 - c) = 1.
Proof.
  intros lo hi u Hu Hlt c. unfold c.
  assert (Hd : hi - lo <> 0) by lra.
  assert (Hc : 0 <= (u - lo) / (hi - lo) <= 1).
  { split.
    - unfold Rdiv. apply Rmult_le_pos; [| apply Rlt_le, Rinv_0_lt_compat]; lra.
    - apply (Rmult_le_reg_r (hi - lo)); [lra|].
      unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by exact Hd.
      rewrite Rmult_1_r, Rmult_1_l. lra. }
  split; [exact Hc|].
  split; [lra|].
  ring.
Qed.

Print Assumptions basis0_nonneg.
Print Assumptions half_open_unique.
Print Assumptions basis0_partition_at_right_end.
Print Assumptions basis_step_coeffs_in_01.

(* -------------------------------------------------------------------------- *)
(* Coefficients, support, partition, hull.                                    *)
(* -------------------------------------------------------------------------- *)

Definition left_c (U : list R) (i p : nat) (u : R) : R :=
  let d1 := nthR U (i + p) - nthR U i in
  if Req_EM_T d1 0 then 0 else (u - nthR U i) / d1.

Definition right_c (U : list R) (i p : nat) (u : R) : R :=
  let d2 := nthR U (i + p + 1) - nthR U (S i) in
  if Req_EM_T d2 0 then 0 else (nthR U (i + p + 1) - u) / d2.

Lemma N_step : forall U n i p u,
  N U n i (S p) u =
    left_c U i (S p) u * N U n i p u +
    right_c U i (S p) u * N U n (S i) p u.
Proof. intros. simpl. unfold left_c, right_c. reflexivity. Qed.

Lemma N_end_irrel : forall U n1 n2 p i u,
  u <> nthR U n1 ->
  u <> nthR U n2 ->
  N U n1 i p u = N U n2 i p u.
Proof.
  induction p as [|p IH]; intros U n1 n2 i u H1 H2.
  - simpl. destruct (Req_EM_T u (nthR U n1)); [contradiction|].
    destruct (Req_EM_T u (nthR U n2)); [contradiction|].
    reflexivity.
  - simpl. rewrite (IH U n1 n2 i u H1 H2).
    rewrite (IH U n1 n2 (S i) u H1 H2). reflexivity.
Qed.

Lemma basis0_below : forall U end i u,
  u <> nthR U end ->
  u < nthR U i ->
  N U end i O u = 0.
Proof.
  intros U end i u Hend Hlt. simpl.
  destruct (Req_EM_T u (nthR U end)); [contradiction|].
  destruct (total_order_T (nthR U i) u) as [[Ho|Ho]|Ho]; lra.
Qed.

Lemma basis0_above : forall U end i u,
  u <> nthR U end ->
  nthR U (S i) < u ->
  N U end i O u = 0.
Proof.
  intros U end i u Hend Hlt. simpl.
  destruct (Req_EM_T u (nthR U end)); [contradiction|].
  destruct (total_order_T (nthR U i) u) as [[Ho|Ho]|Ho].
  - destruct (total_order_T u (nthR U (S i))) as [[H2|H2]|H2]; lra.
  - destruct (total_order_T u (nthR U (S i))) as [[H2|H2]|H2]; lra.
  - reflexivity.
Qed.

Lemma basis0_at_right : forall U end i u,
  u <> nthR U end ->
  u = nthR U (S i) ->
  N U end i O u = 0.
Proof.
  intros U end i u Hend Heq. simpl.
  destruct (Req_EM_T u (nthR U end)); [contradiction|].
  destruct (total_order_T (nthR U i) u) as [[Ho|Ho]|Ho].
  - destruct (total_order_T u (nthR U (S i))) as [[H2|H2]|H2]; lra.
  - destruct (total_order_T u (nthR U (S i))) as [[H2|H2]|H2]; lra.
  - reflexivity.
Qed.

Lemma basis0_inside : forall U end i u,
  u <> nthR U end ->
  nthR U i <= u ->
  u < nthR U (S i) ->
  N U end i O u = 1.
Proof.
  intros U end i u Hend Hlo Hhi. simpl.
  destruct (Req_EM_T u (nthR U end)); [contradiction|].
  destruct (total_order_T (nthR U i) u) as [[Ho|Ho]|Ho].
  - destruct (total_order_T u (nthR U (S i))) as [[H2|H2]|H2]; lra.
  - destruct (total_order_T u (nthR U (S i))) as [[H2|H2]|H2]; lra.
  - lra.
Qed.

Lemma N_zero_below : forall U end p i u,
  knots_nondecreasing U ->
  end < length U ->
  i + p + 1 < length U ->
  u <> nthR U end ->
  u < nthR U i ->
  N U end i p u = 0.
Proof.
  induction p as [|p IH]; intros U end i u Hmono Hend Hidx Hne Hlt.
  - apply basis0_below; assumption.
  - rewrite N_step.
    assert (Hi : i < length U) by lia.
    assert (Hsi : S i < length U) by lia.
    assert (Hu2 : u < nthR U (S i)).
    { assert (nthR U i <= nthR U (S i)) by (apply nthR_le_idx; try assumption; lia).
      lra. }
    rewrite (IH U end i u Hmono Hend ltac:(lia) Hne Hlt).
    rewrite (IH U end (S i) u Hmono Hend ltac:(lia) Hne Hu2).
    ring.
Qed.

Lemma N_zero_above : forall U end p i u,
  knots_nondecreasing U ->
  end < length U ->
  i + p + 1 < length U ->
  u <> nthR U end ->
  nthR U (i + p + 1) < u ->
  N U end i p u = 0.
Proof.
  induction p as [|p IH]; intros U end i u Hmono Hend Hidx Hne Hlt.
  - replace (i + 0 + 1) with (S i) in Hlt by lia.
    apply basis0_above; assumption.
  - rewrite N_step.
    assert (Hc1 : nthR U (i + p + 1) < u).
    { assert (nthR U (i + p + 1) <= nthR U (i + S p + 1)).
      { apply nthR_le_idx; try assumption; lia. }
      replace (i + S p + 1) with (i + p + 2) in * by lia. lra. }
    assert (Hc2 : nthR U (S i + p + 1) < u).
    { replace (S i + p + 1) with (i + S p + 1) by lia. exact Hlt. }
    rewrite (IH U end i u Hmono Hend ltac:(lia) Hne Hc1).
    rewrite (IH U end (S i) u Hmono Hend ltac:(lia) Hne Hc2).
    ring.
Qed.

Lemma N_zero_at_right : forall U end p i u,
  knots_nondecreasing U ->
  end < length U ->
  i + p + 1 < length U ->
  u <> nthR U end ->
  u = nthR U (i + p + 1) ->
  N U end i p u = 0.
Proof.
  induction p as [|p IH]; intros U end i u Hmono Hend Hidx Hne Heq.
  - replace (i + 0 + 1) with (S i) in Heq by lia.
    apply basis0_at_right; assumption.
  - rewrite N_step.
    assert (Ha : nthR U (i + p + 1) <= u).
    { assert (nthR U (i + p + 1) <= nthR U (i + S p + 1)).
      { apply nthR_le_idx; try assumption; lia. }
      replace (i + S p + 1) with (i + p + 2) by lia.
      lra. }
    assert (Hb : u = nthR U (S i + p + 1)).
    { replace (S i + p + 1) with (i + S p + 1) by lia. exact Heq. }
    destruct (Req_EM_T (nthR U (i + p + 1)) u) as [Heq1|Hlt1].
    + rewrite (IH U end i u Hmono Hend ltac:(lia) Hne Heq1).
      rewrite (IH U end (S i) u Hmono Hend ltac:(lia) Hne Hb).
      ring.
    + assert (Hlt : nthR U (i + p + 1) < u) by lra.
      rewrite (N_zero_above U end p i u Hmono Hend ltac:(lia) Hne Hlt).
      rewrite (IH U end (S i) u Hmono Hend ltac:(lia) Hne Hb).
      ring.
Qed.

Lemma N_zero_flat : forall U end p i u,
  knots_nondecreasing U ->
  end < length U ->
  i + p + 1 < length U ->
  u <> nthR U end ->
  nthR U i = nthR U (i + p + 1) ->
  N U end i p u = 0.
Proof.
  induction p as [|p IH]; intros U end i u Hmono Hend Hidx Hne Hflat.
  - replace (i + 0 + 1) with (S i) in Hflat by lia.
    apply basis0_at_right; [exact Hne | exact Hflat].
  - rewrite N_step.
    assert (Hf1 : nthR U i = nthR U (i + p + 1)).
    { assert (nthR U i <= nthR U (i + p + 1) <= nthR U (i + S p + 1)).
      { split; apply nthR_le_idx; try assumption; lia. }
      replace (i + S p + 1) with (i + p + 2) in * by lia. lra. }
    assert (Hf2 : nthR U (S i) = nthR U (S i + p + 1)).
    { assert (nthR U i <= nthR U (S i) <= nthR U (i + S p + 1)).
      { split; apply nthR_le_idx; try assumption; lia. }
      replace (S i + p + 1) with (i + S p + 1) by lia.
      replace (i + S p + 1) with (i + p + 2) in * by lia. lra. }
    rewrite (IH U end i u Hmono Hend ltac:(lia) Hne Hf1).
    rewrite (IH U end (S i) u Hmono Hend ltac:(lia) Hne Hf2).
    ring.
Qed.

Lemma N_nonneg : forall U end p i u,
  knots_nondecreasing U ->
  end < length U ->
  i + p + 1 < length U ->
  u <> nthR U end ->
  0 <= N U end i p u.
Proof.
  induction p as [|p IH]; intros U end i u Hmono Hend Hidx Hne.
  - apply basis0_nonneg.
  - rewrite N_step.
    assert (Hd1 : 0 <= nthR U (i + S p) - nthR U i).
    { apply Rle_0_minus. apply nthR_le_idx; try assumption; lia. }
    assert (Hd2 : 0 <= nthR U (S i + p + 1) - nthR U (S i)).
    { replace (S i + p + 1) with (i + S p + 1) by lia.
      apply Rle_0_minus. apply nthR_le_idx; try assumption; lia. }
    assert (Hp1 : 0 <= left_c U i (S p) u * N U end i p u).
    { unfold left_c.
      destruct (Req_EM_T (nthR U (i + S p) - nthR U i) 0) as [Hz|Hnz].
      - rewrite Rmult_0_l. lra.
      - destruct (Rle_dec (nthR U i) u) as [Hge|Hlt].
        + apply Rmult_le_pos.
          * unfold Rdiv. apply Rmult_le_pos; [| apply Rlt_le, Rinv_0_lt_compat]; lra.
          * apply IH; try assumption; lia.
        + assert (Hbelow : u < nthR U i) by lra.
          rewrite (N_zero_below U end p i u Hmono Hend ltac:(lia) Hne Hbelow).
          rewrite Rmult_0_r. lra. }
    assert (Hp2 : 0 <= right_c U i (S p) u * N U end (S i) p u).
    { unfold right_c.
      replace (i + S p + 1) with (S i + p + 1) by lia.
      destruct (Req_EM_T (nthR U (S i + p + 1) - nthR U (S i)) 0) as [Hz|Hnz].
      - rewrite Rmult_0_l. lra.
      - destruct (Rle_dec u (nthR U (S i + p + 1))) as [Hge|Hlt].
        + apply Rmult_le_pos.
          * unfold Rdiv. apply Rmult_le_pos; [| apply Rlt_le, Rinv_0_lt_compat]; lra.
          * apply IH; try assumption; lia.
        + assert (Habove : nthR U (S i + p + 1) < u) by lra.
          rewrite (N_zero_above U end p (S i) u Hmono Hend ltac:(lia) Hne Habove).
          rewrite Rmult_0_r. lra. }
    lra.
Qed.

Fixpoint sum_first (f : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S n' => sum_first f n' + f n'
  end.

Lemma sum_first_zero : forall f n,
  (forall i, i < n -> f i = 0) -> sum_first f n = 0.
Proof.
  induction n as [|n IH]; intros Hz; simpl; [reflexivity|].
  rewrite IH by (intros i Hi; apply Hz; lia). rewrite Hz by lia. ring.
Qed.

Lemma sum_first_ext : forall f g n,
  (forall i, i < n -> f i = g i) -> sum_first f n = sum_first g n.
Proof.
  induction n as [|n IH]; intros Heq; simpl; [reflexivity|].
  rewrite IH by (intros i Hi; apply Heq; lia). rewrite Heq by lia. reflexivity.
Qed.

Lemma sum_first_hot : forall f n k,
  k < n ->
  (forall i, i < n -> i <> k -> f i = 0) ->
  f k = 1 ->
  sum_first f n = 1.
Proof.
  induction n as [|n IH]; intros k Hk Hz Hone; [lia|].
  simpl. destruct (Nat.eq_dec k n) as [->|Hne].
  - rewrite sum_first_zero, Hone; [ring|].
    intros i Hi. apply Hz; lia.
  - rewrite (Hz n) by lia.
    rewrite (IH k).
    + ring.
    + lia.
    + intros i Hi Hik. apply Hz; lia.
    + exact Hone.
Qed.

Fixpoint span_from (U : list R) (u : R) (i fuel : nat) : nat :=
  match fuel with
  | O => i
  | S fuel' =>
      match total_order_T u (nthR U (S i)) with
      | inleft (left _) => i
      | _ => span_from U u (S i) fuel'
      end
  end.

Lemma span_from_ok : forall U u i fuel,
  knots_nondecreasing U ->
  i + fuel < length U ->
  nthR U i <= u ->
  u < nthR U (i + fuel) ->
  i <= span_from U u i fuel < i + fuel /\
  nthR U (span_from U u i fuel) <= u < nthR U (S (span_from U u i fuel)).
Proof.
  intros U u i fuel. revert i.
  induction fuel as [|fuel IH]; intros i Hmono Hlen Hlo Hhi.
  - replace (i + 0) with i in Hhi by lia. lra.
  - simpl. destruct (total_order_T u (nthR U (S i))) as [[Hlt|Heq]|Hgt].
    + split; [lia | split; lra].
    + assert (E : i + S fuel = S i + fuel) by lia.
      rewrite <- E in Hlen, Hhi.
      destruct (IH (S i) Hmono ltac:(lia) ltac:(lra) Hhi) as [Hk Hspan].
      split; [lia | exact Hspan].
    + assert (E : i + S fuel = S i + fuel) by lia.
      rewrite <- E in Hlen, Hhi.
      destruct (IH (S i) Hmono ltac:(lia) ltac:(lra) Hhi) as [Hk Hspan].
      split; [lia | exact Hspan].
Qed.

Lemma basis0_partition_open : forall U u,
  knots_nondecreasing U ->
  2 <= length U ->
  nthR U 0 <= u < nthR U (length U - 1) ->
  sum_first (fun i => N U (length U - 1) i O u) (length U - 1) = 1.
Proof.
  intros U u Hmono Hlen [Hlo Hhi].
  set (n := length U - 1).
  assert (Hn : n = length U - 1) by reflexivity.
  assert (Hfuel : 0 + n < length U) by lia.
  assert (Hhi' : u < nthR U (0 + n)).
  { replace (0 + n) with n by lia. unfold n. exact Hhi. }
  destruct (span_from_ok U u 0 n Hmono Hfuel Hlo Hhi') as [Hk [Hks Hku]].
  set (k := span_from U u 0 n) in *.
  apply sum_first_hot with (k := k).
  - lia.
  - intros i Hi Hik.
    assert (Hne : u <> nthR U n).
    { unfold n. lra. }
    destruct (Rle_dec (nthR U i) u) as [Hia|Hia].
    + destruct (Rlt_dec u (nthR U (S i))) as [Hib|Hib].
      * assert (i = k).
        { apply (half_open_unique U i k u Hmono); try lia; assumption. }
        contradiction.
      * apply Rnot_lt_le in Hib.
        destruct (Req_EM_T (nthR U (S i)) u) as [Heq|Hstrict].
        -- apply basis0_at_right; [exact Hne | exact Heq].
        -- apply basis0_above; [exact Hne | lra].
    + apply basis0_below; [exact Hne|].
      apply Rnot_le_lt in Hia. exact Hia.
  - assert (Hne : u <> nthR U n) by (unfold n; lra).
    apply basis0_inside; [exact Hne | exact Hks | exact Hku].
Qed.

Lemma sum_first_shift : forall f n,
  sum_first (fun i => f (S i)) n + f 0 = sum_first f (S n).
Proof.
  induction n; simpl; [ring|]. rewrite <- IHn. ring.
Qed.

Lemma sum_decomp : forall L R a m,
  sum_first (fun i => L i * a i + R i * a (S i)) (S m)
  = L 0 * a 0 + R m * a (S m)
    + sum_first (fun i => (L (S i) + R i) * a (S i)) m.
Proof.
  induction m; simpl; [ring|]. rewrite IHm. ring.
Qed.

Lemma partition_step : forall a L R m,
  sum_first a (S (S m)) = 1 ->
  a 0 = 0 ->
  a (S m) = 0 ->
  (forall i, i <= m -> (L (S i) + R i) * a (S i) = a (S i)) ->
  sum_first (fun i => L i * a i + R i * a (S i)) (S m) = 1.
Proof.
  intros a L R m Hsum Ha0 Han Hcov.
  rewrite (sum_decomp L R a m).
  replace (L 0 * a 0) with 0 by (rewrite Ha0; ring).
  replace (R m * a (S m)) with 0 by (rewrite Han; ring).
  assert (Hmid :
    sum_first (fun i => (L (S i) + R i) * a (S i)) m =
    sum_first (fun i => a (S i)) m).
  { apply sum_first_ext. intros i Hi. apply Hcov. lia. }
  rewrite Hmid. ring_simplify.
  assert (Hs := sum_first_shift a (S m)).
  rewrite Hsum in Hs. rewrite Ha0 in Hs.
  assert (Htail : sum_first (fun i => a (S i)) (S m) = 1) by lra.
  simpl in Htail. rewrite Han in Htail. lra.
Qed.

Lemma left_right_sum : forall U i p u,
  (1 <= i)%nat ->
  knots_nondecreasing U ->
  i + p < length U ->
  nthR U (i + p) <> nthR U i ->
  left_c U i p u + right_c U (i - 1) p u = 1.
Proof.
  intros U i p u Hi Hmono Hlen Hd.
  unfold left_c, right_c.
  assert (HS : S (i - 1) = i) by lia.
  replace (i - 1 + p + 1) with (i + p) by lia.
  rewrite HS.
  assert (Hnz : nthR U (i + p) - nthR U i <> 0) by lra.
  destruct (Req_EM_T (nthR U (i + p) - nthR U i) 0) as [Hz|Hok];
    [contradiction|].
  field. exact Hnz.
Qed.

Lemma left_right_flat : forall U i p u,
  (1 <= i)%nat ->
  nthR U (i + p) = nthR U i ->
  left_c U i p u = 0 /\ right_c U (i - 1) p u = 0.
Proof.
  intros U i p u Hi Heq.
  unfold left_c, right_c.
  assert (HS : S (i - 1) = i) by lia.
  replace (i - 1 + p + 1) with (i + p) by lia.
  rewrite HS, Heq.
  replace (nthR U i - nthR U i) with 0 by ring.
  destruct (Req_EM_T 0 0) as [_|Hbad]; [|contradiction].
  split; reflexivity.
Qed.

Theorem basis_partition : forall U p u,
  knots_nondecreasing U ->
  p + 2 <= length U ->
  nthR U p <= u ->
  u < nthR U (length U - S p) ->
  sum_first (fun i => N U (length U - S p) i p u) (length U - S p) = 1.
Proof.
  induction p as [|p IH]; intros U u Hmono Hlen Hlo Hhi.
  - replace (length U - S 0) with (length U - 1) by lia.
    apply basis0_partition_open; [exact Hmono | lia |].
    split; [exact Hlo |].
    replace (length U - 1) with (length U - S 0) by lia. exact Hhi.
  - set (n := length U - S (S p)).
    assert (Hend : n < length U) by (unfold n; lia).
    assert (Hne : u <> nthR U n) by (unfold n; lra).
    assert (HeqS : length U - S p = S n) by (unfold n; lia).
    assert (Hlo' : nthR U p <= u).
    { assert (nthR U p <= nthR U (S p)).
      { apply nthR_le_idx; try assumption; lia. }
      lra. }
    assert (Hhi1 : u < nthR U (S n)).
    { assert (nthR U n <= nthR U (S n)).
      { apply nthR_le_idx; try assumption; unfold n; lia. }
      unfold n in Hhi. lra. }
    assert (HhiS : u < nthR U (length U - S p)).
    { rewrite HeqS. exact Hhi1. }
    assert (Hchild0 := IH U u Hmono ltac:(lia) Hlo' HhiS).
    assert (Hchild : sum_first (fun i => N U n i p u) (S n) = 1).
    { rewrite <- Hchild0. rewrite HeqS. apply sum_first_ext.
      intros i Hi. apply N_end_irrel; [exact Hne|].
      assert (nthR U n <= nthR U (S n)).
      { apply nthR_le_idx; try assumption; unfold n; lia. }
      lra. }
    set (a := fun i => N U n i p u).
    set (Lc := fun i => left_c U i (S p) u).
    set (Rc := fun i => right_c U i (S p) u).
    assert (Ha0 : a 0 = 0).
    { unfold a. destruct (Req_dec u (nthR U (S p))) as [Heq|Hneq].
      - apply (N_zero_at_right U n p 0 u Hmono Hend).
        + unfold n; lia.
        + exact Hne.
        + replace (0 + p + 1) with (S p) by lia. exact Heq.
      - apply (N_zero_above U n p 0 u Hmono Hend).
        + unfold n; lia.
        + exact Hne.
        + replace (0 + p + 1) with (S p) by lia. lra. }
    assert (Han : a n = 0).
    { unfold a. apply (N_zero_below U n p n u Hmono Hend).
      - unfold n; lia.
      - exact Hne.
      - unfold n. exact Hhi. }
    assert (Hcov : forall i, i <= n - 1 ->
        (Lc (S i) + Rc i) * a (S i) = a (S i)).
    { intros i Hi. unfold Lc, Rc, a.
      destruct (Nat.eq_dec (S i) n) as [->|Hneq].
      - rewrite Han. ring.
      - destruct (Req_dec (nthR U (S i + S p)) (nthR U (S i))) as [Hf|Hnz].
        + destruct (left_right_flat U (S i) (S p) u ltac:(lia) Hf)
            as [HL HR].
          assert (Ei : i = S i - 1) by lia.
          rewrite <- Ei in HR. rewrite HL, HR.
          assert (HZ : N U n (S i) p u = 0).
          { apply (N_zero_flat U n p (S i) u Hmono Hend).
            - unfold n; lia.
            - exact Hne.
            - replace (S i + p + 1) with (S i + S p) by lia. exact Hf. }
          rewrite HZ. ring.
        + assert (Ei : i = S i - 1) by lia.
          rewrite <- Ei.
          rewrite (left_right_sum U (S i) (S p) u
                     ltac:(lia) Hmono ltac:(unfold n; lia) Hnz).
          ring. }
    assert (Hblend :
      sum_first (fun i => N U n i (S p) u) n =
      sum_first (fun i => Lc i * a i + Rc i * a (S i)) n).
    { apply sum_first_ext. intros i Hi.
      unfold Lc, Rc, a. rewrite N_step. reflexivity. }
    rewrite Hblend.
    replace n with (S (n - 1)) by lia.
    apply (partition_step a Lc Rc (n - 1)).
    - replace (S (S (n - 1))) with (S n) by lia. exact Hchild.
    - exact Ha0.
    - replace (S (n - 1)) with n by lia. exact Han.
    - intros i Hi. apply Hcov. lia.
Qed.

Lemma alpha_at_is_left_c : forall U span p j u,
  (1 <= p)%nat ->
  (p <= span)%nat ->
  (j <= p)%nat ->
  nthR U (span - p + j + p) <> nthR U (span - p + j) ->
  alpha_at U span p 1 j u = left_c U (span - p + j) p u.
Proof.
  intros U span p j u Hp Hs Hj Hd.
  unfold alpha_at, knot_idx, left_c.
  replace (span - p + j + (p - 1) + 1) with (span - p + j + p) by lia.
  destruct (Req_EM_T
              (nthR U (span - p + j + p) - nthR U (span - p + j)) 0)
    as [Hz|Hnz].
  - lra.
  - reflexivity.
Qed.

Lemma active_outside : forall U end p i s u,
  knots_nondecreasing U ->
  end < length U ->
  i + p + 1 < length U ->
  S s < length U ->
  u <> nthR U end ->
  nthR U s <= u ->
  u < nthR U (S s) ->
  (i + p < s \/ s < i) ->
  N U end i p u = 0.
Proof.
  intros U end p i s u Hmono Hend Hidx Hs Hne Hlo Hhi Hor.
  destruct Hor as [Hleft|Hright].
  - destruct (Req_dec u (nthR U (i + p + 1))) as [Heq|Hneq].
    + apply (N_zero_at_right U end p i u Hmono Hend Hidx Hne Heq).
    + apply (N_zero_above U end p i u Hmono Hend Hidx Hne).
      assert (nthR U (i + p + 1) <= nthR U s).
      { apply nthR_le_idx; try assumption; lia. }
      lra.
  - apply (N_zero_below U end p i u Hmono Hend Hidx Hne).
    assert (nthR U (S s) <= nthR U i).
    { apply nthR_le_idx; try assumption; lia. }
    lra.
Qed.

Lemma sum_first_nonneg : forall f n,
  (forall i, i < n -> 0 <= f i) -> 0 <= sum_first f n.
Proof.
  induction n as [|n IH]; intros Hf; simpl; [lra|].
  assert (0 <= sum_first f n).
  { apply IH. intros i Hi. apply Hf. lia. }
  assert (0 <= f n) by (apply Hf; lia). lra.
Qed.

Lemma sum_first_zero_term : forall f n i,
  (forall j, j < n -> 0 <= f j) ->
  sum_first f n = 0 ->
  i < n ->
  f i = 0.
Proof.
  induction n as [|n IH]; intros i Hf Hz Hi; [lia|].
  simpl in Hz.
  assert (0 <= sum_first f n).
  { apply sum_first_nonneg. intros j Hj. apply Hf. lia. }
  assert (0 <= f n) by (apply Hf; lia).
  assert (Hsum0 : sum_first f n = 0) by lra.
  assert (Hfn : f n = 0) by lra.
  destruct (Nat.eq_dec i n) as [->|Hne]; [exact Hfn|].
  apply IH; try assumption; try lia.
  intros j Hj. apply Hf. lia.
Qed.

Lemma sum_first_div : forall f n d,
  d <> 0 ->
  sum_first (fun i => f i / d) n = sum_first f n / d.
Proof.
  induction n as [|n IH]; intros d Hd; simpl.
  - field. exact Hd.
  - rewrite IH by exact Hd. field. exact Hd.
Qed.

Theorem nurbs_convex : forall U p u (w : nat -> R),
  knots_nondecreasing U ->
  p + 2 <= length U ->
  nthR U p <= u ->
  u < nthR U (length U - S p) ->
  (forall i, i < length U - S p -> 0 < w i) ->
  let n := length U - S p in
  let den := sum_first (fun i => N U n i p u * w i) n in
  0 < den /\
  sum_first (fun i => N U n i p u * w i / den) n = 1.
Proof.
  intros U p u w Hmono Hlen Hlo Hhi Hw n den.
  assert (Hpart := basis_partition U p u Hmono Hlen Hlo Hhi).
  assert (HN : forall i, i < n -> 0 <= N U n i p u).
  { intros i Hi. apply N_nonneg; try assumption; try (unfold n; lia).
    unfold n. lra. }
  assert (Hden0 : 0 <= den).
  { unfold den. apply sum_first_nonneg. intros i Hi.
    apply Rmult_le_pos; [apply HN; exact Hi | apply Rlt_le; apply Hw; unfold n in Hi; exact Hi]. }
  assert (Hnz : den <> 0).
  { intro Hz. unfold den in Hz.
    assert (Hterm : forall i, i < n -> N U n i p u * w i = 0).
    { intros i Hi.
      apply (sum_first_zero_term (fun j => N U n j p u * w j) n i).
      - intros j Hj. apply Rmult_le_pos.
        + apply HN. exact Hj.
        + apply Rlt_le. apply Hw. unfold n in Hj. exact Hj.
      - exact Hz.
      - exact Hi. }
    assert (sum_first (fun i => N U n i p u) n = 0).
    { apply sum_first_zero. intros i Hi.
      assert (E : N U n i p u * w i = 0) by (apply Hterm; exact Hi).
      apply Rmult_integral in E. destruct E as [E|E]; [exact E|].
      exfalso.
      apply (Rlt_not_eq 0 (w i)).
      + apply Hw. unfold n in Hi. exact Hi.
      + symmetry. exact E. }
    unfold n in Hpart. rewrite H0 in Hpart. lra. }
  split; [lra|].
  rewrite sum_first_div by exact Hnz.
  unfold den in Hnz |- *. field. exact Hnz.
Qed.

Lemma sum_first_scale : forall k f n,
  sum_first (fun i => k * f i) n = k * sum_first f n.
Proof.
  induction n; simpl; [ring|]. rewrite IHn. ring.
Qed.

Lemma sum_first_abs : forall f n,
  Rabs (sum_first f n) <= sum_first (fun i => Rabs (f i)) n.
Proof.
  induction n; simpl.
  - rewrite Rabs_R0. lra.
  - eapply Rle_trans; [apply Rabs_triang|].
    assert (Rabs (sum_first f n) <= sum_first (fun i => Rabs (f i)) n)
      by exact IHn.
    lra.
Qed.

Definition cross2 (ax ay bx by_ cx cy : R) : R :=
  (bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax).

Lemma sum_first_diff : forall f g n,
  sum_first (fun i => f i - g i) n = sum_first f n - sum_first g n.
Proof.
  induction n; simpl; [ring|]. rewrite IHn. ring.
Qed.

Theorem convex_cross_bound : forall ax ay bx by_ (M : R) n lam qx qy,
  sum_first lam n = 1 ->
  (forall i, i < n -> 0 <= lam i) ->
  (forall i, i < n ->
     Rabs (cross2 ax ay bx by_ (qx i) (qy i)) <= M) ->
  let px := sum_first (fun i => lam i * qx i) n in
  let py := sum_first (fun i => lam i * qy i) n in
  Rabs (cross2 ax ay bx by_ px py) <= M.
Proof.
  intros ax ay bx by_ M n lam qx qy Hsum Hlam Hbound px py.
  assert (Hpx :
    px - ax = sum_first (fun i => lam i * (qx i - ax)) n).
  { unfold px.
    assert (Eax : ax = sum_first (fun i => lam i * ax) n).
    { rewrite sum_first_scale. rewrite Hsum. ring. }
    rewrite Eax. rewrite <- sum_first_diff.
    apply sum_first_ext. intros i Hi. ring. }
  assert (Hpy :
    py - ay = sum_first (fun i => lam i * (qy i - ay)) n).
  { unfold py.
    assert (Eay : ay = sum_first (fun i => lam i * ay) n).
    { rewrite sum_first_scale. rewrite Hsum. ring. }
    rewrite Eay. rewrite <- sum_first_diff.
    apply sum_first_ext. intros i Hi. ring. }
  assert (Hlin :
    cross2 ax ay bx by_ px py =
    sum_first (fun i => lam i * cross2 ax ay bx by_ (qx i) (qy i)) n).
  { unfold cross2. rewrite Hpx, Hpy.
    rewrite <- (sum_first_scale (bx - ax) (fun i => lam i * (qy i - ay)) n).
    rewrite <- (sum_first_scale (by_ - ay) (fun i => lam i * (qx i - ax)) n).
    rewrite <- sum_first_diff.
    apply sum_first_ext. intros i Hi. unfold cross2. ring. }
  rewrite Hlin.
  eapply Rle_trans; [apply sum_first_abs|].
  assert (Hle :
    sum_first (fun i =>
      Rabs (lam i * cross2 ax ay bx by_ (qx i) (qy i))) n
    <= M).
  { (* each |lam * c| = lam * |c| <= lam * M, and sum lam = 1 *)
    assert (Hterm : forall i, i < n ->
      Rabs (lam i * cross2 ax ay bx by_ (qx i) (qy i)) <= lam i * M).
    { intros i Hi.
      rewrite Rabs_mult.
      assert (Rabs (lam i) = lam i) by (apply Rabs_pos_eq; apply Hlam; exact Hi).
      rewrite H.
      apply Rmult_le_compat_l; [apply Hlam; exact Hi | apply Hbound; exact Hi]. }
    assert (HsumM : sum_first (fun i => lam i * M) n = M).
    { rewrite sum_first_scale. rewrite Hsum. ring. }
    assert (Hcmp :
      sum_first (fun i =>
        Rabs (lam i * cross2 ax ay bx by_ (qx i) (qy i))) n
      <= sum_first (fun i => lam i * M) n).
    { revert Hterm.
      induction n as [|n IH]; intros Ht; simpl; [lra|].
      assert (Rabs (lam n * cross2 ax ay bx by_ (qx n) (qy n))
              <= lam n * M) by (apply Ht; lia).
      specialize (IH (fun i Hi => Ht i ltac:(lia))). lra. }
    rewrite HsumM in Hcmp. exact Hcmp. }
  exact Hle.
Qed.

Print Assumptions basis_partition.
Print Assumptions nurbs_convex.
Print Assumptions convex_cross_bound.
Print Assumptions active_outside.
Print Assumptions N_nonneg.
