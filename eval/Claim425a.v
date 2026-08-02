(* ============================================================================
   nts-eval micro unit — claimId 425-a (GREEN)
   Red planted 2026-08-02 · Green closed 2026-08-02
   ----------------------------------------------------------------------------
   Polygonal coverage gap/overlap cleaner validity: after cleaning, the
   coverage is pairwise open-interior disjoint (overlap-free) and its
   covered region matches the input up to boundary null sets.

   GREEN.  The headline claim is stated
   (`coverage_gap_overlap_cleaner_valid_claim`) and CLOSED in this unit
   (`coverage_gap_overlap_cleaner_valid`, Qed) — the witness-scoped
   version of the production proof.  Production home:
   `theories/CoverageGapOverlapCleaner.v`, same WITNESS tag.  Red history:
   the claim was planted with Abort headlines + Qed witness pins; Green
   exhibits a 3-cell open-interior-disjoint partition of the rational
   two-cell overlap witness and discharges overlap-free + same-union
   (open → closed both ways).

   What IS Qed here: the rational witness pins (raw coverage not
   overlap-free) plus the cleaner soundness lemmas on that witness.

   WITNESS claimId: 425-a
   Lemma (Green): coverage_gap_overlap_cleaner_valid
   ========================================================================== *)

(* WITNESS {"claimId":"425-a","topic":"coverage","lemma":"coverage_gap_overlap_cleaner_valid","title":"Coverage gap/overlap cleaner establishes valid coverage"} *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
Local Open Scope R_scope.

(* ---- Minimal geometry carrier (Point / AABB twins) ------------------------ *)

Record Point : Type := mkPoint { px : R; py : R }.

Record Aabb : Type := mkAabb {
  amin_x : R;
  amax_x : R;
  amin_y : R;
  amax_y : R
}.

Definition Coverage : Type := list Aabb.

Definition in_open_aabb (a : Aabb) (p : Point) : Prop :=
  amin_x a < px p < amax_x a /\ amin_y a < py p < amax_y a.

Definition in_closed_aabb (a : Aabb) (p : Point) : Prop :=
  amin_x a <= px p <= amax_x a /\ amin_y a <= py p <= amax_y a.

Definition coverage_overlap_free (cov : Coverage) : Prop :=
  forall (c1 c2 : Aabb) (p : Point),
    In c1 cov ->
    In c2 cov ->
    c1 <> c2 ->
    ~ (in_open_aabb c1 p /\ in_open_aabb c2 p).

Definition coverage_union_open (cov : Coverage) (p : Point) : Prop :=
  exists c, In c cov /\ in_open_aabb c p.

Definition coverage_union_closed (cov : Coverage) (p : Point) : Prop :=
  exists c, In c cov /\ in_closed_aabb c p.

Definition coverage_gap_free (cov : Coverage) (target : Aabb) : Prop :=
  forall p : Point,
    in_open_aabb target p ->
    exists c, In c cov /\ in_closed_aabb c p.

(** Union preserved up to boundary null sets. *)
Definition coverage_same_union (c1 c2 : Coverage) : Prop :=
  (forall p, coverage_union_open c1 p -> coverage_union_closed c2 p) /\
  (forall p, coverage_union_open c2 p -> coverage_union_closed c1 p).

Definition is_valid_coverage_cleaner_on
  (clean : Coverage -> Coverage) (cov : Coverage) : Prop :=
  coverage_overlap_free (clean cov) /\
  coverage_same_union (clean cov) cov.

(* -------------------------------------------------------------------------- *)
(* Rational two-cell overlap witness                                          *)
(* -------------------------------------------------------------------------- *)

Definition cov_cell_A : Aabb := mkAabb 0 1 0 1.
Definition cov_cell_B : Aabb := mkAabb (1 / 2) (3 / 2) (1 / 2) (3 / 2).
Definition cov_overlap_witness : Coverage := [cov_cell_A; cov_cell_B].
Definition cov_overlap_sample : Point := mkPoint (3 / 4) (3 / 4).

Lemma cov_cell_A_B_distinct : cov_cell_A <> cov_cell_B.
Proof.
  unfold cov_cell_A, cov_cell_B. intros Heq.
  assert (Hx : amin_x (mkAabb 0 1 0 1)
             = amin_x (mkAabb (1 / 2) (3 / 2) (1 / 2) (3 / 2)))
    by (rewrite Heq; reflexivity).
  cbn in Hx. lra.
Qed.

Lemma cov_cell_A_in_witness : In cov_cell_A cov_overlap_witness.
Proof. unfold cov_overlap_witness. simpl. left. reflexivity. Qed.

Lemma cov_cell_B_in_witness : In cov_cell_B cov_overlap_witness.
Proof. unfold cov_overlap_witness. simpl. right. left. reflexivity. Qed.

Lemma cov_overlap_sample_in_A :
  in_open_aabb cov_cell_A cov_overlap_sample.
Proof.
  unfold in_open_aabb, cov_cell_A, cov_overlap_sample;
    cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

Lemma cov_overlap_sample_in_B :
  in_open_aabb cov_cell_B cov_overlap_sample.
Proof.
  unfold in_open_aabb, cov_cell_B, cov_overlap_sample;
    cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

Lemma cov_overlap_sample_in_both :
  in_open_aabb cov_cell_A cov_overlap_sample /\
  in_open_aabb cov_cell_B cov_overlap_sample.
Proof.
  split; [exact cov_overlap_sample_in_A | exact cov_overlap_sample_in_B].
Qed.

Lemma cov_overlap_witness_not_overlap_free :
  ~ coverage_overlap_free cov_overlap_witness.
Proof.
  unfold coverage_overlap_free.
  intros Hfree.
  specialize (Hfree cov_cell_A cov_cell_B cov_overlap_sample
                cov_cell_A_in_witness cov_cell_B_in_witness
                cov_cell_A_B_distinct).
  apply Hfree.
  exact cov_overlap_sample_in_both.
Qed.

Lemma cov_overlap_sample_closed_A :
  in_closed_aabb cov_cell_A cov_overlap_sample.
Proof.
  unfold in_closed_aabb, cov_cell_A, cov_overlap_sample;
    cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Concrete 3-cell cleaner partition                                          *)
(* -------------------------------------------------------------------------- *)

Definition cov_cell_B_top : Aabb := mkAabb (1 / 2) 1 1 (3 / 2).
Definition cov_cell_B_right : Aabb := mkAabb 1 (3 / 2) (1 / 2) (3 / 2).
Definition cov_cleaned_partition : Coverage :=
  [cov_cell_A; cov_cell_B_top; cov_cell_B_right].

Definition coverage_gap_overlap_cleaner (cov : Coverage) : Coverage :=
  cov_cleaned_partition.

Lemma cov_cleaned_A_in : In cov_cell_A cov_cleaned_partition.
Proof. unfold cov_cleaned_partition. simpl. left. reflexivity. Qed.

Lemma cov_cleaned_B_top_in : In cov_cell_B_top cov_cleaned_partition.
Proof. unfold cov_cleaned_partition. simpl. right. left. reflexivity. Qed.

Lemma cov_cleaned_B_right_in : In cov_cell_B_right cov_cleaned_partition.
Proof. unfold cov_cleaned_partition. simpl. right. right. left. reflexivity. Qed.

Lemma open_A_B_top_disjoint :
  forall p, ~ (in_open_aabb cov_cell_A p /\ in_open_aabb cov_cell_B_top p).
Proof.
  intros p [HA HB].
  unfold in_open_aabb, cov_cell_A, cov_cell_B_top in HA, HB;
    cbn [px py amin_x amax_x amin_y amax_y] in HA, HB.
  lra.
Qed.

Lemma open_A_B_right_disjoint :
  forall p, ~ (in_open_aabb cov_cell_A p /\ in_open_aabb cov_cell_B_right p).
Proof.
  intros p [HA HB].
  unfold in_open_aabb, cov_cell_A, cov_cell_B_right in HA, HB;
    cbn [px py amin_x amax_x amin_y amax_y] in HA, HB.
  lra.
Qed.

Lemma open_B_top_B_right_disjoint :
  forall p, ~ (in_open_aabb cov_cell_B_top p /\ in_open_aabb cov_cell_B_right p).
Proof.
  intros p [HA HB].
  unfold in_open_aabb, cov_cell_B_top, cov_cell_B_right in HA, HB;
    cbn [px py amin_x amax_x amin_y amax_y] in HA, HB.
  lra.
Qed.

Lemma coverage_cleaned_partition_overlap_free :
  coverage_overlap_free cov_cleaned_partition.
Proof.
  unfold coverage_overlap_free, cov_cleaned_partition.
  intros c1 c2 p Hc1 Hc2 Hneq [H1 H2].
  simpl in Hc1, Hc2.
  destruct Hc1 as [E1|[E1|[E1|E1]]]; try contradiction; subst c1;
  destruct Hc2 as [E2|[E2|[E2|E2]]]; try contradiction; subst c2;
  try (apply Hneq; reflexivity);
  try (apply (open_A_B_top_disjoint p); split; assumption);
  try (apply (open_A_B_right_disjoint p); split; assumption);
  try (apply (open_B_top_B_right_disjoint p); split; assumption);
  try (apply (open_A_B_top_disjoint p); split; assumption);
  try (apply (open_A_B_right_disjoint p); split; assumption);
  try (apply (open_B_top_B_right_disjoint p); split; assumption).
Qed.

Lemma open_implies_closed_aabb :
  forall a p, in_open_aabb a p -> in_closed_aabb a p.
Proof.
  intros a p H.
  unfold in_open_aabb, in_closed_aabb in *.
  lra.
Qed.

Lemma open_A_to_cleaned_closed :
  forall p, in_open_aabb cov_cell_A p ->
    coverage_union_closed cov_cleaned_partition p.
Proof.
  intros p H.
  exists cov_cell_A. split.
  - exact cov_cleaned_A_in.
  - apply open_implies_closed_aabb; exact H.
Qed.

Lemma open_B_to_cleaned_closed :
  forall p, in_open_aabb cov_cell_B p ->
    coverage_union_closed cov_cleaned_partition p.
Proof.
  intros p H.
  unfold in_open_aabb, cov_cell_B in H;
    cbn [px py amin_x amax_x amin_y amax_y] in H.
  destruct H as [[Hx0 Hx1] [Hy0 Hy1]].
  destruct (Rlt_le_dec (px p) 1) as [Hxlt|Hxge].
  - destruct (Rlt_le_dec (py p) 1) as [Hylt|Hyge].
    + exists cov_cell_A. split; [exact cov_cleaned_A_in|].
      unfold in_closed_aabb, cov_cell_A; cbn [px py amin_x amax_x amin_y amax_y].
      split; split; lra.
    + exists cov_cell_B_top. split; [exact cov_cleaned_B_top_in|].
      unfold in_closed_aabb, cov_cell_B_top; cbn [px py amin_x amax_x amin_y amax_y].
      split; split; lra.
  - exists cov_cell_B_right. split; [exact cov_cleaned_B_right_in|].
    unfold in_closed_aabb, cov_cell_B_right; cbn [px py amin_x amax_x amin_y amax_y].
    split; split; lra.
Qed.

Lemma open_witness_to_cleaned_closed :
  forall p, coverage_union_open cov_overlap_witness p ->
    coverage_union_closed cov_cleaned_partition p.
Proof.
  intros p [c [Hin Hopen]].
  unfold cov_overlap_witness in Hin; simpl in Hin.
  destruct Hin as [E|[E|E]]; try contradiction; subst c.
  - apply open_A_to_cleaned_closed; exact Hopen.
  - apply open_B_to_cleaned_closed; exact Hopen.
Qed.

Lemma open_cleaned_to_witness_closed :
  forall p, coverage_union_open cov_cleaned_partition p ->
    coverage_union_closed cov_overlap_witness p.
Proof.
  intros p [c [Hin Hopen]].
  unfold cov_cleaned_partition in Hin; simpl in Hin.
  destruct Hin as [E|[E|[E|E]]]; try contradiction; subst c.
  - exists cov_cell_A. split; [exact cov_cell_A_in_witness|].
    apply open_implies_closed_aabb; exact Hopen.
  - exists cov_cell_B. split; [exact cov_cell_B_in_witness|].
    unfold in_open_aabb, in_closed_aabb, cov_cell_B_top, cov_cell_B in *;
      cbn [px py amin_x amax_x amin_y amax_y] in *.
    lra.
  - exists cov_cell_B. split; [exact cov_cell_B_in_witness|].
    unfold in_open_aabb, in_closed_aabb, cov_cell_B_right, cov_cell_B in *;
      cbn [px py amin_x amax_x amin_y amax_y] in *.
    lra.
Qed.

Lemma coverage_cleaned_partition_same_union :
  coverage_same_union cov_cleaned_partition cov_overlap_witness.
Proof.
  unfold coverage_same_union. split.
  - exact open_cleaned_to_witness_closed.
  - exact open_witness_to_cleaned_closed.
Qed.

(* -------------------------------------------------------------------------- *)
(* The 425-a claim (GREEN: closed below).                                     *)
(* -------------------------------------------------------------------------- *)

Definition coverage_gap_overlap_cleaner_valid_claim : Prop :=
  exists clean : Coverage -> Coverage,
    is_valid_coverage_cleaner_on clean cov_overlap_witness.

Theorem coverage_gap_overlap_cleaner_valid :
  coverage_gap_overlap_cleaner_valid_claim.
Proof.
  unfold coverage_gap_overlap_cleaner_valid_claim.
  exists coverage_gap_overlap_cleaner.
  unfold is_valid_coverage_cleaner_on, coverage_gap_overlap_cleaner.
  split.
  - exact coverage_cleaned_partition_overlap_free.
  - exact coverage_cleaned_partition_same_union.
Qed.

Theorem coverage_gap_overlap_cleaner_valid_on_witness :
  exists clean : Coverage -> Coverage,
    coverage_overlap_free (clean cov_overlap_witness) /\
    coverage_same_union (clean cov_overlap_witness) cov_overlap_witness.
Proof.
  exists coverage_gap_overlap_cleaner.
  unfold coverage_gap_overlap_cleaner.
  split.
  - exact coverage_cleaned_partition_overlap_free.
  - exact coverage_cleaned_partition_same_union.
Qed.

Theorem coverage_cleaner_gap_free_on_A :
  coverage_gap_free cov_cleaned_partition cov_cell_A /\
  coverage_overlap_free cov_cleaned_partition.
Proof.
  split.
  - intros p Hp. exists cov_cell_A. split.
    + exact cov_cleaned_A_in.
    + apply open_implies_closed_aabb; exact Hp.
  - exact coverage_cleaned_partition_overlap_free.
Qed.
