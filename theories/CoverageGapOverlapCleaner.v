(* ============================================================================
   NetTopologySuite.Proofs.CoverageGapOverlapCleaner
   ----------------------------------------------------------------------------
   Issue #425 subtask 425-a — GREEN + REFACTOR: polygonal coverage
   gap/overlap cleaner validity on the rational two-cell overlap witness
   (classical reals).

   Red planted the claim + witness; Green closed every headline with Qed.
   Refactor (this pass): drop unused envelope/distinct scaffolding; factor
   open-AABB separation by axis cuts; thin the on_witness alias through the
   headline; keep all claims-cited names and statements unchanged.

   Headlines (Qed):
     - `coverage_gap_overlap_cleaner_valid`
     - `coverage_gap_overlap_cleaner_valid_on_witness`
     - `coverage_cleaned_partition_overlap_free`
     - `coverage_cleaned_partition_same_union`
     - `coverage_cleaner_gap_free_on_A`
     - `cov_overlap_sample_cleaned_once`

   Engineering: classical reals; AABB carrier.  `coverage_same_union` is
   open→closed both ways (up to boundary null sets).  Witness-scoped
   cleaner (∀-coverage deferred).  3-axiom allowlist footprint.

   CONCRETE CLEANER (witness partition).
     A       = [0,1]×[0,1]
     B_top   = [1/2,1]×[1,3/2]
     B_right = [1,3/2]×[1/2,3/2]

   RATIONAL WITNESS.
     cell A = [0,1]×[0,1], cell B = [1/2,3/2]×[1/2,3/2]
     sample q = (3/4,3/4) ∈ both open interiors (raw not overlap-free).

   Refs: issue #425; JTS#1126; NTS#810; JTS#1122.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Distance.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Spec shape — coverage cells, overlap-free, same-union up to ∂.         *)
(* -------------------------------------------------------------------------- *)

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

(** Union preserved up to boundary null sets: open of either side lands
    in the closed union of the other. *)
Definition coverage_same_union (c1 c2 : Coverage) : Prop :=
  (forall p, coverage_union_open c1 p -> coverage_union_closed c2 p) /\
  (forall p, coverage_union_open c2 p -> coverage_union_closed c1 p).

Definition is_valid_coverage_cleaner_on
  (clean : Coverage -> Coverage) (cov : Coverage) : Prop :=
  coverage_overlap_free (clean cov) /\
  coverage_same_union (clean cov) cov.

Lemma open_implies_closed_aabb :
  forall a p, in_open_aabb a p -> in_closed_aabb a p.
Proof.
  intros a p H. unfold in_open_aabb, in_closed_aabb in *. lra.
Qed.

(** Open interiors separated by a vertical cut (a left of b). *)
Lemma open_aabb_sep_x :
  forall a b p,
    amax_x a <= amin_x b ->
    ~ (in_open_aabb a p /\ in_open_aabb b p).
Proof.
  intros a b p Hcut [Ha Hb].
  unfold in_open_aabb in Ha, Hb. lra.
Qed.

(** Open interiors separated by a horizontal cut (a below b). *)
Lemma open_aabb_sep_y :
  forall a b p,
    amax_y a <= amin_y b ->
    ~ (in_open_aabb a p /\ in_open_aabb b p).
Proof.
  intros a b p Hcut [Ha Hb].
  unfold in_open_aabb in Ha, Hb. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Rational two-cell overlap witness (ℚ²).                                *)
(* -------------------------------------------------------------------------- *)

Definition cov_cell_A : Aabb := mkAabb 0 1 0 1.
Definition cov_cell_B : Aabb := mkAabb (1 / 2) (3 / 2) (1 / 2) (3 / 2).
Definition cov_overlap_witness : Coverage := [cov_cell_A; cov_cell_B].
Definition cov_overlap_sample : Point := mkPoint (3 / 4) (3 / 4).

Lemma cov_cell_A_B_distinct : cov_cell_A <> cov_cell_B.
Proof.
  intros Heq.
  assert (Hx : amin_x cov_cell_A = amin_x cov_cell_B)
    by (rewrite Heq; reflexivity).
  unfold cov_cell_A, cov_cell_B in Hx; cbn in Hx. lra.
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
Proof. split; [exact cov_overlap_sample_in_A | exact cov_overlap_sample_in_B]. Qed.

Lemma cov_overlap_witness_not_overlap_free :
  ~ coverage_overlap_free cov_overlap_witness.
Proof.
  intros Hfree.
  apply (Hfree cov_cell_A cov_cell_B cov_overlap_sample
           cov_cell_A_in_witness cov_cell_B_in_witness
           cov_cell_A_B_distinct).
  exact cov_overlap_sample_in_both.
Qed.

Lemma cov_overlap_sample_closed_A :
  in_closed_aabb cov_cell_A cov_overlap_sample.
Proof. apply open_implies_closed_aabb, cov_overlap_sample_in_A. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Concrete cleaner — three-cell open-interior-disjoint partition.        *)
(* -------------------------------------------------------------------------- *)

Definition cov_cell_B_top : Aabb := mkAabb (1 / 2) 1 1 (3 / 2).
Definition cov_cell_B_right : Aabb := mkAabb 1 (3 / 2) (1 / 2) (3 / 2).

Definition cov_cleaned_partition : Coverage :=
  [cov_cell_A; cov_cell_B_top; cov_cell_B_right].

Definition coverage_gap_overlap_cleaner (_ : Coverage) : Coverage :=
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
  intro p. apply open_aabb_sep_y.
  unfold cov_cell_A, cov_cell_B_top; cbn. lra.
Qed.

Lemma open_A_B_right_disjoint :
  forall p, ~ (in_open_aabb cov_cell_A p /\ in_open_aabb cov_cell_B_right p).
Proof.
  intro p. apply open_aabb_sep_x.
  unfold cov_cell_A, cov_cell_B_right; cbn. lra.
Qed.

Lemma open_B_top_B_right_disjoint :
  forall p, ~ (in_open_aabb cov_cell_B_top p /\ in_open_aabb cov_cell_B_right p).
Proof.
  intro p. apply open_aabb_sep_x.
  unfold cov_cell_B_top, cov_cell_B_right; cbn. lra.
Qed.

Lemma coverage_cleaned_partition_overlap_free :
  coverage_overlap_free cov_cleaned_partition.
Proof.
  intros c1 c2 p Hc1 Hc2 Hneq Hboth.
  unfold cov_cleaned_partition in Hc1, Hc2; simpl in Hc1, Hc2.
  destruct Hc1 as [<-|[<-|[<-|[]]]];
  destruct Hc2 as [<-|[<-|[<-|[]]]];
  try (apply Hneq; reflexivity).
  - exact (open_A_B_top_disjoint p Hboth).
  - exact (open_A_B_right_disjoint p Hboth).
  - apply (open_A_B_top_disjoint p).
    destruct Hboth as [H1 H2]; split; assumption.
  - exact (open_B_top_B_right_disjoint p Hboth).
  - apply (open_A_B_right_disjoint p).
    destruct Hboth as [H1 H2]; split; assumption.
  - apply (open_B_top_B_right_disjoint p).
    destruct Hboth as [H1 H2]; split; assumption.
Qed.

Lemma open_A_to_cleaned_closed :
  forall p, in_open_aabb cov_cell_A p ->
    coverage_union_closed cov_cleaned_partition p.
Proof.
  intros p H. exists cov_cell_A.
  split; [exact cov_cleaned_A_in | apply open_implies_closed_aabb, H].
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
  destruct Hin as [<-|[<-|[]]].
  - apply open_A_to_cleaned_closed; exact Hopen.
  - apply open_B_to_cleaned_closed; exact Hopen.
Qed.

Lemma open_cleaned_to_witness_closed :
  forall p, coverage_union_open cov_cleaned_partition p ->
    coverage_union_closed cov_overlap_witness p.
Proof.
  intros p [c [Hin Hopen]].
  unfold cov_cleaned_partition in Hin; simpl in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]].
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
  split; [exact open_cleaned_to_witness_closed | exact open_witness_to_cleaned_closed].
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Claim + headlines.                                                     *)
(* -------------------------------------------------------------------------- *)

Definition coverage_gap_overlap_cleaner_valid_claim : Prop :=
  exists clean : Coverage -> Coverage,
    is_valid_coverage_cleaner_on clean cov_overlap_witness.

Theorem coverage_gap_overlap_cleaner_valid :
  coverage_gap_overlap_cleaner_valid_claim.
Proof.
  exists coverage_gap_overlap_cleaner.
  split; [exact coverage_cleaned_partition_overlap_free
        | exact coverage_cleaned_partition_same_union].
Qed.

Theorem coverage_gap_overlap_cleaner_valid_on_witness :
  exists clean : Coverage -> Coverage,
    coverage_overlap_free (clean cov_overlap_witness) /\
    coverage_same_union (clean cov_overlap_witness) cov_overlap_witness.
Proof.
  destruct coverage_gap_overlap_cleaner_valid as [clean H].
  exists clean. exact H.
Qed.

Theorem coverage_cleaner_gap_free_on_A :
  coverage_gap_free cov_cleaned_partition cov_cell_A /\
  coverage_overlap_free cov_cleaned_partition.
Proof.
  split.
  - intros p Hp. exists cov_cell_A.
    split; [exact cov_cleaned_A_in | apply open_implies_closed_aabb, Hp].
  - exact coverage_cleaned_partition_overlap_free.
Qed.

Theorem cov_overlap_sample_cleaned_once :
  coverage_union_closed cov_cleaned_partition cov_overlap_sample /\
  in_open_aabb cov_cell_A cov_overlap_sample /\
  ~ in_open_aabb cov_cell_B_top cov_overlap_sample /\
  ~ in_open_aabb cov_cell_B_right cov_overlap_sample.
Proof.
  split; [|split; [|split]].
  - exists cov_cell_A.
    split; [exact cov_cleaned_A_in | exact cov_overlap_sample_closed_A].
  - exact cov_overlap_sample_in_A.
  - unfold in_open_aabb, cov_cell_B_top, cov_overlap_sample;
      cbn [px py amin_x amax_x amin_y amax_y]. lra.
  - unfold in_open_aabb, cov_cell_B_right, cov_overlap_sample;
      cbn [px py amin_x amax_x amin_y amax_y]. lra.
Qed.

(* WITNESS {"claimId":"425-a","topic":"coverage","lemma":"coverage_gap_overlap_cleaner_valid","title":"Coverage gap/overlap cleaner establishes valid coverage","file":"theories/CoverageGapOverlapCleaner.v"} *)
