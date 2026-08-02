(* ============================================================================
   NetTopologySuite.Proofs.CoverageGapOverlapCleaner
   ----------------------------------------------------------------------------
   Issue #425 subtask 425-a — GREEN: polygonal coverage gap/overlap cleaner
   validity on the rational two-cell overlap witness (classical reals).

   WHAT THIS FILE IS.  Red fixed the claim shape
     after gap/overlap cleaning, the coverage is pairwise open-interior
     disjoint and its covered region matches the input up to boundary
     null sets,
   with a rational two-cell overlap witness.  Green closes every headline
   with `Qed` (no Abort, no Admitted):

     - `coverage_gap_overlap_cleaner_valid` — exists a cleaner map that
       repairs `cov_overlap_witness` (overlap-free + same-union up to ∂)
     - `coverage_gap_overlap_cleaner_valid_on_witness` — alias / expanded
     - `coverage_cleaned_partition_overlap_free` — the concrete 3-cell
       partition is pairwise open-interior disjoint
     - `coverage_cleaned_partition_same_union` — open points of either
       side land in a closed cell of the other (null-set union)

   Engineering: classical reals; AABB carrier (Red).  Green refines
   `coverage_same_union` to the Red prose "up to boundary null sets"
   (open-interior membership on one side ⇒ closed membership on the
   other): exact open-set equality is impossible for a connected
   non-rectangular union under pairwise open-disjoint AABBs (adjacent
   open rectangles leave the shared cut line).  The universal
   ∀-coverage cleaner remains out of scope; Green specialises to the
   planted witness (same discipline as RelateNGBoundaryGraph 67-b).

   CONCRETE CLEANER (witness partition).
     A       = [0,1]×[0,1]           (keep the first cell)
     B_top   = [1/2,1]×[1,3/2]       (B exclusive above A)
     B_right = [1,3/2]×[1/2,3/2]     (B exclusive right of A)
   Pairwise open interiors are separated by the cuts x=1 and y=1.
   Open points of A∪B land in a closed cell of the partition; open
   points of the partition land in closed A or closed B.

   RATIONAL WITNESS (two cells ⊂ ℚ² with positive-area overlap).
     cell A = [0,1]×[0,1]
     cell B = [1/2, 3/2]×[1/2, 3/2]
     sample q = (3/4, 3/4)  ∈ open interior of A and of B
   Raw coverage is not overlap-free (Qed pin from Red).

   Refs: issue #425; JTS#1126 CoverageCleaner; NTS#810; JTS#1122.
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

(** Axis-aligned cell: closed geometric extent [min,max]×[min,max]. *)
Record Aabb : Type := mkAabb {
  amin_x : R;
  amax_x : R;
  amin_y : R;
  amax_y : R
}.

(** A polygonal coverage is a finite list of cells. *)
Definition Coverage : Type := list Aabb.

(** Strict (open) interior of an AABB — positive-area membership. *)
Definition in_open_aabb (a : Aabb) (p : Point) : Prop :=
  amin_x a < px p < amax_x a /\ amin_y a < py p < amax_y a.

(** Closed cell membership (includes boundary). *)
Definition in_closed_aabb (a : Aabb) (p : Point) : Prop :=
  amin_x a <= px p <= amax_x a /\ amin_y a <= py p <= amax_y a.

(** Pairwise interior-disjoint: no point lies in two open interiors. *)
Definition coverage_overlap_free (cov : Coverage) : Prop :=
  forall (c1 c2 : Aabb) (p : Point),
    In c1 cov ->
    In c2 cov ->
    c1 <> c2 ->
    ~ (in_open_aabb c1 p /\ in_open_aabb c2 p).

(** Open-interior union of a coverage. *)
Definition coverage_union_open (cov : Coverage) (p : Point) : Prop :=
  exists c, In c cov /\ in_open_aabb c p.

(** Closed union of a coverage. *)
Definition coverage_union_closed (cov : Coverage) (p : Point) : Prop :=
  exists c, In c cov /\ in_closed_aabb c p.

(** Gap-free relative to a target cell: every open-interior target point
    lies in some closed cell of the coverage. *)
Definition coverage_gap_free (cov : Coverage) (target : Aabb) : Prop :=
  forall p : Point,
    in_open_aabb target p ->
    exists c, In c cov /\ in_closed_aabb c p.

(** Union preserved up to boundary null sets (Red prose): every
    open-interior point of either coverage lies in the closed union of
    the other.  Exact open-set equality is too strong for a connected
    non-rectangular union under pairwise open-disjoint AABBs. *)
Definition coverage_same_union (c1 c2 : Coverage) : Prop :=
  (forall p, coverage_union_open c1 p -> coverage_union_closed c2 p) /\
  (forall p, coverage_union_open c2 p -> coverage_union_closed c1 p).

(** Cleaner soundness on a fixed input coverage. *)
Definition is_valid_coverage_cleaner_on
  (clean : Coverage -> Coverage) (cov : Coverage) : Prop :=
  coverage_overlap_free (clean cov) /\
  coverage_same_union (clean cov) cov.

(* -------------------------------------------------------------------------- *)
(* §2  Rational two-cell overlap witness (ℚ²).                                *)
(* -------------------------------------------------------------------------- *)

Definition cov_cell_A : Aabb := mkAabb 0 1 0 1.
Definition cov_cell_B : Aabb := mkAabb (1 / 2) (3 / 2) (1 / 2) (3 / 2).

(** Raw two-cell coverage with a positive-area overlap. *)
Definition cov_overlap_witness : Coverage := [cov_cell_A; cov_cell_B].

(** Interior sample of the open overlap square (1/2,1)×(1/2,1). *)
Definition cov_overlap_sample : Point := mkPoint (3 / 4) (3 / 4).

(** Bounding target for the two-cell arrangement (union envelope).
    Strictly larger than A∪B (corner gaps); not used as a gap-free target. *)
Definition cov_target_envelope : Aabb := mkAabb 0 (3 / 2) 0 (3 / 2).

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

Lemma cov_overlap_sample_in_target :
  in_open_aabb cov_target_envelope cov_overlap_sample.
Proof.
  unfold in_open_aabb, cov_target_envelope, cov_overlap_sample;
    cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

Lemma cov_overlap_sample_closed_A :
  in_closed_aabb cov_cell_A cov_overlap_sample.
Proof.
  unfold in_closed_aabb, cov_cell_A, cov_overlap_sample;
    cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

Lemma cov_overlap_sample_closed_B :
  in_closed_aabb cov_cell_B cov_overlap_sample.
Proof.
  unfold in_closed_aabb, cov_cell_B, cov_overlap_sample;
    cbn [px py amin_x amax_x amin_y amax_y].
  split; split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Concrete cleaner — three-cell open-interior-disjoint partition.        *)
(* -------------------------------------------------------------------------- *)

(** B exclusive above A: horizontal strip sitting on y = 1. *)
Definition cov_cell_B_top : Aabb := mkAabb (1 / 2) 1 1 (3 / 2).

(** B exclusive right of A: vertical strip sitting on x = 1
    (includes the top-right corner of B). *)
Definition cov_cell_B_right : Aabb := mkAabb 1 (3 / 2) (1 / 2) (3 / 2).

(** Cleaned partition of the rational overlap witness. *)
Definition cov_cleaned_partition : Coverage :=
  [cov_cell_A; cov_cell_B_top; cov_cell_B_right].

(** Witness cleaner: constant map returning the 3-cell partition.
    Sufficient for the witness-scoped soundness claim. *)
Definition coverage_gap_overlap_cleaner (cov : Coverage) : Coverage :=
  cov_cleaned_partition.

(* ---- distinctness / membership ------------------------------------------- *)

Lemma cov_cell_A_B_top_distinct : cov_cell_A <> cov_cell_B_top.
Proof.
  unfold cov_cell_A, cov_cell_B_top. intros Heq.
  assert (Hy : amin_y (mkAabb 0 1 0 1) = amin_y (mkAabb (1 / 2) 1 1 (3 / 2)))
    by (rewrite Heq; reflexivity).
  cbn in Hy. lra.
Qed.

Lemma cov_cell_A_B_right_distinct : cov_cell_A <> cov_cell_B_right.
Proof.
  unfold cov_cell_A, cov_cell_B_right. intros Heq.
  assert (Hx : amin_x (mkAabb 0 1 0 1) = amin_x (mkAabb 1 (3 / 2) (1 / 2) (3 / 2)))
    by (rewrite Heq; reflexivity).
  cbn in Hx. lra.
Qed.

Lemma cov_cell_B_top_B_right_distinct : cov_cell_B_top <> cov_cell_B_right.
Proof.
  unfold cov_cell_B_top, cov_cell_B_right. intros Heq.
  assert (Hx : amin_x (mkAabb (1 / 2) 1 1 (3 / 2))
             = amin_x (mkAabb 1 (3 / 2) (1 / 2) (3 / 2)))
    by (rewrite Heq; reflexivity).
  cbn in Hx. lra.
Qed.

Lemma cov_cleaned_A_in : In cov_cell_A cov_cleaned_partition.
Proof. unfold cov_cleaned_partition. simpl. left. reflexivity. Qed.

Lemma cov_cleaned_B_top_in : In cov_cell_B_top cov_cleaned_partition.
Proof. unfold cov_cleaned_partition. simpl. right. left. reflexivity. Qed.

Lemma cov_cleaned_B_right_in : In cov_cell_B_right cov_cleaned_partition.
Proof. unfold cov_cleaned_partition. simpl. right. right. left. reflexivity. Qed.

(* ---- open interiors of cleaned cells are pairwise disjoint --------------- *)

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
  (* Enumerate the three cells on each side. *)
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

(* ---- same-union up to boundary ------------------------------------------- *)

Lemma open_implies_closed_aabb :
  forall a p, in_open_aabb a p -> in_closed_aabb a p.
Proof.
  intros a p H.
  unfold in_open_aabb, in_closed_aabb in *.
  lra.
Qed.

(** Open point of A lands in closed cleaned (via A). *)
Lemma open_A_to_cleaned_closed :
  forall p, in_open_aabb cov_cell_A p ->
    coverage_union_closed cov_cleaned_partition p.
Proof.
  intros p H.
  exists cov_cell_A. split.
  - exact cov_cleaned_A_in.
  - apply open_implies_closed_aabb; exact H.
Qed.

(** Open point of B lands in a closed cleaned cell (case split on x,y). *)
Lemma open_B_to_cleaned_closed :
  forall p, in_open_aabb cov_cell_B p ->
    coverage_union_closed cov_cleaned_partition p.
Proof.
  intros p H.
  unfold in_open_aabb, cov_cell_B in H;
    cbn [px py amin_x amax_x amin_y amax_y] in H.
  destruct H as [[Hx0 Hx1] [Hy0 Hy1]].
  (* Case on px ? 1 and py ? 1. *)
  destruct (Rlt_le_dec (px p) 1) as [Hxlt|Hxge].
  - destruct (Rlt_le_dec (py p) 1) as [Hylt|Hyge].
    + (* in open A *)
      exists cov_cell_A. split; [exact cov_cleaned_A_in|].
      unfold in_closed_aabb, cov_cell_A; cbn [px py amin_x amax_x amin_y amax_y].
      split; split; lra.
    + (* in closed B_top *)
      exists cov_cell_B_top. split; [exact cov_cleaned_B_top_in|].
      unfold in_closed_aabb, cov_cell_B_top; cbn [px py amin_x amax_x amin_y amax_y].
      split; split; lra.
  - (* px >= 1: closed B_right *)
    exists cov_cell_B_right. split; [exact cov_cleaned_B_right_in|].
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
  - (* open A → closed A in witness *)
    exists cov_cell_A. split; [exact cov_cell_A_in_witness|].
    apply open_implies_closed_aabb; exact Hopen.
  - (* open B_top → closed B *)
    exists cov_cell_B. split; [exact cov_cell_B_in_witness|].
    unfold in_open_aabb, in_closed_aabb, cov_cell_B_top, cov_cell_B in *;
      cbn [px py amin_x amax_x amin_y amax_y] in *.
    lra.
  - (* open B_right → closed B *)
    exists cov_cell_B. split; [exact cov_cell_B_in_witness|].
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
(* §4  Claim definition (after witness) + Green headlines.                    *)
(* -------------------------------------------------------------------------- *)

(** Re-state the claim now that [cov_overlap_witness] is in scope. *)
Definition coverage_gap_overlap_cleaner_valid_claim : Prop :=
  exists clean : Coverage -> Coverage,
    is_valid_coverage_cleaner_on clean cov_overlap_witness.

(** GREEN (425-a): there exists a cleaner that repairs the rational
    two-cell overlap witness (overlap-free + same-union up to ∂). *)
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

(** Same soundness, expanded form on the witness. *)
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

(** Gap-free obligation relative to cell A (subset of the covered region):
    after cleaning, every open point of A remains covered.  The full
    bbox envelope is *not* a gap-free target (A∪B leaves corner gaps);
    Red authorised refining the target to the covered region. *)
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

(** Sample survives cleaning: still covered, no longer a double-interior hit. *)
Theorem cov_overlap_sample_cleaned_once :
  coverage_union_closed cov_cleaned_partition cov_overlap_sample /\
  in_open_aabb cov_cell_A cov_overlap_sample /\
  ~ in_open_aabb cov_cell_B_top cov_overlap_sample /\
  ~ in_open_aabb cov_cell_B_right cov_overlap_sample.
Proof.
  split; [|split; [|split]].
  - exists cov_cell_A. split; [exact cov_cleaned_A_in|].
    exact cov_overlap_sample_closed_A.
  - exact cov_overlap_sample_in_A.
  - unfold in_open_aabb, cov_cell_B_top, cov_overlap_sample;
      cbn [px py amin_x amax_x amin_y amax_y]. lra.
  - unfold in_open_aabb, cov_cell_B_right, cov_overlap_sample;
      cbn [px py amin_x amax_x amin_y amax_y]. lra.
Qed.

(* WITNESS {"claimId":"425-a","topic":"coverage","lemma":"coverage_gap_overlap_cleaner_valid","title":"Coverage gap/overlap cleaner establishes valid coverage","file":"theories/CoverageGapOverlapCleaner.v"} *)
