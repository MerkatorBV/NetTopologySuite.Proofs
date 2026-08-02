(* ============================================================================
   nts-eval micro unit — claimId 425-a (RED)
   ----------------------------------------------------------------------------
   Polygonal coverage gap/overlap cleaner validity: after cleaning, the
   coverage is pairwise interior-disjoint (overlap-free) and its open-
   interior union matches the input (gap-free / union preserved up to
   boundary null sets).

   RED SURFACE.  The headline claim is STATED below
   (`coverage_gap_overlap_cleaner_valid_claim`) and deliberately NOT proved
   in this unit — no `Admitted` (forbidden), no `Axiom`; the claim is a
   named `Definition ... : Prop` plus Abort headlines, so the Eval → Qed
   matcher finds no Qed lemma of this statement here or in production and
   reports 425-a red.  Green must land
   `Lemma coverage_gap_overlap_cleaner_valid :
      coverage_gap_overlap_cleaner_valid_claim.`
   (or the unfolded existence statement) under classical reals in the
   production coverage lane (`theories/CoverageGapOverlapCleaner.v`),
   same WITNESS tag.

   What IS Qed here: the rational two-cell overlap witness that fixes the
   intended semantics so a wrong Green cannot close the claim vacuously —
   cell A = [0,1]×[0,1], cell B = [1/2,3/2]×[1/2,3/2], sample
   q = (3/4,3/4) in both open interiors ⇒ raw coverage is not
   overlap-free (identity is not a valid cleaner).

   WITNESS claimId: 425-a
   Lemma (Green target): coverage_gap_overlap_cleaner_valid
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

Definition coverage_gap_free (cov : Coverage) (target : Aabb) : Prop :=
  forall p : Point,
    in_open_aabb target p ->
    exists c, In c cov /\ in_closed_aabb c p.

Definition coverage_same_union (c1 c2 : Coverage) : Prop :=
  forall p : Point,
    coverage_union_open c1 p <-> coverage_union_open c2 p.

Definition is_valid_coverage_cleaner
  (clean : Coverage -> Coverage) : Prop :=
  forall cov : Coverage,
    coverage_overlap_free (clean cov) /\
    coverage_same_union (clean cov) cov.

(* -------------------------------------------------------------------------- *)
(* The 425-a claim (RED: stated, not closed).                                 *)
(* Exists a cleaner map establishing overlap-free + same-union validity.      *)
(* -------------------------------------------------------------------------- *)

Definition coverage_gap_overlap_cleaner_valid_claim : Prop :=
  exists clean : Coverage -> Coverage, is_valid_coverage_cleaner clean.

(* RED: no proof of the claim in this unit.  Green target statement:
     Lemma coverage_gap_overlap_cleaner_valid :
       coverage_gap_overlap_cleaner_valid_claim.
   in the production coverage lane, same WITNESS tag. *)

(* -------------------------------------------------------------------------- *)
(* Rational witness pins (Qed at Red).                                        *)
(* Two cells with open-interior overlap on the rational corner square.        *)
(* -------------------------------------------------------------------------- *)

Definition cov_cell_A : Aabb := mkAabb 0 1 0 1.
Definition cov_cell_B : Aabb := mkAabb (1 / 2) (3 / 2) (1 / 2) (3 / 2).
Definition cov_overlap_witness : Coverage := [cov_cell_A; cov_cell_B].
Definition cov_overlap_sample : Point := mkPoint (3 / 4) (3 / 4).
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

(** Raw coverage is not overlap-free — pins why identity fails the claim. *)
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

(* ---- Headline (claim 425-a) — Abort, not Admitted ------------------------- *)

Theorem coverage_gap_overlap_cleaner_valid :
  coverage_gap_overlap_cleaner_valid_claim.
Proof.
  (* RED #425-a: Green exhibits a sound CoverageCleaner-style map.
     Do not Admitted. *)
Abort.

Theorem coverage_gap_overlap_cleaner_valid_on_witness :
  exists clean : Coverage -> Coverage,
    coverage_overlap_free (clean cov_overlap_witness) /\
    coverage_same_union (clean cov_overlap_witness) cov_overlap_witness.
Proof.
  (* RED #425-a.  Do not Admitted. *)
Abort.

Theorem coverage_cleaner_gap_free_on_envelope :
  exists clean : Coverage -> Coverage,
    coverage_gap_free (clean cov_overlap_witness) cov_target_envelope /\
    coverage_overlap_free (clean cov_overlap_witness).
Proof.
  (* RED #425-a.  Do not Admitted. *)
Abort.
