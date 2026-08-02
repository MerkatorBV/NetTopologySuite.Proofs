(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLineCollection
   ----------------------------------------------------------------------------
   Issue #67 S15f–S15i: line×line point-set DE-9IM bridge — collection layer.

   Split (2026-08) from the former monolithic RelateNodingLineLine.v; the
   original §-numbers are preserved so the S15 session retros stay accurate.
   RelateNodingLineLine.v remains as the re-export umbrella.

   JTS#1175 collection cross-product BI witness (bnd×int contact across
   segment lists) with the nominated-pair negative; collection existential
   union semantics (`line_collection_de9im_pointset`) + test-10 row
   aggregation; the `dim_value_join` max cell algebra and `matrix_dim_join`
   with fold soundness over the segment-list cross product (S15i); the
   test-10 full 9-cell `line_collection_de9im_pointset` capstone.

   Sections: §14 (JTS#1175 collection BI witness), §15 (collection union
   semantics), §17 (matrix max-join), §18 (cross-product matrix fold).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Lia.
Import ListNotations.
From NTS.Proofs Require Import DE9IM Distance Orientation Segment Intersect
  RelateLineLine RelateBoundary RelateMatrixLineLine
  RelateNodingLineLineStrata RelateNodingLineLineMeet RelateNodingLineLineRows.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §14  JTS#1175 collection BI witness + nominated-pair limitation.           *)
(* -------------------------------------------------------------------------- *)

Definition Segment2 : Type := (Point * Point)%type.

Definition line_collection_bnd_int_contact (segsA segsB : list Segment2) : Prop :=
  exists A B C D,
    In (A, B) segsA /\ In (C, D) segsB /\
    segments_bnd_int_contact A B C D.

Lemma bnd_int_contact_implies_segments_share :
  forall A B C D,
    segments_bnd_int_contact A B C D ->
    segments_share A B C D.
Proof.
  intros A B C D [p [Hbnd Hint]].
  exists p. split.
  - apply endpoint_implies_between. exact Hbnd.
  - apply between_strict_implies_between. exact Hint.
Qed.

Lemma no_share_no_bnd_int_contact :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ segments_bnd_int_contact A B C D.
Proof.
  intros A B C D Hnoshare Hcontact.
  apply Hnoshare. eauto using bnd_int_contact_implies_segments_share.
Qed.

Lemma bi_point_cell_implies_bnd_int_contact :
  forall A B C D d,
    line_cell_ok d LSBnd LSInt A B C D ->
    dim_nonempty d ->
    segments_bnd_int_contact A B C D.
Proof.
  intros A B C D d Hcell Hdn.
  destruct Hcell as [_ Hiff].
  destruct Hiff as [Hto _].
  destruct (Hto Hdn) as [p [Hbnd Hint]].
  exists p. split; assumption.
Qed.

Lemma bi_point_cell_implies_bnd_int_contact_matrix :
  forall A B C D m,
    line_bi_point_cell A B C D m ->
    dim_nonempty (im_bi m) ->
    segments_bnd_int_contact A B C D.
Proof.
  intros A B C D m Hbi Hdn.
  unfold line_bi_point_cell in Hbi.
  eauto using bi_point_cell_implies_bnd_int_contact.
Qed.

Theorem jts1175_no_share_nominated_pair_bi_empty :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ line_bi_point_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hnoshare Hbi.
  apply no_share_no_bnd_int_contact with (A := A) (B := B) (C := C) (D := D).
  - exact Hnoshare.
  - unfold line_bi_point_cell, ll_matrix_paper_test10 in Hbi.
    simpl in Hbi.
    apply (bi_point_cell_implies_bnd_int_contact A B C D (ll_dim0) Hbi).
    simpl. discriminate.
Qed.

Theorem line_collection_bnd_int_bi_cell :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    segments_bnd_int_contact A B C D ->
    line_bi_point_cell A B C D ll_matrix_paper_test10.
Proof.
  intros segsA segsB A B C D _ _ Hcontact.
  apply segments_bnd_int_bi_cell. exact Hcontact.
Qed.

Theorem jts1175_collection_bi_witness :
  forall segsA segsB,
    line_collection_bnd_int_contact segsA segsB ->
    exists A B C D,
      In (A, B) segsA /\
      In (C, D) segsB /\
      line_bi_point_cell A B C D ll_matrix_paper_test10.
Proof.
  intros segsA segsB [A [B [C [D [HinA [HinB Hcontact]]]]]].
  exists A; exists B; exists C; exists D.
  split; [exact HinA | split; [exact HinB | ]].
  apply (line_collection_bnd_int_bi_cell segsA segsB A B C D HinA HinB Hcontact).
Qed.

Theorem mod2_endpoint_bnd_int_bi_cell :
  forall A B C D,
    mod2_is_boundary_node 1 ->
    segments_bnd_int_contact A B C D ->
    line_bi_point_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D _ Hcontact.
  apply segments_bnd_int_bi_cell. exact Hcontact.
Qed.

Theorem classify_disjoint_exterior_be_eb_cells :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    ~ between C D A ->
    ~ between C D B ->
    ~ between A B C ->
    ~ between A B D ->
    line_be_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_eb_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D _ HextA HextB HextC HextD.
  split.
  - apply endpoint_a_exterior_be_cell. exact HextA.
  - apply endpoint_c_exterior_eb_cell. exact HextC.
Qed.

(* -------------------------------------------------------------------------- *)
(* §15  Collection union semantics (existential cross-product aggregation).   *)
(* -------------------------------------------------------------------------- *)

Definition line_collection_all_no_share (segsA segsB : list Segment2) : Prop :=
  forall A B C D,
    In (A, B) segsA -> In (C, D) segsB -> ~ segments_share A B C D.

Definition line_collection_cell_ok (segsA segsB : list Segment2)
    (d : DimValue) (sX sY : LineStratum) : Prop :=
  exists A B C D,
    In (A, B) segsA /\ In (C, D) segsB /\
    line_cell_ok d sX sY A B C D.

Definition line_collection_de9im_pointset (segsA segsB : list Segment2)
    (m : IntersectionMatrix) : Prop :=
  line_collection_cell_ok segsA segsB (im_ii m) LSInt LSInt /\
  line_collection_cell_ok segsA segsB (im_ib m) LSInt LSBnd /\
  line_collection_cell_ok segsA segsB (im_ie m) LSInt LSExt /\
  line_collection_cell_ok segsA segsB (im_bi m) LSBnd LSInt /\
  line_collection_cell_ok segsA segsB (im_bb m) LSBnd LSBnd /\
  line_collection_cell_ok segsA segsB (im_be m) LSBnd LSExt /\
  line_collection_cell_ok segsA segsB (im_ei m) LSExt LSInt /\
  line_collection_cell_ok segsA segsB (im_eb m) LSExt LSBnd /\
  line_collection_cell_ok segsA segsB (im_ee m) LSExt LSExt.

Definition dim_value_join (d1 d2 : DimValue) : DimValue :=
  match d1, d2 with
  | None, d => d
  | d, None => d
  | Some n1, Some n2 => Some (Nat.max n1 n2)
  end.

Lemma dim_value_join_none_left :
  forall d, dim_value_join None d = d.
Proof. intros [n|]; reflexivity. Qed.

Lemma dim_value_join_none_right :
  forall d, dim_value_join d None = d.
Proof. intros [n|]; reflexivity. Qed.

Lemma dim_value_join_commut :
  forall d1 d2, dim_value_join d1 d2 = dim_value_join d2 d1.
Proof.
  intros d1 d2. destruct d1 as [n1|], d2 as [n2|]; simpl; try reflexivity.
  f_equal. lia.
Qed.

Lemma dim_value_join_assoc :
  forall d1 d2 d3,
    dim_value_join (dim_value_join d1 d2) d3 =
    dim_value_join d1 (dim_value_join d2 d3).
Proof.
  intros d1 d2 d3.
  destruct d1 as [n1|], d2 as [n2|], d3 as [n3|]; simpl; try reflexivity.
  f_equal. lia.
Qed.

Lemma dim_value_join_idem :
  forall d, dim_value_join d d = d.
Proof.
  intros [n|]; simpl; [| reflexivity].
  f_equal. lia.
Qed.

Theorem line_collection_pair_cell_sub :
  forall segsA segsB A B C D d sX sY,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_cell_ok d sX sY A B C D ->
    line_collection_cell_ok segsA segsB d sX sY.
Proof.
  intros segsA segsB A B C D d sX sY HinA HinB Hcell.
  exists A; exists B; exists C; exists D.
  split; [exact HinA | split; [exact HinB | exact Hcell]].
Qed.

Theorem line_collection_bnd_int_bi_cell_ok :
  forall segsA segsB,
    line_collection_bnd_int_contact segsA segsB ->
    line_collection_cell_ok segsA segsB (ll_dim0) LSBnd LSInt.
Proof.
  intros segsA segsB [A [B [C [D [HinA [HinB Hcontact]]]]]].
  apply (line_collection_pair_cell_sub segsA segsB A B C D _ _ _ HinA HinB).
  apply segments_bnd_int_bi_cell in Hcontact.
  unfold line_bi_point_cell, ll_matrix_paper_test10 in Hcontact.
  simpl in Hcontact. exact Hcontact.
Qed.

Theorem line_collection_no_share_ie_cell :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    A <> B ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB (ll_dim1) LSInt LSExt.
Proof.
  intros segsA segsB A B C D HinA HinB Hne Hnoshare.
  apply (line_collection_pair_cell_sub segsA segsB A B C D _ _ _ HinA HinB).
  apply no_share_midpoint_ie_cell.
  - exact Hne.
  - apply Hnoshare; assumption.
Qed.

Theorem line_collection_no_share_ei_cell :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    C <> D ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB (ll_dim1) LSExt LSInt.
Proof.
  intros segsA segsB A B C D HinA HinB Hne Hnoshare.
  apply (line_collection_pair_cell_sub segsA segsB A B C D _ _ _ HinA HinB).
  apply no_share_midpoint_ei_cell.
  - exact Hne.
  - apply Hnoshare; assumption.
Qed.

Theorem line_collection_ee_dim2_cell :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_collection_cell_ok segsA segsB (ll_dim2) LSExt LSExt.
Proof.
  intros segsA segsB A B C D HinA HinB.
  apply (line_collection_pair_cell_sub segsA segsB A B C D _ _ _ HinA HinB).
  apply segments_bounded_ee_dim2_cell.
Qed.

Theorem line_collection_test10_de9im_rows :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    A <> B ->
    C <> D ->
    line_collection_bnd_int_contact segsA segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB (im_bi ll_matrix_paper_test10) LSBnd LSInt /\
    line_collection_cell_ok segsA segsB (im_ie ll_matrix_paper_test10) LSInt LSExt /\
    line_collection_cell_ok segsA segsB (im_ei ll_matrix_paper_test10) LSExt LSInt /\
    line_collection_cell_ok segsA segsB (im_ee ll_matrix_paper_test10) LSExt LSExt.
Proof.
  intros segsA segsB A B C D HinA HinB HneAB HneCD Hbndint Hnoshare.
  split.
  - apply line_collection_bnd_int_bi_cell_ok. exact Hbndint.
  - split.
    + apply (line_collection_no_share_ie_cell segsA segsB A B C D); assumption.
    + split.
      * apply (line_collection_no_share_ei_cell segsA segsB A B C D); assumption.
      * apply (line_collection_ee_dim2_cell segsA segsB A B C D); assumption.
Qed.

Theorem line_collection_test10_intersects :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    A <> B ->
    line_collection_all_no_share segsA segsB ->
    line_collection_bnd_int_contact segsA segsB ->
    im_intersects ll_matrix_paper_test10.
Proof.
  intros segsA segsB A B C D HinA HinB HneAB Hnoshare Hbndint.
  unfold im_intersects. right; right; left.
  apply intersects3_matches_some_ie with (n := 1%nat).
  unfold ll_matrix_paper_test10. simpl. reflexivity.
Qed.

Theorem line_collection_classify_disjoint_test10_rows :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    line_collection_bnd_int_contact segsA segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB (im_bi ll_matrix_paper_test10) LSBnd LSInt /\
    line_collection_cell_ok segsA segsB (im_ie ll_matrix_paper_test10) LSInt LSExt /\
    line_collection_cell_ok segsA segsB (im_ei ll_matrix_paper_test10) LSExt LSInt /\
    line_collection_cell_ok segsA segsB (im_ee ll_matrix_paper_test10) LSExt LSExt.
Proof.
  intros segsA segsB A B C D HinA HinB _ HneAB HneCD Hbndint Hnoshare.
  apply (line_collection_test10_de9im_rows segsA segsB A B C D); assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §17  Matrix max-join + collection cell join soundness (S15i).              *)
(* -------------------------------------------------------------------------- *)

Definition matrix_dim_join (m1 m2 : IntersectionMatrix) : IntersectionMatrix :=
  {| im_ii := dim_value_join (im_ii m1) (im_ii m2);
     im_ib := dim_value_join (im_ib m1) (im_ib m2);
     im_ie := dim_value_join (im_ie m1) (im_ie m2);
     im_bi := dim_value_join (im_bi m1) (im_bi m2);
     im_bb := dim_value_join (im_bb m1) (im_bb m2);
     im_be := dim_value_join (im_be m1) (im_be m2);
     im_ei := dim_value_join (im_ei m1) (im_ei m2);
     im_eb := dim_value_join (im_eb m1) (im_eb m2);
     im_ee := dim_value_join (im_ee m1) (im_ee m2) |}.

Lemma matrix_dim_join_commut :
  forall m1 m2, matrix_dim_join m1 m2 = matrix_dim_join m2 m1.
Proof.
  intros m1 m2.
  destruct m1 as [ii1 ib1 ie1 bi1 bb1 be1 ei1 eb1 ee1].
  destruct m2 as [ii2 ib2 ie2 bi2 bb2 be2 ei2 eb2 ee2].
  unfold matrix_dim_join. simpl. f_equal.
  all: apply dim_value_join_commut.
Qed.

Lemma matrix_dim_join_assoc :
  forall m1 m2 m3,
    matrix_dim_join (matrix_dim_join m1 m2) m3 =
    matrix_dim_join m1 (matrix_dim_join m2 m3).
Proof.
  intros m1 m2 m3.
  destruct m1 as [ii1 ib1 ie1 bi1 bb1 be1 ei1 eb1 ee1].
  destruct m2 as [ii2 ib2 ie2 bi2 bb2 be2 ei2 eb2 ee2].
  destruct m3 as [ii3 ib3 ie3 bi3 bb3 be3 ei3 eb3 ee3].
  unfold matrix_dim_join. simpl. f_equal.
  all: apply dim_value_join_assoc.
Qed.

Lemma matrix_dim_join_empty_left :
  forall m, matrix_dim_join ll_matrix_disjoint m = m.
Proof.
  intros m.
  destruct m as [ii ib ie bi bb be ei eb ee].
  unfold matrix_dim_join, ll_matrix_disjoint. simpl. f_equal.
  all: apply dim_value_join_none_left.
Qed.

Lemma matrix_dim_join_empty_right :
  forall m, matrix_dim_join m ll_matrix_disjoint = m.
Proof.
  intros m. rewrite matrix_dim_join_commut.
  apply matrix_dim_join_empty_left.
Qed.

Lemma matrix_dim_join_idem :
  forall m, matrix_dim_join m m = m.
Proof.
  intros m.
  destruct m as [ii ib ie bi bb be ei eb ee].
  unfold matrix_dim_join. simpl. f_equal.
  all: apply dim_value_join_idem.
Qed.

Lemma dim_value_ok_join :
  forall d1 d2,
    dim_value_ok d1 ->
    dim_value_ok d2 ->
    dim_value_ok (dim_value_join d1 d2).
Proof.
  intros d1 d2 Hd1 Hd2.
  destruct d1 as [n1|], d2 as [n2|]; simpl; try tauto.
  simpl. unfold dim_value_ok in Hd1, Hd2. simpl in Hd1, Hd2.
  unfold dim_value_ok. simpl.
  destruct (Nat.le_gt_cases n1 n2) as [Hle | Hgt].
  - rewrite Nat.max_r by lia. exact Hd2.
  - rewrite Nat.max_l by lia. exact Hd1.
Qed.

Lemma matrix_dim_join_ok :
  forall m1 m2, matrix_ok m1 -> matrix_ok m2 -> matrix_ok (matrix_dim_join m1 m2).
Proof.
  intros m1 m2.
  intros [Hii1 [Hib1 [Hie1 [Hbi1 [Hbb1 [Hbe1 [Hei1 [Heb1 Hee1]]]]]]]].
  intros [Hii2 [Hib2 [Hie2 [Hbi2 [Hbb2 [Hbe2 [Hei2 [Heb2 Hee2]]]]]]]].
  unfold matrix_ok, matrix_dim_join. repeat split.
  all: apply dim_value_ok_join; assumption.
Qed.

Lemma line_cell_ok_max_dim_right :
  forall n1 n2 sX sY A B C D,
    (n1 <= n2)%nat ->
    line_cell_ok (Some n2) sX sY A B C D ->
    line_cell_ok (Some (Nat.max n1 n2)) sX sY A B C D.
Proof.
  intros n1 n2 sX sY A B C D Hle [Hdok [Hdn Hex]].
  assert (Heq : Nat.max n1 n2 = n2) by lia.
  split.
  - rewrite Heq. exact Hdok.
  - rewrite Heq. split; assumption.
Qed.

Lemma line_cell_ok_max_dim_left :
  forall n1 n2 sX sY A B C D,
    (n2 <= n1)%nat ->
    line_cell_ok (Some n1) sX sY A B C D ->
    line_cell_ok (Some (Nat.max n1 n2)) sX sY A B C D.
Proof.
  intros n1 n2 sX sY A B C D Hle [Hdok [Hdn Hex]].
  assert (Heq : Nat.max n1 n2 = n1) by lia.
  split.
  - rewrite Heq. exact Hdok.
  - rewrite Heq. split; assumption.
Qed.

Theorem line_collection_cell_ok_dim_join :
  forall segsA segsB d1 d2 sX sY,
    line_collection_cell_ok segsA segsB d1 sX sY ->
    line_collection_cell_ok segsA segsB d2 sX sY ->
    line_collection_cell_ok segsA segsB (dim_value_join d1 d2) sX sY.
Proof.
  intros segsA segsB d1 d2 sX sY H1 H2.
  destruct d1 as [n1|], d2 as [n2|]; simpl.
  - destruct (Nat.le_gt_cases n1 n2) as [Hle | Hgt].
    + destruct H2 as [A [B [C [D [HinA [HinB Hcell]]]]]].
      exists A; exists B; exists C; exists D.
      split; [exact HinA | split; [exact HinB | ]].
      apply (line_cell_ok_max_dim_right n1 n2 sX sY A B C D Hle).
      exact Hcell.
    + destruct H1 as [A [B [C [D [HinA [HinB Hcell]]]]]].
      exists A; exists B; exists C; exists D.
      split; [exact HinA | split; [exact HinB | ]].
      apply (line_cell_ok_max_dim_left n1 n2 sX sY A B C D).
      * lia.
      * exact Hcell.
  - exact H1.
  - exact H2.
  - exact H1.
Qed.

Lemma line_de9im_pointset_collection_cells :
  forall segsA segsB A B C D m,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_de9im_pointset A B C D m ->
    line_collection_cell_ok segsA segsB (im_ii m) LSInt LSInt /\
    line_collection_cell_ok segsA segsB (im_ib m) LSInt LSBnd /\
    line_collection_cell_ok segsA segsB (im_ie m) LSInt LSExt /\
    line_collection_cell_ok segsA segsB (im_bi m) LSBnd LSInt /\
    line_collection_cell_ok segsA segsB (im_bb m) LSBnd LSBnd /\
    line_collection_cell_ok segsA segsB (im_be m) LSBnd LSExt /\
    line_collection_cell_ok segsA segsB (im_ei m) LSExt LSInt /\
    line_collection_cell_ok segsA segsB (im_eb m) LSExt LSBnd /\
    line_collection_cell_ok segsA segsB (im_ee m) LSExt LSExt.
Proof.
  intros segsA segsB A B C D m HinA HinB Hps.
  destruct Hps as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  repeat split.
  all: apply (line_collection_pair_cell_sub segsA segsB A B C D); assumption.
Qed.

Theorem line_collection_de9im_pointset_join :
  forall segsA segsB m1 m2,
    line_collection_de9im_pointset segsA segsB m1 ->
    line_collection_de9im_pointset segsA segsB m2 ->
    line_collection_de9im_pointset segsA segsB (matrix_dim_join m1 m2).
Proof.
  intros segsA segsB m1 m2 H1 H2.
  destruct H1 as [Hii1 [Hib1 [Hie1 [Hbi1 [Hbb1 [Hbe1 [Hei1 [Heb1 Hee1]]]]]]]].
  destruct H2 as [Hii2 [Hib2 [Hie2 [Hbi2 [Hbb2 [Hbe2 [Hei2 [Heb2 Hee2]]]]]]]].
  unfold line_collection_de9im_pointset, matrix_dim_join. simpl.
  repeat split.
  all: apply line_collection_cell_ok_dim_join; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §18  Cross-product matrix fold (S15i).                                       *)
(* -------------------------------------------------------------------------- *)

Fixpoint line_collection_matrix_fold_segsB
    (assign : Point -> Point -> Point -> Point -> IntersectionMatrix)
    (A B : Point) (segsB : list Segment2) : IntersectionMatrix :=
  match segsB with
  | nil => ll_matrix_disjoint
  | (C, D) :: rest =>
      matrix_dim_join (assign A B C D)
        (line_collection_matrix_fold_segsB assign A B rest)
  end.

Fixpoint line_collection_matrix_fold
    (assign : Point -> Point -> Point -> Point -> IntersectionMatrix)
    (segsA segsB : list Segment2) : IntersectionMatrix :=
  match segsA with
  | nil => ll_matrix_disjoint
  | (A, B) :: rest =>
      matrix_dim_join
        (line_collection_matrix_fold assign rest segsB)
        (line_collection_matrix_fold_segsB assign A B segsB)
  end.

Lemma line_collection_cell_ok_segsB_cons :
  forall segsA segsB C0 D0 d sX sY,
    line_collection_cell_ok segsA segsB d sX sY ->
    line_collection_cell_ok segsA ((C0, D0) :: segsB) d sX sY.
Proof.
  intros segsA segsB C0 D0 d sX sY H.
  destruct H as [A [B [C [D [HinA [HinB Hcell]]]]]].
  exists A; exists B; exists C; exists D.
  split.
  - exact HinA.
  - split.
    + right. exact HinB.
    + exact Hcell.
Qed.

Lemma line_collection_de9im_pointset_segsB_cons :
  forall segsA segsB C0 D0 m,
    line_collection_de9im_pointset segsA segsB m ->
    line_collection_de9im_pointset segsA ((C0, D0) :: segsB) m.
Proof.
  intros segsA segsB C0 D0 m H.
  destruct H as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  repeat split.
  all: apply line_collection_cell_ok_segsB_cons with (C0 := C0) (D0 := D0); assumption.
Qed.

Lemma line_collection_cell_ok_segsA_cons :
  forall segsA segsB A0 B0 d sX sY,
    line_collection_cell_ok segsA segsB d sX sY ->
    line_collection_cell_ok ((A0, B0) :: segsA) segsB d sX sY.
Proof.
  intros segsA segsB A0 B0 d sX sY H.
  destruct H as [A [B [C [D [HinA [HinB Hcell]]]]]].
  exists A; exists B; exists C; exists D.
  split.
  - right. exact HinA.
  - split; [exact HinB | exact Hcell].
Qed.

Lemma line_collection_de9im_pointset_segsA_cons :
  forall segsA segsB A0 B0 m,
    line_collection_de9im_pointset segsA segsB m ->
    line_collection_de9im_pointset ((A0, B0) :: segsA) segsB m.
Proof.
  intros segsA segsB A0 B0 m H.
  destruct H as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  repeat split.
  all: apply line_collection_cell_ok_segsA_cons with (A0 := A0) (B0 := B0); assumption.
Qed.

Lemma line_de9im_pointset_implies_collection :
  forall segsA segsB A B C D m,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_de9im_pointset A B C D m ->
    line_collection_de9im_pointset segsA segsB m.
Proof.
  intros segsA segsB A B C D m HinA HinB Hps.
  destruct (line_de9im_pointset_collection_cells segsA segsB A B C D m HinA HinB Hps)
    as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  repeat split; assumption.
Qed.

Lemma line_collection_matrix_fold_segsB_sound :
  forall assign segsA segsB A B,
    In (A, B) segsA ->
    (forall C D,
       In (C, D) segsB ->
       line_de9im_pointset A B C D (assign A B C D)) ->
    (exists C D, In (C, D) segsB) ->
    line_collection_de9im_pointset segsA segsB
      (line_collection_matrix_fold_segsB assign A B segsB).
Proof.
  intros assign segsA segsB A B HinA Hpair HexB.
  induction segsB as [| [C D] rest IH]; simpl.
  - destruct HexB as [C [D H]]. simpl in H. destruct H.
  - destruct HexB as [C0 [D0 HinB]].
    destruct HinB as [Hhead | Htail].
    + inversion Hhead. subst C0 D0.
      destruct rest as [| [C1 D1] rest'].
      * rewrite matrix_dim_join_empty_right.
        apply (line_de9im_pointset_implies_collection segsA ((C, D) :: nil) A B C D
            (assign A B C D)).
        exact HinA. left. reflexivity. apply Hpair. left. reflexivity.
      * apply line_collection_de9im_pointset_join.
        -- apply (line_de9im_pointset_implies_collection segsA ((C, D) :: (C1, D1) :: rest')
            A B C D (assign A B C D)).
           exact HinA. left. reflexivity. apply Hpair. left. reflexivity.
        -- apply line_collection_de9im_pointset_segsB_cons with (C0 := C) (D0 := D).
           apply IH.
           intros C' D' HinB'. apply Hpair. right. exact HinB'.
           exists C1. exists D1. left. reflexivity.
    + apply line_collection_de9im_pointset_join.
      -- apply (line_de9im_pointset_implies_collection segsA ((C, D) :: rest)
          A B C D (assign A B C D)).
         exact HinA. left. reflexivity. apply Hpair. left. reflexivity.
      -- apply line_collection_de9im_pointset_segsB_cons with (C0 := C) (D0 := D).
         apply IH.
         intros C' D' HinB'. apply Hpair. right. exact HinB'.
         exists C0. exists D0. exact Htail.
Qed.

Theorem line_collection_matrix_fold_sound :
  forall assign segsA segsB,
    (exists A B, In (A, B) segsA) ->
    (exists C D, In (C, D) segsB) ->
    (forall A B C D,
       In (A, B) segsA ->
       In (C, D) segsB ->
       line_de9im_pointset A B C D (assign A B C D)) ->
    line_collection_de9im_pointset segsA segsB
      (line_collection_matrix_fold assign segsA segsB).
Proof.
  intros assign segsA segsB HexA HexB Hpair.
  induction segsA as [| [A0 B0] rest IH]; simpl.
  - destruct HexA as [A [B H]]. simpl in H. destruct H.
  - destruct rest as [| [A1 B1] rest'].
    + simpl. rewrite matrix_dim_join_empty_left.
      apply line_collection_matrix_fold_segsB_sound.
      * left. reflexivity.
      * intros C D HinB. apply Hpair; [left; reflexivity | exact HinB].
      * exact HexB.
    + apply line_collection_de9im_pointset_join.
      * apply line_collection_de9im_pointset_segsA_cons with (A0 := A0) (B0 := B0).
        apply IH.
        -- exists A1. exists B1. left. reflexivity.
        -- intros A B C D HinA HinB.
           apply Hpair; [right; exact HinA | exact HinB].
      * apply line_collection_matrix_fold_segsB_sound.
        -- left. reflexivity.
        -- intros C D HinB. apply Hpair; [left; reflexivity | exact HinB].
        -- exact HexB.
Qed.

Theorem line_collection_de9im_pointset_implies_rows :
  forall segsA segsB m,
    line_collection_de9im_pointset segsA segsB m ->
    line_collection_cell_ok segsA segsB (im_bi m) LSBnd LSInt /\
    line_collection_cell_ok segsA segsB (im_ie m) LSInt LSExt /\
    line_collection_cell_ok segsA segsB (im_ei m) LSExt LSInt /\
    line_collection_cell_ok segsA segsB (im_ee m) LSExt LSExt.
Proof.
  intros segsA segsB m H.
  destruct H as [_ [_ [Hie [Hbi [_ [_ [Hei [_ Hee]]]]]]]].
  repeat split; assumption.
Qed.

Theorem line_collection_no_share_empty_meet_cells :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB None LSInt LSInt /\
    line_collection_cell_ok segsA segsB None LSInt LSBnd /\
    line_collection_cell_ok segsA segsB None LSBnd LSBnd.
Proof.
  intros segsA segsB A B C D HinA HinB Hnoshare.
  assert (Hns : ~ segments_share A B C D).
  { apply Hnoshare; assumption. }
  split.
  - apply (line_collection_pair_cell_sub segsA segsB A B C D None LSInt LSInt HinA HinB).
    apply (line_cell_ok_none_when LSInt LSInt A B C D).
    eauto using no_share_no_int_int.
  - split.
    + apply (line_collection_pair_cell_sub segsA segsB A B C D None LSInt LSBnd HinA HinB).
      apply (line_cell_ok_none_when LSInt LSBnd A B C D).
      eauto using no_share_no_int_bnd.
    + apply (line_collection_pair_cell_sub segsA segsB A B C D None LSBnd LSBnd HinA HinB).
      apply (line_cell_ok_none_when LSBnd LSBnd A B C D).
      eauto using no_share_no_bnd_bnd.
Qed.

Theorem line_collection_be_eb_test10_cells :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_cell_ok segsA segsB (im_be ll_matrix_paper_test10) LSBnd LSExt /\
    line_collection_cell_ok segsA segsB (im_eb ll_matrix_paper_test10) LSExt LSBnd.
Proof.
  intros segsA segsB A B C D HinA HinB Hnoshare.
  assert (Hns : ~ segments_share A B C D).
  { apply Hnoshare; assumption. }
  destruct (separated_segments_endpoint_exterior_be_eb A B C D Hns)
    as [Hbe Heb].
  split.
  - apply (line_collection_pair_cell_sub segsA segsB A B C D
      (im_be ll_matrix_paper_test10) LSBnd LSExt HinA HinB).
    unfold im_be, ll_matrix_paper_test10 in Hbe. simpl. exact Hbe.
  - apply (line_collection_pair_cell_sub segsA segsB A B C D
      (im_eb ll_matrix_paper_test10) LSExt LSBnd HinA HinB).
    unfold im_eb, ll_matrix_paper_test10 in Heb. simpl. exact Heb.
Qed.

Theorem line_collection_test10_de9im_pointset :
  forall segsA segsB A B C D,
    In (A, B) segsA ->
    In (C, D) segsB ->
    A <> B ->
    C <> D ->
    line_collection_bnd_int_contact segsA segsB ->
    line_collection_all_no_share segsA segsB ->
    line_collection_de9im_pointset segsA segsB ll_matrix_paper_test10.
Proof.
  intros segsA segsB A B C D HinA HinB HneAB HneCD Hbndint Hnoshare.
  unfold line_collection_de9im_pointset.
  destruct (line_collection_no_share_empty_meet_cells segsA segsB A B C D HinA HinB Hnoshare)
    as [Hii [Hib Hbb]].
  destruct (line_collection_test10_de9im_rows segsA segsB A B C D HinA HinB HneAB HneCD Hbndint Hnoshare)
    as [Hbi [Hie [Hei Hee]]].
  destruct (line_collection_be_eb_test10_cells segsA segsB A B C D HinA HinB Hnoshare)
    as [Hbe Heb].
  repeat split.
  - unfold im_ii, ll_matrix_paper_test10. simpl. exact Hii.
  - unfold im_ib, ll_matrix_paper_test10. simpl. exact Hib.
  - exact Hie.
  - exact Hbi.
  - unfold im_bb, ll_matrix_paper_test10. simpl. exact Hbb.
  - exact Hbe.
  - exact Hei.
  - exact Heb.
  - exact Hee.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions bnd_int_contact_implies_segments_share.
Print Assumptions jts1175_no_share_nominated_pair_bi_empty.
Print Assumptions jts1175_collection_bi_witness.
Print Assumptions mod2_endpoint_bnd_int_bi_cell.
Print Assumptions classify_disjoint_exterior_be_eb_cells.
Print Assumptions line_collection_pair_cell_sub.
Print Assumptions line_collection_bnd_int_bi_cell_ok.
Print Assumptions line_collection_test10_de9im_rows.
Print Assumptions line_collection_test10_intersects.
Print Assumptions line_collection_classify_disjoint_test10_rows.
Print Assumptions matrix_dim_join_ok.
Print Assumptions line_collection_de9im_pointset_join.
Print Assumptions line_collection_matrix_fold_sound.
Print Assumptions line_collection_test10_de9im_pointset.
