(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLineRows
   ----------------------------------------------------------------------------
   Issue #67 S15c–S15h: line×line point-set DE-9IM bridge — exterior rows
   and per-pair test-10 fill bridges.

   Split (2026-08) from the former monolithic RelateNodingLineLine.v; the
   original §-numbers are preserved so the S15 session retros stay accurate.
   RelateNodingLineLine.v remains as the re-export umbrella.

   Romanschek EE = 2 exterior cell for any bounded segment pair; OGC
   exterior rows (no-share midpoints ⇒ IE/EI = 1-dim, endpoint exterior to
   the other segment ⇒ BE/EB = 0-dim); JTS#1175 negative (no-share ⇒
   point-set BI empty on a nominated pair); bnd×int share ⇒ BI = 0-dim;
   and the S15h per-pair 9-cell noding bridges — disjoint test-10 exterior
   rows + meet fill, Share vs Touches IB disambiguation, regime-keyed
   `line_de9im_pointset` packaging (proper-cross meet layer, overlap
   meet + EE).

   Sections: §11 (EE = 2 row), §12 (exterior rows + JTS#1175 BI negative),
   §16 (per-pair 9-cell noding bridges, S15h).

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
  RelateNodingLineLineStrata RelateNodingLineLineMeet.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §11  OGC exterior row — EE = 2 for Romanschek / bounded segment pairs.     *)
(* -------------------------------------------------------------------------- *)

Definition line_ee_dim2_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ee m) LSExt LSExt A B C D.

Theorem segments_bounded_ee_dim2_cell :
  forall A B C D,
    line_ee_dim2_cell A B C D
      {| im_ii := ll_cell_empty; im_ib := ll_cell_empty; im_ie := ll_cell_empty;
         im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_cell_empty;
         im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_dim2 |}.
Proof.
  intros A B C D.
  unfold line_ee_dim2_cell, ll_dim2. simpl.
  destruct (two_segments_exterior_meet A B C D) as [p [HA HB]].
  apply (line_cell_ok_dim2 LSExt LSExt A B C D p); assumption.
Qed.

Theorem paper_matrix_ee_dim2_cell :
  forall A B C D (m : IntersectionMatrix),
    im_ee m = Some 2%nat ->
    line_ee_dim2_cell A B C D m.
Proof.
  intros A B C D m Heq.
  unfold line_ee_dim2_cell. rewrite Heq. simpl.
  destruct (two_segments_exterior_meet A B C D) as [p [HA HB]].
  apply (line_cell_ok_dim2 LSExt LSExt A B C D p); assumption.
Qed.

Theorem paper_test10_ee_dim2_cell :
  forall A B C D, line_ee_dim2_cell A B C D ll_matrix_paper_test10.
Proof.
  intros. apply paper_matrix_ee_dim2_cell. reflexivity.
Qed.

Theorem paper_test13_ee_dim2_cell :
  forall A B C D, line_ee_dim2_cell A B C D ll_matrix_paper_test13.
Proof.
  intros. apply paper_matrix_ee_dim2_cell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §12  OGC exterior rows + JTS#1175 BI negative (no-share regime).           *)
(* -------------------------------------------------------------------------- *)

Definition line_ie_dim1_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ie m) LSInt LSExt A B C D.

Definition line_ei_dim1_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ei m) LSExt LSInt A B C D.

Definition line_be_dim0_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_be m) LSBnd LSExt A B C D.

Definition line_eb_dim0_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_eb m) LSExt LSBnd A B C D.

Definition line_bi_point_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_bi m) LSBnd LSInt A B C D.

Definition segments_bnd_int_contact (A B C D : Point) : Prop :=
  exists p : Point, seg_in_stratum LSBnd A B p /\ seg_in_stratum LSInt C D p.

Lemma int_on_cd_share :
  forall A B C D p,
    seg_in_stratum LSInt A B p ->
    between C D p ->
    segments_share A B C D.
Proof.
  intros A B C D p HAB Hbet.
  exists p. split.
  - apply between_strict_implies_between. exact HAB.
  - exact Hbet.
Qed.

Lemma int_on_ab_share :
  forall A B C D p,
    seg_in_stratum LSInt C D p ->
    between A B p ->
    segments_share A B C D.
Proof.
  intros A B C D p HCD Hbet.
  exists p. split.
  - exact Hbet.
  - apply between_strict_implies_between. exact HCD.
Qed.

Lemma no_share_interior_not_on_cd :
  forall A B C D p,
    seg_in_stratum LSInt A B p ->
    ~ segments_share A B C D ->
    ~ between C D p.
Proof.
  intros A B C D p HAB Hnoshare Hbet.
  apply Hnoshare. eauto using int_on_cd_share.
Qed.

Lemma no_share_interior_not_on_ab :
  forall A B C D p,
    seg_in_stratum LSInt C D p ->
    ~ segments_share A B C D ->
    ~ between A B p.
Proof.
  intros A B C D p HCD Hnoshare Hbet.
  apply Hnoshare. eauto using int_on_ab_share.
Qed.

Theorem no_share_midpoint_ie_cell :
  forall A B C D,
    A <> B ->
    ~ segments_share A B C D ->
    line_ie_dim1_cell A B C D
      {| im_ii := ll_cell_empty; im_ib := ll_cell_empty; im_ie := ll_dim1;
         im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_cell_empty;
         im_ei := ll_cell_empty; im_eb := ll_cell_empty; im_ee := ll_cell_empty |}.
Proof.
  intros A B C D Hne Hnoshare.
  unfold line_ie_dim1_cell. simpl.
  apply (line_cell_ok_dim1 LSInt LSExt A B C D (midpoint A B)).
  - apply between_strict_midpoint. exact Hne.
  - unfold seg_in_stratum. simpl.
    intro Hbet. apply Hnoshare.
    apply int_on_cd_share with (p := midpoint A B).
    + apply between_strict_midpoint. exact Hne.
    + exact Hbet.
Qed.

Theorem no_share_midpoint_ei_cell :
  forall A B C D,
    C <> D ->
    ~ segments_share A B C D ->
    line_ei_dim1_cell A B C D
      {| im_ii := ll_cell_empty; im_ib := ll_cell_empty; im_ie := ll_cell_empty;
         im_bi := ll_cell_empty; im_bb := ll_cell_empty; im_be := ll_cell_empty;
         im_ei := ll_dim1; im_eb := ll_cell_empty; im_ee := ll_cell_empty |}.
Proof.
  intros A B C D Hne Hnoshare.
  unfold line_ei_dim1_cell. simpl.
  apply (line_cell_ok_dim1 LSExt LSInt A B C D (midpoint C D)).
  - unfold seg_in_stratum. simpl.
    intro Hbet. apply Hnoshare.
    apply int_on_ab_share with (p := midpoint C D).
    + apply between_strict_midpoint. exact Hne.
    + exact Hbet.
  - apply between_strict_midpoint. exact Hne.
Qed.

Theorem classify_disjoint_midpoint_ie_ei_cells :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    line_ie_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_ei_dim1_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hdisj HneAB HneCD.
  unfold line_ie_dim1_cell, line_ei_dim1_cell, ll_matrix_paper_test10. simpl.
  split.
  - apply no_share_midpoint_ie_cell.
    + exact HneAB.
    + intro Hshare. apply (rejection_not_share A B C D Hdisj Hshare).
  - apply no_share_midpoint_ei_cell.
    + exact HneCD.
    + intro Hshare. apply (rejection_not_share A B C D Hdisj Hshare).
Qed.

Theorem segments_bnd_int_bi_cell :
  forall A B C D,
    segments_bnd_int_contact A B C D ->
    line_bi_point_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D [p [HAB HCD]].
  unfold line_bi_point_cell, ll_matrix_paper_test10. simpl.
  apply (line_cell_ok_dim0 LSBnd LSInt A B C D p); assumption.
Qed.

Theorem jts1175_no_share_pointset_bi_empty :
  forall A B C D,
    ~ segments_share A B C D ->
    line_cell_ok None LSBnd LSInt A B C D.
Proof.
  intros. apply (line_cell_ok_none_when LSBnd LSInt A B C D).
  eauto using no_share_no_bnd_int.
Qed.

Theorem endpoint_a_exterior_be_cell :
  forall A B C D,
    ~ between C D A ->
    line_be_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hext.
  unfold line_be_dim0_cell, ll_matrix_paper_test10. simpl.
  apply (line_cell_ok_dim0 LSBnd LSExt A B C D A).
  - apply seg_in_stratum_bnd_left.
  - unfold seg_in_stratum. simpl. exact Hext.
Qed.

Theorem endpoint_b_exterior_be_cell :
  forall A B C D,
    ~ between C D B ->
    line_be_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hext.
  unfold line_be_dim0_cell, ll_matrix_paper_test10. simpl.
  apply (line_cell_ok_dim0 LSBnd LSExt A B C D B).
  - apply seg_in_stratum_bnd_right.
  - unfold seg_in_stratum. simpl. exact Hext.
Qed.

Theorem endpoint_c_exterior_eb_cell :
  forall A B C D,
    ~ between A B C ->
    line_eb_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hext.
  unfold line_eb_dim0_cell, ll_matrix_paper_test10. simpl.
  apply (line_cell_ok_dim0 LSExt LSBnd A B C D C).
  - unfold seg_in_stratum. simpl. exact Hext.
  - apply seg_in_stratum_bnd_left.
Qed.

Theorem endpoint_d_exterior_eb_cell :
  forall A B C D,
    ~ between A B D ->
    line_eb_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hext.
  unfold line_eb_dim0_cell, ll_matrix_paper_test10. simpl.
  apply (line_cell_ok_dim0 LSExt LSBnd A B C D D).
  - unfold seg_in_stratum. simpl. exact Hext.
  - apply seg_in_stratum_bnd_right.
Qed.

Theorem paper_test10_ie_ei_ee_cells :
  forall A B C D,
    A <> B ->
    C <> D ->
    ~ segments_share A B C D ->
    line_ie_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_ei_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_ee_dim2_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D HneAB HneCD Hnoshare.
  split.
  - unfold line_ie_dim1_cell, ll_matrix_paper_test10. simpl.
    apply no_share_midpoint_ie_cell; assumption.
  - split.
    + unfold line_ei_dim1_cell, ll_matrix_paper_test10. simpl.
      apply no_share_midpoint_ei_cell; assumption.
    + apply paper_test10_ee_dim2_cell.
Qed.

(* -------------------------------------------------------------------------- *)
(* §16  Per-pair 9-cell noding bridges (S15h).                                *)
(* -------------------------------------------------------------------------- *)

Lemma no_share_endpoint_a_exterior_cd :
  forall A B C D, ~ segments_share A B C D -> ~ between C D A.
Proof.
  intros A B C D Hnoshare Hbet.
  apply Hnoshare. exists A. split.
  - apply endpoint_implies_between. apply seg_in_stratum_bnd_left.
  - exact Hbet.
Qed.

Lemma no_share_endpoint_b_exterior_cd :
  forall A B C D, ~ segments_share A B C D -> ~ between C D B.
Proof.
  intros A B C D Hnoshare Hbet.
  apply Hnoshare. exists B. split.
  - apply endpoint_implies_between. apply seg_in_stratum_bnd_right.
  - exact Hbet.
Qed.

Lemma no_share_endpoint_c_exterior_ab :
  forall A B C D, ~ segments_share A B C D -> ~ between A B C.
Proof.
  intros A B C D Hnoshare Hbet.
  apply Hnoshare. exists C. split.
  - exact Hbet.
  - apply endpoint_implies_between. apply seg_in_stratum_bnd_left.
Qed.

Lemma no_share_endpoint_d_exterior_ab :
  forall A B C D, ~ segments_share A B C D -> ~ between A B D.
Proof.
  intros A B C D Hnoshare Hbet.
  apply Hnoshare. exists D. split.
  - exact Hbet.
  - apply endpoint_implies_between. apply seg_in_stratum_bnd_right.
Qed.

Theorem separated_segments_endpoint_exterior_be_eb :
  forall A B C D,
    ~ segments_share A B C D ->
    line_be_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_eb_dim0_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hnoshare.
  split.
  - apply endpoint_a_exterior_be_cell.
    exact (no_share_endpoint_a_exterior_cd A B C D Hnoshare).
  - apply endpoint_c_exterior_eb_cell.
    exact (no_share_endpoint_c_exterior_ab A B C D Hnoshare).
Qed.

Theorem classify_disjoint_paper_test10_exterior_rows :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    line_ie_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_ei_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_be_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_eb_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_ee_dim2_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hdisj HneAB HneCD.
  assert (Hnoshare : ~ segments_share A B C D).
  { intro Hshare. apply (rejection_not_share A B C D). exact Hdisj. exact Hshare. }
  destruct (classify_disjoint_midpoint_ie_ei_cells A B C D Hdisj HneAB HneCD)
    as [Hie Hei].
  destruct (separated_segments_endpoint_exterior_be_eb A B C D Hnoshare)
    as [Hbe Heb].
  split.
  - exact Hie.
  - split.
    + exact Hei.
    + split.
      * exact Hbe.
      * split.
        -- exact Heb.
        -- apply paper_test10_ee_dim2_cell.
Qed.

Theorem classify_disjoint_test10_empty_meet_rows :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    line_cell_ok (im_ii ll_matrix_paper_test10) LSInt LSInt A B C D /\
    line_cell_ok (im_ib ll_matrix_paper_test10) LSInt LSBnd A B C D /\
    line_cell_ok (im_bb ll_matrix_paper_test10) LSBnd LSBnd A B C D.
Proof.
  intros A B C D Hdisj.
  assert (Hnoshare : ~ segments_share A B C D).
  { intro Hshare. apply (rejection_not_share A B C D). exact Hdisj. exact Hshare. }
  unfold im_ii, im_ib, im_bb, ll_matrix_paper_test10. simpl.
  repeat split.
  all: apply (line_cell_ok_none_when _ _ A B C D);
    eauto using no_share_no_int_int, no_share_no_int_bnd, no_share_no_bnd_bnd.
Qed.

Theorem classify_disjoint_line_de9im_pointset_test10 :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    line_no_ib_meet A B C D (line_pair_fill LPR_Disjoint) /\
    line_ie_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_ei_dim1_cell A B C D ll_matrix_paper_test10 /\
    line_be_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_eb_dim0_cell A B C D ll_matrix_paper_test10 /\
    line_ee_dim2_cell A B C D ll_matrix_paper_test10.
Proof.
  intros A B C D Hdisj HneAB HneCD.
  split.
  - apply classify_disjoint_line_no_ib_meet. exact Hdisj.
  - apply classify_disjoint_paper_test10_exterior_rows; assumption.
Qed.

Theorem classify_share_endpoint_only_touches_ib :
  forall A B C D,
    classify_line_pair A B C D LPR_Share ->
    segments_int_bnd_contact A B C D ->
    line_ib_point_cell A B C D ll_matrix_touches_endpoint.
Proof.
  intros A B C D _ Hcontact.
  apply segments_int_bnd_touches_ib_cell. exact Hcontact.
Qed.

Theorem classify_share_interior_vs_touches :
  forall A B C D,
    classify_line_pair A B C D LPR_Share ->
    segments_interior_share A B C D ->
    line_ii_point_cell A B C D (line_pair_fill LPR_Share).
Proof.
  intros A B C D Hshare Hint.
  apply classify_share_interior_line_ii_cell; assumption.
Qed.

Theorem classify_share_int_bnd_touches_vs_interior :
  forall A B C D,
    classify_line_pair A B C D LPR_Share ->
    segments_int_bnd_contact A B C D ->
    ~ segments_interior_share A B C D ->
    line_ib_point_cell A B C D ll_matrix_touches_endpoint.
Proof.
  intros A B C D Hshare Hcontact Hnoint.
  apply classify_share_endpoint_only_touches_ib; assumption.
Qed.

Theorem classify_proper_cross_line_de9im_pointset :
  forall A B C D,
    classify_line_pair A B C D LPR_ProperCross ->
    line_point_ii_ib_meet A B C D (line_pair_fill LPR_ProperCross).
Proof.
  intros A B C D Hcross.
  apply classify_proper_cross_line_point_ii_ib_meet. exact Hcross.
Qed.

Theorem segments_collinear_overlap_ee_dim0_cell :
  forall A B C D,
    line_cell_ok (im_ee ll_matrix_overlap_ii) LSExt LSExt A B C D.
Proof.
  intros A B C D.
  unfold im_ee, ll_matrix_overlap_ii. simpl.
  destruct (two_segments_exterior_meet A B C D) as [p [HA HB]].
  apply (line_cell_ok_dim0 LSExt LSExt A B C D p); assumption.
Qed.

Theorem classify_collinear_overlap_line_de9im_pointset :
  forall A B C D,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    C <> D ->
    line_ii_dim1_cell A B C D (line_pair_fill LPR_CollinearOverlap) /\
    line_cell_ok (im_ee (line_pair_fill LPR_CollinearOverlap)) LSExt LSExt A B C D.
Proof.
  intros A B C D Hov Hne.
  rewrite line_pair_fill_collinear_overlap_eq.
  split.
  - apply classify_collinear_overlap_line_ii_cell; assumption.
  - apply segments_collinear_overlap_ee_dim0_cell.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions paper_matrix_ee_dim2_cell.
Print Assumptions classify_disjoint_midpoint_ie_ei_cells.
Print Assumptions jts1175_no_share_pointset_bi_empty.
Print Assumptions segments_bnd_int_bi_cell.
Print Assumptions paper_test10_ie_ei_ee_cells.
Print Assumptions separated_segments_endpoint_exterior_be_eb.
Print Assumptions classify_disjoint_paper_test10_exterior_rows.
Print Assumptions classify_disjoint_line_de9im_pointset_test10.
Print Assumptions classify_share_endpoint_only_touches_ib.
Print Assumptions classify_share_interior_vs_touches.
Print Assumptions classify_proper_cross_line_de9im_pointset.
Print Assumptions classify_collinear_overlap_line_de9im_pointset.
