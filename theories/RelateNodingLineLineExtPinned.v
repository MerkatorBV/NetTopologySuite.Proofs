(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLineExtPinned
   ----------------------------------------------------------------------------
   Issue #67 subtask 67-c (chunk S15l): line×line exterior-row
   true-dimension pinning.

   S15j (`RelateNodingLineLinePinned.v`) pins II/BB meet cells only;
   `line_cell_ok_pinned` is False on every exterior stratum.  This module
   adds the complementary pinning layer for IE / EI / BE / EB / EE.

   True dimensions (OGC lineal convention, non-degenerate no-share):
     IE = 1  (open AB minus CD),  EI = 1,  BE = 0,  EB = 0,  EE = 2.
   The S8 fill `line_pair_fill LPR_Disjoint = ll_matrix_disjoint` still
   assigns None on those cells — documented as
   `line_pair_fill_disjoint_ie_not_true_dim`.  The OGC test-10 matrix
   carries the true exterior row.

   Witness: parallel unit segments AB = (0,0)–(1,0), CD = (0,1)–(1,1).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok
   ========================================================================== *)

(* WITNESS {"claimId":"67-c","topic":"relate","lemma":"classify_disjoint_exterior_row_dim_pinned","title":"No-share line×line exterior row true-dim (IE=1,EI=1,BE=0,EB=0,EE=2)","file":"theories/RelateNodingLineLineExtPinned.v"} *)
(* mutation-seed: 713586 *)

From Stdlib Require Import Reals Lra List Lia.
Import ListNotations.
From NTS.Proofs Require Import DE9IM Distance Orientation Segment Intersect
  RelateLineLine RelateMatrixLineLine
  RelateNodingLineLineStrata RelateNodingLineLineMeet
  RelateNodingLineLineRows RelateNodingLineLinePinned.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Exterior-row pinning (IE / EI / BE / EB / EE).                             *)
(* -------------------------------------------------------------------------- *)

Definition line_cell_ok_pinned_ext (d : DimValue) (sX sY : LineStratum)
    (A B C D : Point) : Prop :=
  match sX, sY with
  | LSInt, LSExt =>
      match d with
      | None => ~ line_stratum_meet_nonempty LSInt LSExt A B C D
      | Some 1%nat => line_stratum_meet_nonempty LSInt LSExt A B C D
      | Some _ => False
      end
  | LSExt, LSInt =>
      match d with
      | None => ~ line_stratum_meet_nonempty LSExt LSInt A B C D
      | Some 1%nat => line_stratum_meet_nonempty LSExt LSInt A B C D
      | Some _ => False
      end
  | LSBnd, LSExt =>
      match d with
      | None => ~ line_stratum_meet_nonempty LSBnd LSExt A B C D
      | Some 0%nat => line_stratum_meet_nonempty LSBnd LSExt A B C D
      | Some _ => False
      end
  | LSExt, LSBnd =>
      match d with
      | None => ~ line_stratum_meet_nonempty LSExt LSBnd A B C D
      | Some 0%nat => line_stratum_meet_nonempty LSExt LSBnd A B C D
      | Some _ => False
      end
  | LSExt, LSExt =>
      match d with
      | Some 2%nat => True
      | _ => False
      end
  | _, _ => False
  end.

Definition line_cell_true_dim_ext (sX sY : LineStratum)
    (A B C D : Point) (d : DimValue) : Prop :=
  line_cell_ok_pinned_ext d sX sY A B C D.

Lemma line_cell_ok_pinned_ext_implies_ok_ie :
  forall d A B C D,
    line_cell_ok_pinned_ext d LSInt LSExt A B C D ->
    line_cell_ok d LSInt LSExt A B C D.
Proof.
  intros d A B C D Hpin.
  unfold line_cell_ok_pinned_ext in Hpin.
  destruct d as [n|].
  - destruct n as [| n1]; [contradiction Hpin|].
    destruct n1 as [| n2]; [| contradiction Hpin].
    destruct Hpin as [p [HsX HsY]].
    exact (line_cell_ok_dim1 LSInt LSExt A B C D p HsX HsY).
  - apply line_cell_ok_none_when. exact Hpin.
Qed.

Lemma line_cell_ok_pinned_ext_implies_ok_ei :
  forall d A B C D,
    line_cell_ok_pinned_ext d LSExt LSInt A B C D ->
    line_cell_ok d LSExt LSInt A B C D.
Proof.
  intros d A B C D Hpin.
  unfold line_cell_ok_pinned_ext in Hpin.
  destruct d as [n|].
  - destruct n as [| n1]; [contradiction Hpin|].
    destruct n1 as [| n2]; [| contradiction Hpin].
    destruct Hpin as [p [HsX HsY]].
    exact (line_cell_ok_dim1 LSExt LSInt A B C D p HsX HsY).
  - apply line_cell_ok_none_when. exact Hpin.
Qed.

Lemma line_cell_ok_pinned_ext_implies_ok_be :
  forall d A B C D,
    line_cell_ok_pinned_ext d LSBnd LSExt A B C D ->
    line_cell_ok d LSBnd LSExt A B C D.
Proof.
  intros d A B C D Hpin.
  unfold line_cell_ok_pinned_ext in Hpin.
  destruct d as [n|].
  - destruct n as [| n1]; [| contradiction Hpin].
    destruct Hpin as [p [HsX HsY]].
    exact (line_cell_ok_dim0 LSBnd LSExt A B C D p HsX HsY).
  - apply line_cell_ok_none_when. exact Hpin.
Qed.

Lemma line_cell_ok_pinned_ext_implies_ok_eb :
  forall d A B C D,
    line_cell_ok_pinned_ext d LSExt LSBnd A B C D ->
    line_cell_ok d LSExt LSBnd A B C D.
Proof.
  intros d A B C D Hpin.
  unfold line_cell_ok_pinned_ext in Hpin.
  destruct d as [n|].
  - destruct n as [| n1]; [| contradiction Hpin].
    destruct Hpin as [p [HsX HsY]].
    exact (line_cell_ok_dim0 LSExt LSBnd A B C D p HsX HsY).
  - apply line_cell_ok_none_when. exact Hpin.
Qed.

Lemma line_cell_ok_pinned_ext_implies_ok_ee :
  forall d A B C D,
    line_cell_ok_pinned_ext d LSExt LSExt A B C D ->
    line_cell_ok d LSExt LSExt A B C D.
Proof.
  intros d A B C D Hpin.
  unfold line_cell_ok_pinned_ext in Hpin.
  destruct d as [n|]; [| contradiction Hpin].
  destruct n as [| n1]; [contradiction Hpin|].
  destruct n1 as [| n2]; [contradiction Hpin|].
  destruct n2 as [| n3]; [| contradiction Hpin].
  destruct (two_segments_exterior_meet A B C D) as [p [HA HB]].
  exact (line_cell_ok_dim2 LSExt LSExt A B C D p HA HB).
Qed.

Theorem line_cell_ok_pinned_ext_implies_ok :
  forall d sX sY A B C D,
    line_cell_ok_pinned_ext d sX sY A B C D ->
    line_cell_ok d sX sY A B C D.
Proof.
  intros d sX sY A B C D Hpin.
  unfold line_cell_ok_pinned_ext in Hpin.
  destruct sX as [| |], sY as [| |]; try contradiction Hpin.
  - apply line_cell_ok_pinned_ext_implies_ok_ie. exact Hpin.
  - apply line_cell_ok_pinned_ext_implies_ok_be. exact Hpin.
  - apply line_cell_ok_pinned_ext_implies_ok_ei. exact Hpin.
  - apply line_cell_ok_pinned_ext_implies_ok_eb. exact Hpin.
  - apply line_cell_ok_pinned_ext_implies_ok_ee. exact Hpin.
Qed.

(* -------------------------------------------------------------------------- *)
(* True-dimension pins from geometry.                                         *)
(* -------------------------------------------------------------------------- *)

Theorem no_share_ie_dim_pinned :
  forall A B C D,
    A <> B ->
    ~ segments_share A B C D ->
    line_cell_ok_pinned_ext (Some 1%nat) LSInt LSExt A B C D.
Proof.
  intros A B C D Hne Hnoshare. simpl.
  exists (midpoint A B). split.
  - apply between_strict_midpoint. exact Hne.
  - unfold seg_in_stratum. simpl.
    apply (no_share_interior_not_on_cd A B C D (midpoint A B)).
    + apply between_strict_midpoint. exact Hne.
    + exact Hnoshare.
Qed.

Theorem no_share_ei_dim_pinned :
  forall A B C D,
    C <> D ->
    ~ segments_share A B C D ->
    line_cell_ok_pinned_ext (Some 1%nat) LSExt LSInt A B C D.
Proof.
  intros A B C D Hne Hnoshare. simpl.
  exists (midpoint C D). split.
  - unfold seg_in_stratum. simpl.
    apply (no_share_interior_not_on_ab A B C D (midpoint C D)).
    + apply between_strict_midpoint. exact Hne.
    + exact Hnoshare.
  - apply between_strict_midpoint. exact Hne.
Qed.

Theorem no_share_be_dim_pinned :
  forall A B C D,
    ~ segments_share A B C D ->
    line_cell_ok_pinned_ext (Some 0%nat) LSBnd LSExt A B C D.
Proof.
  intros A B C D Hnoshare. simpl.
  exists A. split.
  - apply seg_in_stratum_bnd_left.
  - unfold seg_in_stratum. simpl.
    exact (no_share_endpoint_a_exterior_cd A B C D Hnoshare).
Qed.

Theorem no_share_eb_dim_pinned :
  forall A B C D,
    ~ segments_share A B C D ->
    line_cell_ok_pinned_ext (Some 0%nat) LSExt LSBnd A B C D.
Proof.
  intros A B C D Hnoshare. simpl.
  exists C. split.
  - unfold seg_in_stratum. simpl.
    exact (no_share_endpoint_c_exterior_ab A B C D Hnoshare).
  - apply seg_in_stratum_bnd_left.
Qed.

Theorem bounded_ee_dim_pinned :
  forall A B C D,
    line_cell_ok_pinned_ext (Some 2%nat) LSExt LSExt A B C D.
Proof.
  intros A B C D. simpl. exact I.
Qed.

Lemma classify_disjoint_not_share :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    ~ segments_share A B C D.
Proof.
  intros A B C D Hdisj Hshare.
  apply (rejection_not_share A B C D Hdisj Hshare).
Qed.

Theorem classify_disjoint_exterior_row_dim_pinned :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    line_cell_ok_pinned_ext (Some 1%nat) LSInt LSExt A B C D /\
    line_cell_ok_pinned_ext (Some 1%nat) LSExt LSInt A B C D /\
    line_cell_ok_pinned_ext (Some 0%nat) LSBnd LSExt A B C D /\
    line_cell_ok_pinned_ext (Some 0%nat) LSExt LSBnd A B C D /\
    line_cell_ok_pinned_ext (Some 2%nat) LSExt LSExt A B C D.
Proof.
  intros A B C D Hdisj HneAB HneCD.
  pose proof (classify_disjoint_not_share A B C D Hdisj) as Hnoshare.
  split; [apply no_share_ie_dim_pinned; assumption|].
  split; [apply no_share_ei_dim_pinned; assumption|].
  split; [apply no_share_be_dim_pinned; assumption|].
  split; [apply no_share_eb_dim_pinned; assumption|].
  apply bounded_ee_dim_pinned.
Qed.

Theorem classify_disjoint_test10_exterior_row_pinned :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    A <> B ->
    C <> D ->
    line_cell_ok_pinned_ext (im_ie ll_matrix_paper_test10) LSInt LSExt A B C D /\
    line_cell_ok_pinned_ext (im_ei ll_matrix_paper_test10) LSExt LSInt A B C D /\
    line_cell_ok_pinned_ext (im_be ll_matrix_paper_test10) LSBnd LSExt A B C D /\
    line_cell_ok_pinned_ext (im_eb ll_matrix_paper_test10) LSExt LSBnd A B C D /\
    line_cell_ok_pinned_ext (im_ee ll_matrix_paper_test10) LSExt LSExt A B C D.
Proof.
  intros A B C D Hdisj HneAB HneCD.
  unfold ll_matrix_paper_test10. simpl.
  apply classify_disjoint_exterior_row_dim_pinned; assumption.
Qed.

(* S8 disjoint fill is the empty-matrix pin, not the true OGC exterior row. *)
Theorem line_pair_fill_disjoint_ie_not_true_dim :
  forall A B C D,
    A <> B ->
    classify_line_pair A B C D LPR_Disjoint ->
    ~ line_cell_ok_pinned_ext (im_ie (line_pair_fill LPR_Disjoint))
        LSInt LSExt A B C D.
Proof.
  intros A B C D Hne Hdisj Hpin.
  rewrite line_pair_fill_disjoint_eq in Hpin.
  unfold im_ie, ll_matrix_disjoint in Hpin. simpl in Hpin.
  apply Hpin.
  pose proof (classify_disjoint_not_share A B C D Hdisj) as Hnoshare.
  exact (no_share_ie_dim_pinned A B C D Hne Hnoshare).
Qed.

(* -------------------------------------------------------------------------- *)
(* Geometric witness: parallel unit segments (Romanschek / test-10 class).    *)
(* -------------------------------------------------------------------------- *)

Definition ext_pin_A : Point := mkPoint 0 0.
Definition ext_pin_B : Point := mkPoint 1 0.
Definition ext_pin_C : Point := mkPoint 0 1.
Definition ext_pin_D : Point := mkPoint 1 1.

Lemma ext_pin_AB_neq : ext_pin_A <> ext_pin_B.
Proof.
  unfold ext_pin_A, ext_pin_B. intro H. apply (f_equal px) in H. simpl in H. lra.
Qed.

Lemma ext_pin_CD_neq : ext_pin_C <> ext_pin_D.
Proof.
  unfold ext_pin_C, ext_pin_D. intro H. apply (f_equal px) in H. simpl in H. lra.
Qed.

Lemma ext_pin_disjoint :
  classify_line_pair ext_pin_A ext_pin_B ext_pin_C ext_pin_D LPR_Disjoint.
Proof.
  unfold classify_line_pair, segments_rejected,
    ext_pin_A, ext_pin_B, ext_pin_C, ext_pin_D, cross. simpl.
  left. lra.
Qed.

Example parallel_unit_segments_exterior_row_pinned :
  line_cell_ok_pinned_ext (Some 1%nat) LSInt LSExt
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
  line_cell_ok_pinned_ext (Some 1%nat) LSExt LSInt
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
  line_cell_ok_pinned_ext (Some 0%nat) LSBnd LSExt
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
  line_cell_ok_pinned_ext (Some 0%nat) LSExt LSBnd
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D /\
  line_cell_ok_pinned_ext (Some 2%nat) LSExt LSExt
    ext_pin_A ext_pin_B ext_pin_C ext_pin_D.
Proof.
  apply classify_disjoint_exterior_row_dim_pinned.
  - apply ext_pin_disjoint.
  - apply ext_pin_AB_neq.
  - apply ext_pin_CD_neq.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions line_cell_ok_pinned_ext_implies_ok.
Print Assumptions classify_disjoint_exterior_row_dim_pinned.
Print Assumptions classify_disjoint_test10_exterior_row_pinned.
Print Assumptions line_pair_fill_disjoint_ie_not_true_dim.
Print Assumptions parallel_unit_segments_exterior_row_pinned.
