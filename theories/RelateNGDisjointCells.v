(* ============================================================================
   NetTopologySuite.Proofs.RelateNGDisjointCells
   ----------------------------------------------------------------------------
   Issue #573 / #522 claimId 522-d: bar-2 beachhead — the exact OGC matrix
   of a separated triangle pair, in the specified-interior (gtri) vocabulary.

   True areal disjoint is FF2FF1212 (oracle `cm_matrix_disjoint_disks`).
   The designated classifier fill `aa_matrix_disjoint` is still the older
   non-OGC FFFFFFFFF pin (`ll_matrix_disjoint`).  This module names the
   OGC fill and proves the nine gtri cells on the #571 sentinel pair.
   It does NOT remint `aa_matrix_disjoint` (shared with the rect/line
   lanes) and does NOT rewire `triangle_pair_fill TPR_Disjoint`.

   Green (Qed):
     - `aa_matrix_disjoint_ogc` is FF2FF1212
     - `im_disjoint_ogc aa_matrix_disjoint_ogc` (RelateCurveMatrix pattern)
     - engine: `triangles_separated` empties II/IB/BI/BB in gtri signs
     - sentinel nine-cell theorem in gtri vocabulary (disks + segments
       from #568 / 522-g)

   Finding (Qex):
     - `~ im_disjoint aa_matrix_disjoint_ogc`
       DE9IM.v `pat_disjoint` forces EI=EB=F, so the true areal matrix
       is not a `Disjoint` witness.  That is why the classifier pointer
       stays on FFFFFFFFF.  Rewiring the pointer is later.  #575 / 522-f
       is the oracle wire token (`UNSUPPORTED`), not this remint.

   Not claimed:
     - `geom_de9im_pointset` / `cell_ok` on `point_set` (ADR-0003: do
       not wire ray parity; the sanctioned seam is RelateNGTouchCells)
     - remint of `aa_matrix_disjoint` or `triangle_pair_fill`
     - leftover certificates, classifier-order changes, ADR-0004

   Frozen anchors untouched.  Not an ADR-0004 remint.  `522-d` is the
   existing #573 ticket id.

   WITNESS topic: relate · claimId: 522-d · witness: 522-d-disjoint-ogc
   macro: relate
   lane: proofs
   issue: #573 / #522
   ADR-0004: not a remint. 522-d is the existing #573 ticket id.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

(* WITNESS {"claimId":"522-d","topic":"relate","lemma":"sentinel_disjoint_ogc_gtri_cells","title":"Nine gtri cells of FF2FF1212 on the #571 sentinel pair","file":"theories/RelateNGDisjointCells.v","witness":"522-d-disjoint-ogc","board":"#573"} *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Segment
  DE9IM RelateAreaArea RelateLineLine
  RelateCurveMatrix
  GeneralTriangleSeparation
  RelateMatrixTriangle
  RelateNGRingInclusion.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* OGC areal disjoint fill.  Not an alias of `aa_matrix_disjoint`.            *)
(* -------------------------------------------------------------------------- *)

Definition aa_matrix_disjoint_ogc : IntersectionMatrix :=
  {| im_ii := None;           im_ib := None;           im_ie := aa_dim2;
     im_bi := None;           im_bb := None;           im_be := aa_dim1;
     im_ei := aa_dim2;        im_eb := aa_dim1;        im_ee := aa_dim2 |}.

Lemma aa_matrix_disjoint_ogc_ie : im_ie aa_matrix_disjoint_ogc = Some 2%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_disjoint_ogc_ei : im_ei aa_matrix_disjoint_ogc = Some 2%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_disjoint_ogc_be : im_be aa_matrix_disjoint_ogc = Some 1%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_disjoint_ogc_eb : im_eb aa_matrix_disjoint_ogc = Some 1%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_disjoint_ogc_ee : im_ee aa_matrix_disjoint_ogc = Some 2%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_disjoint_ogc_meet_empty :
  im_ii aa_matrix_disjoint_ogc = None /\
  im_ib aa_matrix_disjoint_ogc = None /\
  im_bi aa_matrix_disjoint_ogc = None /\
  im_bb aa_matrix_disjoint_ogc = None.
Proof. repeat split; reflexivity. Qed.

Lemma aa_matrix_disjoint_ogc_im_disjoint_ogc :
  im_disjoint_ogc aa_matrix_disjoint_ogc.
Proof.
  apply im_disjoint_ogc_iff_no_meet.
  exact aa_matrix_disjoint_ogc_meet_empty.
Qed.

(* Qex: DE9IM.v `pat_disjoint` rejects the true areal matrix (EI=2, EB=1). *)
Theorem ogc_disjoint_fill_not_im_disjoint :
  ~ im_disjoint aa_matrix_disjoint_ogc.
Proof.
  unfold im_disjoint, pat_disjoint, matrix_matches, aa_matrix_disjoint_ogc.
  intros H.
  destruct H as [_ [_ [_ [_ [_ [_ [Hei _]]]]]]].
  simpl in Hei. exact Hei.
Qed.

(* Honesty: the classifier still emits the empty-IE pin. *)
Lemma triangle_disjoint_fill_ie_still_empty :
  im_ie (triangle_pair_fill TPR_Disjoint) = None.
Proof.
  rewrite triangle_pair_fill_disjoint_eq.
  exact disjoint_fill_ie_empty.
Qed.

(* -------------------------------------------------------------------------- *)
(* Engine: closed-region separation empties the four meet cells.              *)
(* Specified interior 0 < gtri ⊂ closure 0 <= gtri; specified boundary is     *)
(* gtri = 0 ⊂ closure.  Ray parity is not used.                               *)
(* -------------------------------------------------------------------------- *)

Lemma interior_in_closure : forall a1 a2 a3 pt,
  in_tri_interior a1 a2 a3 pt -> in_tri_closure a1 a2 a3 pt.
Proof. exact in_tri_interior_closure. Qed.

Lemma gtri_zero_in_closure : forall ax ay bx by_ cx cy pt,
  gtri ax ay bx by_ cx cy pt = 0 ->
  0 <= gtri ax ay bx by_ cx cy pt.
Proof. intros; lra. Qed.

Lemma separated_ii_empty :
  forall a1 a2 a3 b1 b2 b3 pt,
    triangles_separated a1 a2 a3 b1 b2 b3 ->
    ~ (in_tri_interior a1 a2 a3 pt /\ in_tri_interior b1 b2 b3 pt).
Proof.
  intros a1 a2 a3 b1 b2 b3 pt [_ [_ Hsep]] [HA HB].
  apply (Hsep pt).
  split; apply in_tri_interior_closure; assumption.
Qed.

Lemma separated_ib_empty :
  forall a1 a2 a3 b1 b2 b3 pt,
    triangles_separated a1 a2 a3 b1 b2 b3 ->
    ~ (in_tri_interior a1 a2 a3 pt /\
       gtri (px b1) (py b1) (px b2) (py b2) (px b3) (py b3) pt = 0).
Proof.
  intros a1 a2 a3 b1 b2 b3 pt [_ [_ Hsep]] [HA HB0].
  apply (Hsep pt). split.
  - apply in_tri_interior_closure; exact HA.
  - unfold in_tri_closure. apply gtri_zero_in_closure; exact HB0.
Qed.

Lemma separated_bi_empty :
  forall a1 a2 a3 b1 b2 b3 pt,
    triangles_separated a1 a2 a3 b1 b2 b3 ->
    ~ (gtri (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt = 0 /\
       in_tri_interior b1 b2 b3 pt).
Proof.
  intros a1 a2 a3 b1 b2 b3 pt [_ [_ Hsep]] [HA0 HB].
  apply (Hsep pt). split.
  - unfold in_tri_closure. apply gtri_zero_in_closure; exact HA0.
  - apply in_tri_interior_closure; exact HB.
Qed.

Lemma separated_bb_empty :
  forall a1 a2 a3 b1 b2 b3 pt,
    triangles_separated a1 a2 a3 b1 b2 b3 ->
    ~ (gtri (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt = 0 /\
       gtri (px b1) (py b1) (px b2) (py b2) (px b3) (py b3) pt = 0).
Proof.
  intros a1 a2 a3 b1 b2 b3 pt [_ [_ Hsep]] [HA0 HB0].
  apply (Hsep pt). split; unfold in_tri_closure; apply gtri_zero_in_closure;
    assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Sentinel gtri cells.  A = (0,0)(1,0)(0,1), B = (2,0)(3,0)(2,1).            *)
(* -------------------------------------------------------------------------- *)

Definition sentinel_gtri_ii (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\ 0 < gtri 2 0 3 0 2 1 p.

Definition sentinel_gtri_ib (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\ gtri 2 0 3 0 2 1 p = 0.

Definition sentinel_gtri_bi (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p = 0 /\ 0 < gtri 2 0 3 0 2 1 p.

Definition sentinel_gtri_bb (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p = 0 /\ gtri 2 0 3 0 2 1 p = 0.

Definition sentinel_gtri_ie (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\ gtri 2 0 3 0 2 1 p < 0.

Definition sentinel_gtri_ei (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\ 0 < gtri 2 0 3 0 2 1 p.

Definition sentinel_gtri_be (p : Point) : Prop :=
  between (mkPoint 0 0) (mkPoint 1 0) p /\ gtri 2 0 3 0 2 1 p < 0.

Definition sentinel_gtri_eb (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\ between (mkPoint 2 0) (mkPoint 3 0) p.

Definition sentinel_gtri_ee (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\ gtri 2 0 3 0 2 1 p < 0.

Definition gtri_cell_empty (P : Point -> Prop) : Prop :=
  forall p, ~ P p.

Definition gtri_cell_dim1 (P : Point -> Prop) : Prop :=
  exists q r, P q /\ P r /\ q <> r.

Definition gtri_cell_dim2 (P : Point -> Prop) : Prop :=
  exists c r, 0 < r /\ forall q, dist c q < r -> P q.

Lemma sentinel_ii_empty : gtri_cell_empty sentinel_gtri_ii.
Proof.
  intros p [HA HB].
  exact (separated_ii_empty
           (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
           (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) p
           dispatch_pair_separated
           (conj HA HB)).
Qed.

Lemma sentinel_ib_empty : gtri_cell_empty sentinel_gtri_ib.
Proof.
  intros p [HA HB0].
  exact (separated_ib_empty
           (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
           (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) p
           dispatch_pair_separated
           (conj HA HB0)).
Qed.

Lemma sentinel_bi_empty : gtri_cell_empty sentinel_gtri_bi.
Proof.
  intros p [HA0 HB].
  exact (separated_bi_empty
           (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
           (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) p
           dispatch_pair_separated
           (conj HA0 HB)).
Qed.

Lemma sentinel_bb_empty : gtri_cell_empty sentinel_gtri_bb.
Proof.
  intros p [HA0 HB0].
  exact (separated_bb_empty
           (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
           (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) p
           dispatch_pair_separated
           (conj HA0 HB0)).
Qed.

Lemma sentinel_ie_dim2 : gtri_cell_dim2 sentinel_gtri_ie.
Proof.
  exists sentinel_ie_center, sentinel_ie_radius.
  destruct sentinel_ie_has_dim2 as [Hr Hdisk].
  split; [exact Hr|].
  intros q Hq. apply Hdisk; exact Hq.
Qed.

(* EI disk: B's centroid (7/3, 1/3), radius 1/12. *)
Definition sentinel_ei_center : Point := mkPoint (7 / 3) (1 / 3).
Definition sentinel_ei_radius : R := 1 / 12.

Lemma sentinel_ei_coord_box :
  forall q,
    dist sentinel_ei_center q < sentinel_ei_radius ->
    9 / 4 < px q < 29 / 12 /\ 1 / 4 < py q < 5 / 12.
Proof.
  intros q Hq.
  unfold sentinel_ei_center, sentinel_ei_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint (7 / 3) (1 / 3)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint (7 / 3) (1 / 3)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (7 / 3 - px q) < 1 / 12) by lra.
  assert (Hy' : Rabs (1 / 3 - py q) < 1 / 12) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma sentinel_ei_dim2 : gtri_cell_dim2 sentinel_gtri_ei.
Proof.
  exists sentinel_ei_center, sentinel_ei_radius.
  split; [unfold sentinel_ei_radius; lra|].
  intros q Hq.
  apply sentinel_ei_coord_box in Hq.
  destruct (sentinel_A_gs q) as [HAa [HAb HAc]].
  destruct (sentinel_B_gs q) as [HBa [HBb HBc]].
  split.
  - apply Rle_lt_trans with (gsB 1 0 0 1 q).
    + apply (gtri_le_gsB 0 0 1 0 0 1 q).
    + rewrite HAb. lra.
  - apply (proj2 (gtri_pos_iff 2 0 3 0 2 1 q)).
    rewrite HBa, HBb, HBc. lra.
Qed.

Lemma sentinel_be_dim1 : gtri_cell_dim1 sentinel_gtri_be.
Proof.
  exists (mkPoint (1 / 3) 0), (mkPoint (2 / 3) 0).
  repeat split.
  - exists (1 / 3). repeat split; try lra; simpl; field.
  - destruct (sentinel_B_gs (mkPoint (1 / 3) 0)) as [_ [_ HC]].
    apply Rle_lt_trans with (gsC 2 0 2 1 (mkPoint (1 / 3) 0)).
    + apply (gtri_le_gsC 2 0 3 0 2 1 (mkPoint (1 / 3) 0)).
    + rewrite HC. simpl. lra.
  - exists (2 / 3). repeat split; try lra; simpl; field.
  - destruct (sentinel_B_gs (mkPoint (2 / 3) 0)) as [_ [_ HC]].
    apply Rle_lt_trans with (gsC 2 0 2 1 (mkPoint (2 / 3) 0)).
    + apply (gtri_le_gsC 2 0 3 0 2 1 (mkPoint (2 / 3) 0)).
    + rewrite HC. simpl. lra.
  - intros Heq. apply (f_equal px) in Heq. simpl in Heq. lra.
Qed.

Lemma sentinel_eb_dim1 : gtri_cell_dim1 sentinel_gtri_eb.
Proof.
  exists (mkPoint (7 / 3) 0), (mkPoint (8 / 3) 0).
  repeat split.
  - destruct (sentinel_A_gs (mkPoint (7 / 3) 0)) as [_ [HB _]].
    apply Rle_lt_trans with (gsB 1 0 0 1 (mkPoint (7 / 3) 0)).
    + apply (gtri_le_gsB 0 0 1 0 0 1 (mkPoint (7 / 3) 0)).
    + rewrite HB. simpl. lra.
  - exists (1 / 3). repeat split; try lra; simpl; field.
  - destruct (sentinel_A_gs (mkPoint (8 / 3) 0)) as [_ [HB _]].
    apply Rle_lt_trans with (gsB 1 0 0 1 (mkPoint (8 / 3) 0)).
    + apply (gtri_le_gsB 0 0 1 0 0 1 (mkPoint (8 / 3) 0)).
    + rewrite HB. simpl. lra.
  - exists (2 / 3). repeat split; try lra; simpl; field.
  - intros Heq. apply (f_equal px) in Heq. simpl in Heq. lra.
Qed.

Definition sentinel_ee_center : Point := mkPoint 0 (-1).
Definition sentinel_ee_radius : R := 1 / 4.

Lemma sentinel_ee_coord_box :
  forall q,
    dist sentinel_ee_center q < sentinel_ee_radius ->
    -1 / 4 < px q < 1 / 4 /\ -5 / 4 < py q < -3 / 4.
Proof.
  intros q Hq.
  unfold sentinel_ee_center, sentinel_ee_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint 0 (-1)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint 0 (-1)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (0 - px q) < 1 / 4) by lra.
  assert (Hy' : Rabs ((-1) - py q) < 1 / 4) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma sentinel_ee_dim2 : gtri_cell_dim2 sentinel_gtri_ee.
Proof.
  exists sentinel_ee_center, sentinel_ee_radius.
  split; [unfold sentinel_ee_radius; lra|].
  intros q Hq.
  apply sentinel_ee_coord_box in Hq.
  destruct (sentinel_A_gs q) as [HAa _].
  destruct (sentinel_B_gs q) as [HBa _].
  split.
  - apply Rle_lt_trans with (gsA 0 0 1 0 q).
    + apply (gtri_le_gsA 0 0 1 0 0 1 q).
    + rewrite HAa. lra.
  - apply Rle_lt_trans with (gsA 2 0 3 0 q).
    + apply (gtri_le_gsA 2 0 3 0 2 1 q).
    + rewrite HBa. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: nine gtri cells of FF2FF1212 on the #571 sentinel.               *)
(* -------------------------------------------------------------------------- *)

Theorem sentinel_disjoint_ogc_gtri_cells :
  gtri_cell_empty sentinel_gtri_ii /\
  gtri_cell_empty sentinel_gtri_ib /\
  gtri_cell_dim2 sentinel_gtri_ie /\
  gtri_cell_empty sentinel_gtri_bi /\
  gtri_cell_empty sentinel_gtri_bb /\
  gtri_cell_dim1 sentinel_gtri_be /\
  gtri_cell_dim2 sentinel_gtri_ei /\
  gtri_cell_dim1 sentinel_gtri_eb /\
  gtri_cell_dim2 sentinel_gtri_ee.
Proof.
  repeat split.
  - exact sentinel_ii_empty.
  - exact sentinel_ib_empty.
  - exact sentinel_ie_dim2.
  - exact sentinel_bi_empty.
  - exact sentinel_bb_empty.
  - exact sentinel_be_dim1.
  - exact sentinel_ei_dim2.
  - exact sentinel_eb_dim1.
  - exact sentinel_ee_dim2.
Qed.

Print Assumptions sentinel_disjoint_ogc_gtri_cells.
Print Assumptions ogc_disjoint_fill_not_im_disjoint.
Print Assumptions aa_matrix_disjoint_ogc_im_disjoint_ogc.
Print Assumptions triangle_disjoint_fill_ie_still_empty.
