(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchEdgeCells
   ----------------------------------------------------------------------------
   Issue #576 / #522 claimId 522-h (touch-edge split): bar-2 beachhead for
   the shared-edge touch regime — the exact OGC matrix of the frozen
   touch pair, in the specified-interior (gtri) vocabulary.

   True areal edge-touch is FF2F11212 (disk-touch FF2F01212 with BB=1
   for a shared segment).  The designated classifier fill
   `aa_matrix_touch_vertical` is still the older FFFF1FFF2 pin (only
   BB=1, EE=2).  `touch_int_ext_exclusion` already places int(A) in
   ext(B), so IE/EI are dim-2, not empty.  This module names the OGC
   fill and proves the nine gtri cells on the frozen shared-edge pair.
   It does NOT remint `aa_matrix_touch_vertical` (shared with the rect
   lane) and does NOT rewire `triangle_pair_fill TPR_TouchEdge`.

   This is the second split of #576 (contains first as #592, then
   touch-edge, then overlap).  Overlap remains.  Ticket 576 stays open.

   Frozen anchors untouched:
     `triangles_touch_on_shared_edge`
     `touch_int_ext_exclusion`
     `touch_triangle_ii_separation_not_unconditional`

   Green (Qed):
     - `aa_matrix_touch_edge_ogc` is FF2F11212
     - `im_touches aa_matrix_touch_edge_ogc` (`pat_touches_1`)
     - engine: `touch_triangle_pair_strict_ii_no_common` empties II;
       `touch_int_ext_exclusion` empties IB and supplies IE
     - touch-pair nine-cell theorem in gtri vocabulary
     - the pair classifies `TPR_TouchEdge`

   Finding (Qex):
     - `im_ie (triangle_pair_fill TPR_TouchEdge) = None`
       while IE is dim-2.  The classifier pointer stays on FFFF1FFF2.
       Rewiring that shared pin is later.

   Not claimed:
     - `geom_de9im_pointset` / `cell_ok` on `point_set` (ADR-0003)
     - remint of `aa_matrix_touch_vertical` or `triangle_pair_fill`
     - overlap nine-cell theorem (later #576 split)
     - leftover certificates, classifier-order changes, ADR-0004

   Not an ADR-0004 remint.  `522-h` is the existing #576 ticket id
   (this letter is the touch-edge split only).

   WITNESS topic: relate · claimId: 522-h · witness: 522-h-touch-edge-bar2
   macro: relate
   lane: proofs
   issue: #576 / #522
   ADR-0004: not a remint. 522-h is the existing #576 ticket id.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

(* WITNESS {"claimId":"522-h","topic":"relate","lemma":"touch_edge_pair_ogc_gtri_cells","title":"Nine gtri cells of FF2F11212 on the shared-edge touch pair","file":"theories/RelateNGTouchEdgeCells.v","witness":"522-h-touch-edge-bar2","board":"#576"} *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Segment
  DE9IM RelateAreaArea RelateLineLine
  RelateCurveMatrix
  GeneralTriangleSeparation
  RelateMatrixTriangle
  RelateNGCore
  RelateNGTouch
  RelateNGRingInclusion
  RelateNGDisjointCells.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* OGC areal edge-touch fill.  Not an alias of `aa_matrix_touch_vertical`.    *)
(* -------------------------------------------------------------------------- *)

Definition aa_matrix_touch_edge_ogc : IntersectionMatrix :=
  {| im_ii := None;           im_ib := None;           im_ie := aa_dim2;
     im_bi := None;           im_bb := aa_dim1;        im_be := aa_dim1;
     im_ei := aa_dim2;        im_eb := aa_dim1;        im_ee := aa_dim2 |}.

Lemma aa_matrix_touch_edge_ogc_ie : im_ie aa_matrix_touch_edge_ogc = Some 2%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_touch_edge_ogc_bb : im_bb aa_matrix_touch_edge_ogc = Some 1%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_touch_edge_ogc_be : im_be aa_matrix_touch_edge_ogc = Some 1%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_touch_edge_ogc_ei : im_ei aa_matrix_touch_edge_ogc = Some 2%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_touch_edge_ogc_eb : im_eb aa_matrix_touch_edge_ogc = Some 1%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_touch_edge_ogc_ee : im_ee aa_matrix_touch_edge_ogc = Some 2%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_touch_edge_ogc_meet_empty :
  im_ii aa_matrix_touch_edge_ogc = None /\
  im_ib aa_matrix_touch_edge_ogc = None /\
  im_bi aa_matrix_touch_edge_ogc = None.
Proof. repeat split; reflexivity. Qed.

Lemma aa_matrix_touch_edge_ogc_im_touches :
  im_touches aa_matrix_touch_edge_ogc.
Proof.
  right; left.
  unfold matrix_matches, pat_touches_1, aa_matrix_touch_edge_ogc.
  simpl. repeat split.
Qed.

(* Honesty: the classifier still emits the empty-IE pin. *)
Lemma triangle_touch_fill_ie_still_empty :
  im_ie (triangle_pair_fill TPR_TouchEdge) = None.
Proof.
  rewrite triangle_pair_fill_touch_edge_eq.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Witness pair: A = (0,0)(1,0)(0,1), B = (1,0)(1,1)(0,1).                    *)
(* Shared hypotenuse (1,0)–(0,1).  Same A as the #571 sentinel.               *)
(* -------------------------------------------------------------------------- *)

Lemma touch_pair_regime :
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  exact (triangle_pair_regime_touch 0 0 1 0 0 1 1 0 1 1 0 1
           ex_triangles_touch_on_shared_edge).
Qed.

Lemma touch_B_gs :
  forall q,
    gsA 1 0 1 1 q = 1 - px q /\
    gsB 1 1 0 1 q = 1 - py q /\
    gsC 1 0 0 1 q = px q + py q - 1.
Proof. intros q; unfold gsA, gsB, gsC; split; [|split]; lra. Qed.

(* -------------------------------------------------------------------------- *)
(* Specified-interior cells of the touch pair.                                *)
(* -------------------------------------------------------------------------- *)

Definition touch_gtri_ii (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\ 0 < gtri 1 0 1 1 0 1 p.

Definition touch_gtri_ib (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\ gtri 1 0 1 1 0 1 p = 0.

Definition touch_gtri_ie (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\ gtri 1 0 1 1 0 1 p < 0.

Definition touch_gtri_bi (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p = 0 /\ 0 < gtri 1 0 1 1 0 1 p.

Definition touch_gtri_bb (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p = 0 /\ gtri 1 0 1 1 0 1 p = 0.

Definition touch_gtri_be (p : Point) : Prop :=
  between (mkPoint 0 0) (mkPoint 1 0) p /\ gtri 1 0 1 1 0 1 p < 0.

Definition touch_gtri_ei (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\ 0 < gtri 1 0 1 1 0 1 p.

Definition touch_gtri_eb (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\
  between (mkPoint 1 0) (mkPoint 1 1) p.

Definition touch_gtri_ee (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\ gtri 1 0 1 1 0 1 p < 0.

Lemma touch_ii_empty : gtri_cell_empty touch_gtri_ii.
Proof.
  intros p [HA HB].
  apply (touch_triangle_pair_strict_ii_no_common
           0 0 1 0 0 1 1 0 1 1 0 1
           ex_triangles_touch_on_shared_edge).
  exists p. split; assumption.
Qed.

Lemma touch_ib_empty : gtri_cell_empty touch_gtri_ib.
Proof.
  intros p [HA HB0].
  pose proof (touch_int_ext_exclusion
                0 0 1 0 0 1 1 0 1 1 0 1 p
                ex_triangles_touch_on_shared_edge HA).
  lra.
Qed.

Lemma touch_bi_empty : gtri_cell_empty touch_gtri_bi.
Proof.
  intros p [HA0 HB].
  apply gtri_pos_iff in HB.
  destruct HB as [_ [_ HBc]].
  destruct (touch_B_gs p) as [_ [_ HBc']].
  rewrite HBc' in HBc.
  assert (HA_nn : 0 <= gtri 0 0 1 0 0 1 p) by lra.
  apply gtri_nonneg_iff in HA_nn.
  destruct HA_nn as [_ [HAb _]].
  destruct (sentinel_A_gs p) as [_ [HAb' _]].
  rewrite HAb' in HAb.
  lra.
Qed.

Lemma touch_ie_dim2 : gtri_cell_dim2 touch_gtri_ie.
Proof.
  exists sentinel_ie_center, sentinel_ie_radius.
  split; [unfold sentinel_ie_radius; lra|].
  intros q Hq.
  split.
  - apply sentinel_A_strict_in_disk; exact Hq.
  - apply (touch_int_ext_exclusion
             0 0 1 0 0 1 1 0 1 1 0 1 q
             ex_triangles_touch_on_shared_edge).
    apply sentinel_A_strict_in_disk; exact Hq.
Qed.

(* EI disk: B's interior point (2/3, 2/3), radius 1/24. *)
Definition touch_ei_center : Point := mkPoint (2 / 3) (2 / 3).
Definition touch_ei_radius : R := 1 / 24.

Lemma touch_ei_coord_box :
  forall q,
    dist touch_ei_center q < touch_ei_radius ->
    15 / 24 < px q < 17 / 24 /\ 15 / 24 < py q < 17 / 24.
Proof.
  intros q Hq.
  unfold touch_ei_center, touch_ei_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint (2 / 3) (2 / 3)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint (2 / 3) (2 / 3)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (2 / 3 - px q) < 1 / 24) by lra.
  assert (Hy' : Rabs (2 / 3 - py q) < 1 / 24) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma touch_ei_dim2 : gtri_cell_dim2 touch_gtri_ei.
Proof.
  exists touch_ei_center, touch_ei_radius.
  split; [unfold touch_ei_radius; lra|].
  intros q Hq.
  apply touch_ei_coord_box in Hq.
  destruct (sentinel_A_gs q) as [_ [HAb _]].
  destruct (touch_B_gs q) as [HBa [HBb HBc]].
  split.
  - apply Rle_lt_trans with (gsB 1 0 0 1 q).
    + apply (gtri_le_gsB 0 0 1 0 0 1 q).
    + rewrite HAb. lra.
  - apply (proj2 (gtri_pos_iff 1 0 1 1 0 1 q)).
    rewrite HBa, HBb, HBc. lra.
Qed.

Lemma touch_bb_dim1 : gtri_cell_dim1 touch_gtri_bb.
Proof.
  exists (mkPoint (2 / 3) (1 / 3)), (mkPoint (1 / 3) (2 / 3)).
  repeat split.
  - destruct (sentinel_A_gs (mkPoint (2 / 3) (1 / 3))) as [HA [HB HC]].
    apply Rle_antisym.
    + apply Rle_trans with (gsB 1 0 0 1 (mkPoint (2 / 3) (1 / 3))).
      * apply (gtri_le_gsB 0 0 1 0 0 1 (mkPoint (2 / 3) (1 / 3))).
      * rewrite HB. simpl. lra.
    + apply gtri_nonneg_iff. rewrite HA, HB, HC. simpl. lra.
  - destruct (touch_B_gs (mkPoint (2 / 3) (1 / 3))) as [HA [HB HC]].
    apply Rle_antisym.
    + apply Rle_trans with (gsC 1 0 0 1 (mkPoint (2 / 3) (1 / 3))).
      * apply (gtri_le_gsC 1 0 1 1 0 1 (mkPoint (2 / 3) (1 / 3))).
      * rewrite HC. simpl. lra.
    + apply gtri_nonneg_iff. rewrite HA, HB, HC. simpl. lra.
  - destruct (sentinel_A_gs (mkPoint (1 / 3) (2 / 3))) as [HA [HB HC]].
    apply Rle_antisym.
    + apply Rle_trans with (gsB 1 0 0 1 (mkPoint (1 / 3) (2 / 3))).
      * apply (gtri_le_gsB 0 0 1 0 0 1 (mkPoint (1 / 3) (2 / 3))).
      * rewrite HB. simpl. lra.
    + apply gtri_nonneg_iff. rewrite HA, HB, HC. simpl. lra.
  - destruct (touch_B_gs (mkPoint (1 / 3) (2 / 3))) as [HA [HB HC]].
    apply Rle_antisym.
    + apply Rle_trans with (gsC 1 0 0 1 (mkPoint (1 / 3) (2 / 3))).
      * apply (gtri_le_gsC 1 0 1 1 0 1 (mkPoint (1 / 3) (2 / 3))).
      * rewrite HC. simpl. lra.
    + apply gtri_nonneg_iff. rewrite HA, HB, HC. simpl. lra.
  - intros Heq. apply (f_equal px) in Heq. simpl in Heq. lra.
Qed.

Lemma touch_be_dim1 : gtri_cell_dim1 touch_gtri_be.
Proof.
  exists (mkPoint (1 / 3) 0), (mkPoint (2 / 3) 0).
  repeat split.
  - exists (1 / 3). repeat split; try lra; simpl; field.
  - destruct (touch_B_gs (mkPoint (1 / 3) 0)) as [_ [_ HC]].
    apply Rle_lt_trans with (gsC 1 0 0 1 (mkPoint (1 / 3) 0)).
    + apply (gtri_le_gsC 1 0 1 1 0 1 (mkPoint (1 / 3) 0)).
    + rewrite HC. simpl. lra.
  - exists (2 / 3). repeat split; try lra; simpl; field.
  - destruct (touch_B_gs (mkPoint (2 / 3) 0)) as [_ [_ HC]].
    apply Rle_lt_trans with (gsC 1 0 0 1 (mkPoint (2 / 3) 0)).
    + apply (gtri_le_gsC 1 0 1 1 0 1 (mkPoint (2 / 3) 0)).
    + rewrite HC. simpl. lra.
  - intros Heq. apply (f_equal px) in Heq. simpl in Heq. lra.
Qed.

Lemma touch_eb_dim1 : gtri_cell_dim1 touch_gtri_eb.
Proof.
  exists (mkPoint 1 (1 / 3)), (mkPoint 1 (2 / 3)).
  repeat split.
  - destruct (sentinel_A_gs (mkPoint 1 (1 / 3))) as [_ [HB _]].
    apply Rle_lt_trans with (gsB 1 0 0 1 (mkPoint 1 (1 / 3))).
    + apply (gtri_le_gsB 0 0 1 0 0 1 (mkPoint 1 (1 / 3))).
    + rewrite HB. simpl. lra.
  - exists (1 / 3). repeat split; try lra; simpl; field.
  - destruct (sentinel_A_gs (mkPoint 1 (2 / 3))) as [_ [HB _]].
    apply Rle_lt_trans with (gsB 1 0 0 1 (mkPoint 1 (2 / 3))).
    + apply (gtri_le_gsB 0 0 1 0 0 1 (mkPoint 1 (2 / 3))).
    + rewrite HB. simpl. lra.
  - exists (2 / 3). repeat split; try lra; simpl; field.
  - intros Heq. apply (f_equal py) in Heq. simpl in Heq. lra.
Qed.

Definition touch_ee_center : Point := mkPoint 0 (-1).
Definition touch_ee_radius : R := 1 / 4.

Lemma touch_ee_coord_box :
  forall q,
    dist touch_ee_center q < touch_ee_radius ->
    -1 / 4 < px q < 1 / 4 /\ -5 / 4 < py q < -3 / 4.
Proof.
  intros q Hq.
  unfold touch_ee_center, touch_ee_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint 0 (-1)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint 0 (-1)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (0 - px q) < 1 / 4) by lra.
  assert (Hy' : Rabs ((-1) - py q) < 1 / 4) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma touch_ee_dim2 : gtri_cell_dim2 touch_gtri_ee.
Proof.
  exists touch_ee_center, touch_ee_radius.
  split; [unfold touch_ee_radius; lra|].
  intros q Hq.
  apply touch_ee_coord_box in Hq.
  destruct (sentinel_A_gs q) as [HAa _].
  destruct (touch_B_gs q) as [_ [_ HBc]].
  split.
  - apply Rle_lt_trans with (gsA 0 0 1 0 q).
    + apply (gtri_le_gsA 0 0 1 0 0 1 q).
    + rewrite HAa. lra.
  - apply Rle_lt_trans with (gsC 1 0 0 1 q).
    + apply (gtri_le_gsC 1 0 1 1 0 1 q).
    + rewrite HBc. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: nine gtri cells of FF2F11212 on the frozen touch pair.           *)
(* -------------------------------------------------------------------------- *)

Theorem touch_edge_pair_ogc_gtri_cells :
  gtri_cell_empty touch_gtri_ii /\
  gtri_cell_empty touch_gtri_ib /\
  gtri_cell_dim2 touch_gtri_ie /\
  gtri_cell_empty touch_gtri_bi /\
  gtri_cell_dim1 touch_gtri_bb /\
  gtri_cell_dim1 touch_gtri_be /\
  gtri_cell_dim2 touch_gtri_ei /\
  gtri_cell_dim1 touch_gtri_eb /\
  gtri_cell_dim2 touch_gtri_ee.
Proof.
  repeat split.
  - exact touch_ii_empty.
  - exact touch_ib_empty.
  - exact touch_ie_dim2.
  - exact touch_bi_empty.
  - exact touch_bb_dim1.
  - exact touch_be_dim1.
  - exact touch_ei_dim2.
  - exact touch_eb_dim1.
  - exact touch_ee_dim2.
Qed.

(* Qex: classifier IE is empty while the OGC cell is dim-2. *)
Theorem ogc_touch_ie_not_classifier :
  im_ie (triangle_pair_fill TPR_TouchEdge) = None /\
  gtri_cell_dim2 touch_gtri_ie.
Proof.
  split.
  - exact triangle_touch_fill_ie_still_empty.
  - exact touch_ie_dim2.
Qed.

Print Assumptions touch_edge_pair_ogc_gtri_cells.
Print Assumptions ogc_touch_ie_not_classifier.
Print Assumptions aa_matrix_touch_edge_ogc_im_touches.
Print Assumptions triangle_touch_fill_ie_still_empty.
Print Assumptions touch_pair_regime.
