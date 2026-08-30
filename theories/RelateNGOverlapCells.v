(* ============================================================================
   NetTopologySuite.Proofs.RelateNGOverlapCells
   ----------------------------------------------------------------------------
   Issue #576 / #522 claimId 522-h (overlap split): bar-2 beachhead for
   the overlap regime — the exact OGC matrix of the #567 / #570
   overlapping triangle pair, in the specified-interior (gtri)
   vocabulary.

   True areal overlap of two crossing-boundary triangles is 212101212
   (oracle `cm_matrix_overlapping_disks`; BB=0 at the two edge
   crossings).  The designated classifier fill
   `aa_matrix_partial_overlap` is still the older 2FFF1FFF2 pin
   (empty IE/IB/BI/BE/EI/EB, and BB=1).  This module names the OGC
   fill and proves the nine gtri cells on the #567 overlap pair.  It
   does NOT remint `aa_matrix_partial_overlap` (shared with the rect
   lane) and does NOT rewire `triangle_pair_fill TPR_Overlap`.

   This is the third split of #576 (contains first as #592, then
   touch-edge as #593, then overlap).  Ticket 576 stays open.

   Green (Qed):
     - `aa_matrix_overlap_ogc` is 212101212
     - `im_overlaps aa_matrix_overlap_ogc` (`pat_overlaps_pp_aa`)
     - overlap-pair nine-cell theorem in gtri vocabulary
     - the pair classifies `TPR_Overlap` (`overlap_b` fires)

   Finding (Qex):
     - `im_ie (triangle_pair_fill TPR_Overlap) = None`
       while IE is dim-2.  The classifier pointer stays on 2FFF1FFF2
       (and still has BB=1 while BB is dim-0).  Rewiring that shared
       pin is later.

   Not claimed:
     - `geom_de9im_pointset` / `cell_ok` on `point_set` (ADR-0003)
     - remint of `aa_matrix_partial_overlap` or `triangle_pair_fill`
     - leftover certificates, classifier-order changes, ADR-0004

   Frozen anchors untouched.  Not an ADR-0004 remint.  `522-h` is the
   existing #576 ticket id (this letter is the overlap split only).

   WITNESS topic: relate · claimId: 522-h · witness: 522-h-overlap-bar2
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

(* WITNESS {"claimId":"522-h","topic":"relate","lemma":"overlap_pair_ogc_gtri_cells","title":"Nine gtri cells of 212101212 on the #567 overlap pair","file":"theories/RelateNGOverlapCells.v","witness":"522-h-overlap-bar2","board":"#576"} *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Segment
  DE9IM RelateAreaArea RelateLineLine
  RelateCurveMatrix
  GeneralTriangleSeparation
  RelateMatrixTriangle
  RelateNGCore
  RelateNGOverlap
  RelateNGRingInclusion
  RelateNGDisjointCells.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* OGC areal overlap fill.  Not an alias of `aa_matrix_partial_overlap`.      *)
(* -------------------------------------------------------------------------- *)

Definition aa_dim0 : DimValue := Some 0%nat.

Definition aa_matrix_overlap_ogc : IntersectionMatrix :=
  {| im_ii := aa_dim2;        im_ib := aa_dim1;        im_ie := aa_dim2;
     im_bi := aa_dim1;        im_bb := aa_dim0;        im_be := aa_dim1;
     im_ei := aa_dim2;        im_eb := aa_dim1;        im_ee := aa_dim2 |}.

Lemma aa_matrix_overlap_ogc_eq_cm :
  aa_matrix_overlap_ogc = cm_matrix_overlapping_disks.
Proof. reflexivity. Qed.

Lemma aa_matrix_overlap_ogc_im_overlaps :
  im_overlaps aa_matrix_overlap_ogc.
Proof.
  unfold im_overlaps, pat_overlaps_pp_aa, matrix_matches,
         aa_matrix_overlap_ogc.
  simpl. left. repeat split.
Qed.

(* Honesty: the classifier still emits the empty-IE pin. *)
Lemma triangle_overlap_fill_ie_still_empty :
  im_ie (triangle_pair_fill TPR_Overlap) = None.
Proof.
  rewrite triangle_pair_fill_overlap_eq.
  reflexivity.
Qed.

Lemma triangle_overlap_fill_bb_still_dim1 :
  im_bb (triangle_pair_fill TPR_Overlap) = Some 1%nat.
Proof.
  rewrite triangle_pair_fill_overlap_eq.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Witness pair: A = (0,0)(1,0)(0,1), B = (1/4,1/4)(5/4,1/4)(1/4,5/4).        *)
(* Same A as the #571 sentinel, so `sentinel_A_gs` applies.                   *)
(* -------------------------------------------------------------------------- *)

Lemma overlap_pair_regime :
  triangle_pair_regime 0 0 1 0 0 1 (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4)
  = TPR_Overlap.
Proof.
  apply triangle_pair_regime_overlap.
  exact overlap_ex_overlap_b.
Qed.

(* B is A translated by (1/4,1/4); slacks are the obvious shifts. *)
Lemma overlap_B_gs :
  forall q,
    gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) q = py q - 1 / 4 /\
    gsB (5 / 4) (1 / 4) (1 / 4) (5 / 4) q = 3 / 2 - px q - py q /\
    gsC (1 / 4) (1 / 4) (1 / 4) (5 / 4) q = px q - 1 / 4.
Proof. intros q; unfold gsA, gsB, gsC; split; [|split]; lra. Qed.

Definition gtri_cell_dim0 (P : Point -> Prop) : Prop :=
  exists p, P p.

(* -------------------------------------------------------------------------- *)
(* Specified-interior cells of the overlap pair.                              *)
(* -------------------------------------------------------------------------- *)

Definition overlap_gtri_ii (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\
  0 < gtri (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p.

Definition overlap_gtri_ib (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\
  gtri (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p = 0.

Definition overlap_gtri_ie (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\
  gtri (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p < 0.

Definition overlap_gtri_bi (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p = 0 /\
  0 < gtri (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p.

Definition overlap_gtri_bb (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p = 0 /\
  gtri (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p = 0.

Definition overlap_gtri_be (p : Point) : Prop :=
  between (mkPoint 0 0) (mkPoint 1 0) p /\
  gtri (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p < 0.

Definition overlap_gtri_ei (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\
  0 < gtri (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p.

Definition overlap_gtri_eb (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\
  gtri (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p = 0.

Definition overlap_gtri_ee (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\
  gtri (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p < 0.

(* II disk: lens point (3/8, 3/8), radius 1/24. *)
Definition overlap_ii_center : Point := mkPoint (3 / 8) (3 / 8).
Definition overlap_ii_radius : R := 1 / 24.

Lemma overlap_ii_coord_box :
  forall q,
    dist overlap_ii_center q < overlap_ii_radius ->
    8 / 24 < px q < 10 / 24 /\ 8 / 24 < py q < 10 / 24.
Proof.
  intros q Hq.
  unfold overlap_ii_center, overlap_ii_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint (3 / 8) (3 / 8)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint (3 / 8) (3 / 8)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (3 / 8 - px q) < 1 / 24) by lra.
  assert (Hy' : Rabs (3 / 8 - py q) < 1 / 24) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma overlap_ii_dim2 : gtri_cell_dim2 overlap_gtri_ii.
Proof.
  exists overlap_ii_center, overlap_ii_radius.
  split; [unfold overlap_ii_radius; lra|].
  intros q Hq.
  apply overlap_ii_coord_box in Hq.
  destruct (sentinel_A_gs q) as [HAa [HAb HAc]].
  destruct (overlap_B_gs q) as [HBa [HBb HBc]].
  split.
  - apply (proj2 (gtri_pos_iff 0 0 1 0 0 1 q)).
    rewrite HAa, HAb, HAc. lra.
  - apply (proj2 (gtri_pos_iff (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) q)).
    rewrite HBa, HBb, HBc. lra.
Qed.

(* IE disk: (1/8, 1/8), radius 1/16.  Same box as the contains IE. *)
Definition overlap_ie_center : Point := mkPoint (1 / 8) (1 / 8).
Definition overlap_ie_radius : R := 1 / 16.

Lemma overlap_ie_coord_box :
  forall q,
    dist overlap_ie_center q < overlap_ie_radius ->
    1 / 16 < px q < 3 / 16 /\ 1 / 16 < py q < 3 / 16.
Proof.
  intros q Hq.
  unfold overlap_ie_center, overlap_ie_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint (1 / 8) (1 / 8)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint (1 / 8) (1 / 8)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (1 / 8 - px q) < 1 / 16) by lra.
  assert (Hy' : Rabs (1 / 8 - py q) < 1 / 16) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma overlap_ie_dim2 : gtri_cell_dim2 overlap_gtri_ie.
Proof.
  exists overlap_ie_center, overlap_ie_radius.
  split; [unfold overlap_ie_radius; lra|].
  intros q Hq.
  apply overlap_ie_coord_box in Hq.
  destruct (sentinel_A_gs q) as [HAa [HAb HAc]].
  destruct (overlap_B_gs q) as [HBa _].
  split.
  - apply (proj2 (gtri_pos_iff 0 0 1 0 0 1 q)).
    rewrite HAa, HAb, HAc. lra.
  - apply Rle_lt_trans with (gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) q).
    + apply (gtri_le_gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) q).
    + rewrite HBa. lra.
Qed.

(* EI disk: (3/4, 1/2), radius 1/16.  x+y > 1 and B-slacks stay positive. *)
Definition overlap_ei_center : Point := mkPoint (3 / 4) (1 / 2).
Definition overlap_ei_radius : R := 1 / 16.

Lemma overlap_ei_coord_box :
  forall q,
    dist overlap_ei_center q < overlap_ei_radius ->
    11 / 16 < px q < 13 / 16 /\ 7 / 16 < py q < 9 / 16.
Proof.
  intros q Hq.
  unfold overlap_ei_center, overlap_ei_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint (3 / 4) (1 / 2)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint (3 / 4) (1 / 2)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (3 / 4 - px q) < 1 / 16) by lra.
  assert (Hy' : Rabs (1 / 2 - py q) < 1 / 16) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma overlap_ei_dim2 : gtri_cell_dim2 overlap_gtri_ei.
Proof.
  exists overlap_ei_center, overlap_ei_radius.
  split; [unfold overlap_ei_radius; lra|].
  intros q Hq.
  apply overlap_ei_coord_box in Hq.
  destruct (sentinel_A_gs q) as [_ [HAb _]].
  destruct (overlap_B_gs q) as [HBa [HBb HBc]].
  split.
  - apply Rle_lt_trans with (gsB 1 0 0 1 q).
    + apply (gtri_le_gsB 0 0 1 0 0 1 q).
    + rewrite HAb. lra.
  - apply (proj2 (gtri_pos_iff (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) q)).
    rewrite HBa, HBb, HBc. lra.
Qed.

(* IB: two points of B's base that sit in int(A). *)
Lemma overlap_B_gtri_zero_on_base :
  forall p,
    py p = 1 / 4 ->
    1 / 4 <= px p <= 5 / 4 ->
    gtri (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p = 0.
Proof.
  intros p Hy Hx.
  destruct (overlap_B_gs p) as [HBa [HBb HBc]].
  apply Rle_antisym.
  - apply Rle_trans with (gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) p).
    + apply (gtri_le_gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) p).
    + rewrite HBa, Hy. lra.
  - apply gtri_nonneg_iff. rewrite HBa, HBb, HBc, Hy. lra.
Qed.

Lemma overlap_ib_dim1 : gtri_cell_dim1 overlap_gtri_ib.
Proof.
  exists (mkPoint (3 / 8) (1 / 4)), (mkPoint (5 / 8) (1 / 4)).
  repeat split.
  - apply (proj2 (gtri_pos_iff 0 0 1 0 0 1 (mkPoint (3 / 8) (1 / 4)))).
    destruct (sentinel_A_gs (mkPoint (3 / 8) (1 / 4))) as [HA [HB HC]].
    rewrite HA, HB, HC. simpl. lra.
  - apply overlap_B_gtri_zero_on_base; simpl; lra.
  - apply (proj2 (gtri_pos_iff 0 0 1 0 0 1 (mkPoint (5 / 8) (1 / 4)))).
    destruct (sentinel_A_gs (mkPoint (5 / 8) (1 / 4))) as [HA [HB HC]].
    rewrite HA, HB, HC. simpl. lra.
  - apply overlap_B_gtri_zero_on_base; simpl; lra.
  - intros Heq. apply (f_equal px) in Heq. simpl in Heq. lra.
Qed.

(* BI: two points of A's hypotenuse that sit in int(B). *)
Lemma overlap_A_gtri_zero_on_hyp :
  forall p,
    px p + py p = 1 ->
    0 <= px p ->
    0 <= py p ->
    gtri 0 0 1 0 0 1 p = 0.
Proof.
  intros p Hsum Hx Hy.
  destruct (sentinel_A_gs p) as [HAa [HAb HAc]].
  apply Rle_antisym.
  - apply Rle_trans with (gsB 1 0 0 1 p).
    + apply (gtri_le_gsB 0 0 1 0 0 1 p).
    + rewrite HAb. lra.
  - apply gtri_nonneg_iff. rewrite HAa, HAb, HAc. lra.
Qed.

Lemma overlap_bi_dim1 : gtri_cell_dim1 overlap_gtri_bi.
Proof.
  exists (mkPoint (5 / 8) (3 / 8)), (mkPoint (3 / 8) (5 / 8)).
  repeat split.
  - apply overlap_A_gtri_zero_on_hyp; simpl; lra.
  - apply (proj2 (gtri_pos_iff (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4)
                    (mkPoint (5 / 8) (3 / 8)))).
    destruct (overlap_B_gs (mkPoint (5 / 8) (3 / 8))) as [HA [HB HC]].
    rewrite HA, HB, HC. simpl. lra.
  - apply overlap_A_gtri_zero_on_hyp; simpl; lra.
  - apply (proj2 (gtri_pos_iff (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4)
                    (mkPoint (3 / 8) (5 / 8)))).
    destruct (overlap_B_gs (mkPoint (3 / 8) (5 / 8))) as [HA [HB HC]].
    rewrite HA, HB, HC. simpl. lra.
  - intros Heq. apply (f_equal px) in Heq. simpl in Heq. lra.
Qed.

(* BB dim-0: the crossing (3/4, 1/4) of A's hypotenuse and B's base. *)
Lemma overlap_bb_dim0 : gtri_cell_dim0 overlap_gtri_bb.
Proof.
  exists (mkPoint (3 / 4) (1 / 4)).
  split.
  - apply overlap_A_gtri_zero_on_hyp; simpl; lra.
  - apply overlap_B_gtri_zero_on_base; simpl; lra.
Qed.

Lemma overlap_be_dim1 : gtri_cell_dim1 overlap_gtri_be.
Proof.
  exists (mkPoint (1 / 3) 0), (mkPoint (2 / 3) 0).
  repeat split.
  - exists (1 / 3). repeat split; try lra; simpl; field.
  - destruct (overlap_B_gs (mkPoint (1 / 3) 0)) as [HA _].
    apply Rle_lt_trans with (gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) (mkPoint (1 / 3) 0)).
    + apply (gtri_le_gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4)
               (mkPoint (1 / 3) 0)).
    + rewrite HA. simpl. lra.
  - exists (2 / 3). repeat split; try lra; simpl; field.
  - destruct (overlap_B_gs (mkPoint (2 / 3) 0)) as [HA _].
    apply Rle_lt_trans with (gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) (mkPoint (2 / 3) 0)).
    + apply (gtri_le_gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4)
               (mkPoint (2 / 3) 0)).
    + rewrite HA. simpl. lra.
  - intros Heq. apply (f_equal px) in Heq. simpl in Heq. lra.
Qed.

(* EB: two points of B's base that sit in ext(A) (x+y > 1). *)
Lemma overlap_eb_dim1 : gtri_cell_dim1 overlap_gtri_eb.
Proof.
  exists (mkPoint 1 (1 / 4)), (mkPoint (9 / 8) (1 / 4)).
  repeat split.
  - destruct (sentinel_A_gs (mkPoint 1 (1 / 4))) as [_ [HB _]].
    apply Rle_lt_trans with (gsB 1 0 0 1 (mkPoint 1 (1 / 4))).
    + apply (gtri_le_gsB 0 0 1 0 0 1 (mkPoint 1 (1 / 4))).
    + rewrite HB. simpl. lra.
  - apply overlap_B_gtri_zero_on_base; simpl; lra.
  - destruct (sentinel_A_gs (mkPoint (9 / 8) (1 / 4))) as [_ [HB _]].
    apply Rle_lt_trans with (gsB 1 0 0 1 (mkPoint (9 / 8) (1 / 4))).
    + apply (gtri_le_gsB 0 0 1 0 0 1 (mkPoint (9 / 8) (1 / 4))).
    + rewrite HB. simpl. lra.
  - apply overlap_B_gtri_zero_on_base; simpl; lra.
  - intros Heq. apply (f_equal px) in Heq. simpl in Heq. lra.
Qed.

(* EE disk: (0, -1), radius 1/4.  Same box as the #573 sentinel EE. *)
Definition overlap_ee_center : Point := mkPoint 0 (-1).
Definition overlap_ee_radius : R := 1 / 4.

Lemma overlap_ee_coord_box :
  forall q,
    dist overlap_ee_center q < overlap_ee_radius ->
    -1 / 4 < px q < 1 / 4 /\ -5 / 4 < py q < -3 / 4.
Proof.
  intros q Hq.
  unfold overlap_ee_center, overlap_ee_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint 0 (-1)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint 0 (-1)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (0 - px q) < 1 / 4) by lra.
  assert (Hy' : Rabs ((-1) - py q) < 1 / 4) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma overlap_ee_dim2 : gtri_cell_dim2 overlap_gtri_ee.
Proof.
  exists overlap_ee_center, overlap_ee_radius.
  split; [unfold overlap_ee_radius; lra|].
  intros q Hq.
  apply overlap_ee_coord_box in Hq.
  destruct (sentinel_A_gs q) as [HAa _].
  destruct (overlap_B_gs q) as [HBa _].
  split.
  - apply Rle_lt_trans with (gsA 0 0 1 0 q).
    + apply (gtri_le_gsA 0 0 1 0 0 1 q).
    + rewrite HAa. lra.
  - apply Rle_lt_trans with (gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) q).
    + apply (gtri_le_gsA (1 / 4) (1 / 4) (5 / 4) (1 / 4) (1 / 4) (5 / 4) q).
    + rewrite HBa. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: nine gtri cells of 212101212 on the #567 overlap pair.           *)
(* -------------------------------------------------------------------------- *)

Theorem overlap_pair_ogc_gtri_cells :
  gtri_cell_dim2 overlap_gtri_ii /\
  gtri_cell_dim1 overlap_gtri_ib /\
  gtri_cell_dim2 overlap_gtri_ie /\
  gtri_cell_dim1 overlap_gtri_bi /\
  gtri_cell_dim0 overlap_gtri_bb /\
  gtri_cell_dim1 overlap_gtri_be /\
  gtri_cell_dim2 overlap_gtri_ei /\
  gtri_cell_dim1 overlap_gtri_eb /\
  gtri_cell_dim2 overlap_gtri_ee.
Proof.
  repeat split.
  - exact overlap_ii_dim2.
  - exact overlap_ib_dim1.
  - exact overlap_ie_dim2.
  - exact overlap_bi_dim1.
  - exact overlap_bb_dim0.
  - exact overlap_be_dim1.
  - exact overlap_ei_dim2.
  - exact overlap_eb_dim1.
  - exact overlap_ee_dim2.
Qed.

(* Qex: classifier IE is empty while the OGC cell is dim-2. *)
Theorem ogc_overlap_ie_not_classifier :
  im_ie (triangle_pair_fill TPR_Overlap) = None /\
  gtri_cell_dim2 overlap_gtri_ie.
Proof.
  split.
  - exact triangle_overlap_fill_ie_still_empty.
  - exact overlap_ie_dim2.
Qed.

Print Assumptions overlap_pair_ogc_gtri_cells.
Print Assumptions ogc_overlap_ie_not_classifier.
Print Assumptions aa_matrix_overlap_ogc_im_overlaps.
Print Assumptions triangle_overlap_fill_ie_still_empty.
Print Assumptions overlap_pair_regime.
