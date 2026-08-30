(* ============================================================================
   NetTopologySuite.Proofs.RelateNGContainsCells
   ----------------------------------------------------------------------------
   Issue #576 / #522 claimId 522-h (contains split): bar-2 beachhead for
   the contains regime — the exact OGC matrix of a strictly-interior
   triangle pair, in the specified-interior (gtri) vocabulary.

   True areal A-contains-B is 212FF1FF2 (oracle `cm_matrix_contains_disk`).
   The designated classifier fill `aa_matrix_contains` is still the older
   pattern-only 2FFFFFFF2 pin (empty IB/IE/BE).  `contains_b_ring_strictly_inside`
   already places B's whole boundary in `{0 < gtri A}`, so IB is dim-1,
   not empty.  This module names the OGC fill and proves the nine gtri
   cells on the #567 contains pair.  It does NOT remint
   `aa_matrix_contains` (shared with the rect lane) and does NOT rewire
   `triangle_pair_fill TPR_Contains`.

   This is the first split of #576 (contains, then touch-edge, then
   overlap).  Touch-edge and overlap remain.  Ticket 576 stays open.

   Green (Qed):
     - `aa_matrix_contains_ogc` is 212FF1FF2
     - `im_contains aa_matrix_contains_ogc` (pat_contains is II=T, EI=F, EB=F)
     - engine: closed B sits in `{1/4 <= gtri A}`, emptying BI/BB/EI/EB
     - contains-pair nine-cell theorem in gtri vocabulary (disks +
       segments from #568 / 522-g)
     - the pair classifies `TPR_Contains` (`contains_b` fires)

   Finding (Qex):
     - `im_ib (triangle_pair_fill TPR_Contains) = None`
       while IB is dim-1 on B's base.  The classifier pointer stays on
       2FFFFFFF2.  Rewiring that shared pin is later.

   Not claimed:
     - `geom_de9im_pointset` / `cell_ok` on `point_set` (ADR-0003)
     - remint of `aa_matrix_contains` or `triangle_pair_fill`
     - touch-edge or overlap nine-cell theorems (later #576 splits)
     - leftover certificates, classifier-order changes, ADR-0004

   Frozen anchors untouched.  Not an ADR-0004 remint.  `522-h` is the
   existing #576 ticket id (this letter is the contains split only).

   WITNESS topic: relate · claimId: 522-h · witness: 522-h-contains-bar2
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

(* WITNESS {"claimId":"522-h","topic":"relate","lemma":"contains_pair_ogc_gtri_cells","title":"Nine gtri cells of 212FF1FF2 on the #567 contains pair","file":"theories/RelateNGContainsCells.v","witness":"522-h-contains-bar2","board":"#576"} *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Segment
  DE9IM RelateAreaArea RelateLineLine
  RelateCurveMatrix
  GeneralTriangleSeparation
  RelateMatrixTriangle
  RelateNGCore
  RelateNGContains
  RelateNGRingInclusion
  RelateNGDisjointCells.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* OGC areal contains fill.  Not an alias of `aa_matrix_contains`.            *)
(* -------------------------------------------------------------------------- *)

Definition aa_matrix_contains_ogc : IntersectionMatrix :=
  {| im_ii := aa_dim2;        im_ib := aa_dim1;        im_ie := aa_dim2;
     im_bi := None;           im_bb := None;           im_be := aa_dim1;
     im_ei := None;           im_eb := None;           im_ee := aa_dim2 |}.

Lemma aa_matrix_contains_ogc_eq_cm :
  aa_matrix_contains_ogc = cm_matrix_contains_disk.
Proof. reflexivity. Qed.

Lemma aa_matrix_contains_ogc_ii : im_ii aa_matrix_contains_ogc = Some 2%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_contains_ogc_ib : im_ib aa_matrix_contains_ogc = Some 1%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_contains_ogc_ie : im_ie aa_matrix_contains_ogc = Some 2%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_contains_ogc_be : im_be aa_matrix_contains_ogc = Some 1%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_contains_ogc_ee : im_ee aa_matrix_contains_ogc = Some 2%nat.
Proof. reflexivity. Qed.

Lemma aa_matrix_contains_ogc_B_empty :
  im_bi aa_matrix_contains_ogc = None /\
  im_bb aa_matrix_contains_ogc = None /\
  im_ei aa_matrix_contains_ogc = None /\
  im_eb aa_matrix_contains_ogc = None.
Proof. repeat split; reflexivity. Qed.

Lemma aa_matrix_contains_ogc_im_contains :
  im_contains aa_matrix_contains_ogc.
Proof.
  unfold im_contains, pat_contains, matrix_matches, aa_matrix_contains_ogc.
  simpl. repeat split.
Qed.

(* Honesty: the classifier still emits the empty-IB pin. *)
Lemma triangle_contains_fill_ib_still_empty :
  im_ib (triangle_pair_fill TPR_Contains) = None.
Proof.
  rewrite triangle_pair_fill_contains_eq.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Witness pair: A = (0,0)(1,0)(0,1), B = (1/4,1/4)(1/2,1/4)(1/4,1/2).        *)
(* Same A as the #571 sentinel, so `sentinel_A_gs` applies.                   *)
(* -------------------------------------------------------------------------- *)

Lemma contains_pair_A_ccw :
  0 < gdbl 0 0 1 0 0 1.
Proof. unfold gdbl; lra. Qed.

Lemma contains_pair_B_vertex_d_in_A :
  0 < gtri 0 0 1 0 0 1 (mkPoint (1 / 4) (1 / 4)).
Proof.
  destruct (sentinel_A_gs (mkPoint (1 / 4) (1 / 4))) as [HA [HB HC]].
  apply (proj2 (gtri_pos_iff 0 0 1 0 0 1 (mkPoint (1 / 4) (1 / 4)))).
  rewrite HA, HB, HC. simpl. lra.
Qed.

Lemma contains_pair_B_vertex_e_in_A :
  0 < gtri 0 0 1 0 0 1 (mkPoint (1 / 2) (1 / 4)).
Proof.
  destruct (sentinel_A_gs (mkPoint (1 / 2) (1 / 4))) as [HA [HB HC]].
  apply (proj2 (gtri_pos_iff 0 0 1 0 0 1 (mkPoint (1 / 2) (1 / 4)))).
  rewrite HA, HB, HC. simpl. lra.
Qed.

Lemma contains_pair_B_vertex_f_in_A :
  0 < gtri 0 0 1 0 0 1 (mkPoint (1 / 4) (1 / 2)).
Proof.
  destruct (sentinel_A_gs (mkPoint (1 / 4) (1 / 2))) as [HA [HB HC]].
  apply (proj2 (gtri_pos_iff 0 0 1 0 0 1 (mkPoint (1 / 4) (1 / 2)))).
  rewrite HA, HB, HC. simpl. lra.
Qed.

Lemma contains_pair_contains_b :
  contains_b 0 0 1 0 0 1 (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) = true.
Proof.
  unfold contains_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exact (False_rect _ (Hn contains_pair_A_ccw)) ].
  destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint (1 / 4) (1 / 4)))) as [_ | Hn];
    [ | exact (False_rect _ (Hn contains_pair_B_vertex_d_in_A)) ].
  destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint (1 / 2) (1 / 4)))) as [_ | Hn];
    [ | exact (False_rect _ (Hn contains_pair_B_vertex_e_in_A)) ].
  destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint (1 / 4) (1 / 2)))) as [_ | Hn];
    [ | exact (False_rect _ (Hn contains_pair_B_vertex_f_in_A)) ].
  reflexivity.
Qed.

Lemma contains_pair_regime :
  triangle_pair_regime 0 0 1 0 0 1 (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2)
  = TPR_Contains.
Proof.
  apply triangle_pair_regime_contains.
  - exact contains_pair_A_ccw.
  - exact contains_pair_B_vertex_d_in_A.
  - exact contains_pair_B_vertex_e_in_A.
  - exact contains_pair_B_vertex_f_in_A.
Qed.

(* -------------------------------------------------------------------------- *)
(* B's three slacks.  Scale is 1/4 of the un-normalised 4y-1 form;            *)
(* signs and zero-sets are what the cells need.                               *)
(* -------------------------------------------------------------------------- *)

Lemma contains_B_gs :
  forall q,
    gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) q = (py q - 1 / 4) / 4 /\
    gsB (1 / 2) (1 / 4) (1 / 4) (1 / 2) q = (3 / 4 - px q - py q) / 4 /\
    gsC (1 / 4) (1 / 4) (1 / 4) (1 / 2) q = (px q - 1 / 4) / 4.
Proof. intros q; unfold gsA, gsB, gsC; split; [|split]; field. Qed.

(* Closed B sits in {x >= 1/4, y >= 1/4, x+y <= 3/4} ⊂ {1/4 <= gtri A}. *)
Lemma contains_closed_B_gtri_A_ge :
  forall p,
    0 <= gtri (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) p ->
    1 / 4 <= gtri 0 0 1 0 0 1 p.
Proof.
  intros p HB.
  apply gtri_nonneg_iff in HB.
  destruct HB as [HBa [HBb HBc]].
  destruct (contains_B_gs p) as [HBa' [HBb' HBc']].
  rewrite HBa' in HBa; rewrite HBb' in HBb; rewrite HBc' in HBc.
  destruct (sentinel_A_gs p) as [HAa [HAb HAc]].
  unfold gtri.
  apply Rmin_glb.
  - apply Rmin_glb.
    + rewrite HAa. lra.
    + rewrite HAb. lra.
  - rewrite HAc. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Specified-interior cells of the contains pair.                             *)
(* -------------------------------------------------------------------------- *)

Definition contains_gtri_ii (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\
  0 < gtri (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) p.

Definition contains_gtri_ib (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\
  gtri (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) p = 0.

Definition contains_gtri_ie (p : Point) : Prop :=
  0 < gtri 0 0 1 0 0 1 p /\
  gtri (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) p < 0.

Definition contains_gtri_bi (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p = 0 /\
  0 < gtri (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) p.

Definition contains_gtri_bb (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p = 0 /\
  gtri (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) p = 0.

Definition contains_gtri_be (p : Point) : Prop :=
  between (mkPoint 0 0) (mkPoint 1 0) p /\
  gtri (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) p < 0.

Definition contains_gtri_ei (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\
  0 < gtri (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) p.

Definition contains_gtri_eb (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\
  gtri (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) p = 0.

Definition contains_gtri_ee (p : Point) : Prop :=
  gtri 0 0 1 0 0 1 p < 0 /\
  gtri (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) p < 0.

Lemma contains_bi_empty : gtri_cell_empty contains_gtri_bi.
Proof.
  intros p [HA0 HB].
  assert (Hge : 1 / 4 <= gtri 0 0 1 0 0 1 p).
  { apply contains_closed_B_gtri_A_ge. lra. }
  lra.
Qed.

Lemma contains_bb_empty : gtri_cell_empty contains_gtri_bb.
Proof.
  intros p [HA0 HB0].
  assert (Hge : 1 / 4 <= gtri 0 0 1 0 0 1 p).
  { apply contains_closed_B_gtri_A_ge. lra. }
  lra.
Qed.

Lemma contains_ei_empty : gtri_cell_empty contains_gtri_ei.
Proof.
  intros p [HA HB].
  assert (Hge : 1 / 4 <= gtri 0 0 1 0 0 1 p).
  { apply contains_closed_B_gtri_A_ge. lra. }
  lra.
Qed.

Lemma contains_eb_empty : gtri_cell_empty contains_gtri_eb.
Proof.
  intros p [HA HB0].
  assert (Hge : 1 / 4 <= gtri 0 0 1 0 0 1 p).
  { apply contains_closed_B_gtri_A_ge. lra. }
  lra.
Qed.

(* II disk: B's centroid (1/3, 1/3), radius 1/24.  The L^\infty box is
   (7/24, 9/24)^2, which sits strictly inside both open triangles. *)
Definition contains_ii_center : Point := mkPoint (1 / 3) (1 / 3).
Definition contains_ii_radius : R := 1 / 24.

Lemma contains_ii_coord_box :
  forall q,
    dist contains_ii_center q < contains_ii_radius ->
    7 / 24 < px q < 9 / 24 /\ 7 / 24 < py q < 9 / 24.
Proof.
  intros q Hq.
  unfold contains_ii_center, contains_ii_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint (1 / 3) (1 / 3)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint (1 / 3) (1 / 3)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (1 / 3 - px q) < 1 / 24) by lra.
  assert (Hy' : Rabs (1 / 3 - py q) < 1 / 24) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma contains_ii_dim2 : gtri_cell_dim2 contains_gtri_ii.
Proof.
  exists contains_ii_center, contains_ii_radius.
  split; [unfold contains_ii_radius; lra|].
  intros q Hq.
  apply contains_ii_coord_box in Hq.
  destruct (sentinel_A_gs q) as [HAa [HAb HAc]].
  destruct (contains_B_gs q) as [HBa [HBb HBc]].
  split.
  - apply (proj2 (gtri_pos_iff 0 0 1 0 0 1 q)).
    rewrite HAa, HAb, HAc. lra.
  - apply (proj2 (gtri_pos_iff (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) q)).
    rewrite HBa, HBb, HBc. lra.
Qed.

(* IE disk: (1/8, 1/8), radius 1/16.  The box is (1/16, 3/16)^2 ⊂ int(A)
   and x < 1/4 forces gsC_B < 0. *)
Definition contains_ie_center : Point := mkPoint (1 / 8) (1 / 8).
Definition contains_ie_radius : R := 1 / 16.

Lemma contains_ie_coord_box :
  forall q,
    dist contains_ie_center q < contains_ie_radius ->
    1 / 16 < px q < 3 / 16 /\ 1 / 16 < py q < 3 / 16.
Proof.
  intros q Hq.
  unfold contains_ie_center, contains_ie_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint (1 / 8) (1 / 8)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint (1 / 8) (1 / 8)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (1 / 8 - px q) < 1 / 16) by lra.
  assert (Hy' : Rabs (1 / 8 - py q) < 1 / 16) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma contains_ie_dim2 : gtri_cell_dim2 contains_gtri_ie.
Proof.
  exists contains_ie_center, contains_ie_radius.
  split; [unfold contains_ie_radius; lra|].
  intros q Hq.
  apply contains_ie_coord_box in Hq.
  destruct (sentinel_A_gs q) as [HAa [HAb HAc]].
  destruct (contains_B_gs q) as [_ [_ HBc]].
  split.
  - apply (proj2 (gtri_pos_iff 0 0 1 0 0 1 q)).
    rewrite HAa, HAb, HAc. lra.
  - apply Rle_lt_trans with (gsC (1 / 4) (1 / 4) (1 / 4) (1 / 2) q).
    + apply (gtri_le_gsC (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) q).
    + rewrite HBc. lra.
Qed.

Lemma contains_ib_dim1 : gtri_cell_dim1 contains_gtri_ib.
Proof.
  exists (mkPoint (1 / 4) (1 / 4)), (mkPoint (1 / 2) (1 / 4)).
  repeat split.
  - exact contains_pair_B_vertex_d_in_A.
  - destruct (contains_B_gs (mkPoint (1 / 4) (1 / 4))) as [HA [HB HC]].
    apply Rle_antisym.
    + apply Rle_trans with (gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) (mkPoint (1 / 4) (1 / 4))).
      * apply (gtri_le_gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2)
                 (mkPoint (1 / 4) (1 / 4))).
      * rewrite HA. simpl. lra.
    + apply gtri_nonneg_iff. rewrite HA, HB, HC. simpl. lra.
  - exact contains_pair_B_vertex_e_in_A.
  - destruct (contains_B_gs (mkPoint (1 / 2) (1 / 4))) as [HA [HB HC]].
    apply Rle_antisym.
    + apply Rle_trans with (gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) (mkPoint (1 / 2) (1 / 4))).
      * apply (gtri_le_gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2)
                 (mkPoint (1 / 2) (1 / 4))).
      * rewrite HA. simpl. lra.
    + apply gtri_nonneg_iff. rewrite HA, HB, HC. simpl. lra.
  - intros Heq. apply (f_equal px) in Heq. simpl in Heq. lra.
Qed.

Lemma contains_be_dim1 : gtri_cell_dim1 contains_gtri_be.
Proof.
  exists (mkPoint (1 / 3) 0), (mkPoint (2 / 3) 0).
  repeat split.
  - exists (1 / 3). repeat split; try lra; simpl; field.
  - destruct (contains_B_gs (mkPoint (1 / 3) 0)) as [HA _].
    apply Rle_lt_trans with (gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) (mkPoint (1 / 3) 0)).
    + apply (gtri_le_gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2)
               (mkPoint (1 / 3) 0)).
    + rewrite HA. simpl. lra.
  - exists (2 / 3). repeat split; try lra; simpl; field.
  - destruct (contains_B_gs (mkPoint (2 / 3) 0)) as [HA _].
    apply Rle_lt_trans with (gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) (mkPoint (2 / 3) 0)).
    + apply (gtri_le_gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2)
               (mkPoint (2 / 3) 0)).
    + rewrite HA. simpl. lra.
  - intros Heq. apply (f_equal px) in Heq. simpl in Heq. lra.
Qed.

(* EE disk: (0, -1), radius 1/4.  Same box as the #573 sentinel EE. *)
Definition contains_ee_center : Point := mkPoint 0 (-1).
Definition contains_ee_radius : R := 1 / 4.

Lemma contains_ee_coord_box :
  forall q,
    dist contains_ee_center q < contains_ee_radius ->
    -1 / 4 < px q < 1 / 4 /\ -5 / 4 < py q < -3 / 4.
Proof.
  intros q Hq.
  unfold contains_ee_center, contains_ee_radius in Hq.
  pose proof (abs_coord_le_dist_x (mkPoint 0 (-1)) q) as Hx.
  pose proof (abs_coord_le_dist_y (mkPoint 0 (-1)) q) as Hy.
  simpl in Hx, Hy.
  assert (Hx' : Rabs (0 - px q) < 1 / 4) by lra.
  assert (Hy' : Rabs ((-1) - py q) < 1 / 4) by lra.
  apply Rabs_lt_between in Hx'.
  apply Rabs_lt_between in Hy'.
  lra.
Qed.

Lemma contains_ee_dim2 : gtri_cell_dim2 contains_gtri_ee.
Proof.
  exists contains_ee_center, contains_ee_radius.
  split; [unfold contains_ee_radius; lra|].
  intros q Hq.
  apply contains_ee_coord_box in Hq.
  destruct (sentinel_A_gs q) as [HAa _].
  destruct (contains_B_gs q) as [HBa _].
  split.
  - apply Rle_lt_trans with (gsA 0 0 1 0 q).
    + apply (gtri_le_gsA 0 0 1 0 0 1 q).
    + rewrite HAa. lra.
  - apply Rle_lt_trans with (gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) q).
    + apply (gtri_le_gsA (1 / 4) (1 / 4) (1 / 2) (1 / 4) (1 / 4) (1 / 2) q).
    + rewrite HBa. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Headline: nine gtri cells of 212FF1FF2 on the #567 contains pair.          *)
(* -------------------------------------------------------------------------- *)

Theorem contains_pair_ogc_gtri_cells :
  gtri_cell_dim2 contains_gtri_ii /\
  gtri_cell_dim1 contains_gtri_ib /\
  gtri_cell_dim2 contains_gtri_ie /\
  gtri_cell_empty contains_gtri_bi /\
  gtri_cell_empty contains_gtri_bb /\
  gtri_cell_dim1 contains_gtri_be /\
  gtri_cell_empty contains_gtri_ei /\
  gtri_cell_empty contains_gtri_eb /\
  gtri_cell_dim2 contains_gtri_ee.
Proof.
  repeat split.
  - exact contains_ii_dim2.
  - exact contains_ib_dim1.
  - exact contains_ie_dim2.
  - exact contains_bi_empty.
  - exact contains_bb_empty.
  - exact contains_be_dim1.
  - exact contains_ei_empty.
  - exact contains_eb_empty.
  - exact contains_ee_dim2.
Qed.

(* Qex: classifier IB is empty while the OGC cell is dim-1. *)
Theorem ogc_contains_ib_not_classifier :
  im_ib (triangle_pair_fill TPR_Contains) = None /\
  gtri_cell_dim1 contains_gtri_ib.
Proof.
  split.
  - exact triangle_contains_fill_ib_still_empty.
  - exact contains_ib_dim1.
Qed.

Print Assumptions contains_pair_ogc_gtri_cells.
Print Assumptions ogc_contains_ib_not_classifier.
Print Assumptions aa_matrix_contains_ogc_im_contains.
Print Assumptions triangle_contains_fill_ib_still_empty.
Print Assumptions contains_pair_regime.
