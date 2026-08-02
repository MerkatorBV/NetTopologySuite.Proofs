(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLineMeet
   ----------------------------------------------------------------------------
   Issue #67 S15a–S15g: line×line point-set DE-9IM bridge — meet layer.

   Split (2026-08) from the former monolithic RelateNodingLineLine.v; the
   original §-numbers are preserved so the S15 session retros stay accurate.
   RelateNodingLineLine.v remains as the re-export umbrella.

   Per-regime meet-cell bridges over the strata layer:
   `segments_rejected` / `LPR_Disjoint` ⇒ four interior/boundary-meet cells
   empty (`line_no_ib_meet`); `segments_proper_cross` / `LPR_ProperCross` ⇒
   II = 0-dimensional point cell with IB/BI/BB empty; `LPR_Share` (interior)
   ⇒ II = 0-dim point cell; `LPR_CollinearOverlap` with `C <> D` ⇒ II =
   1-dimensional cell (degenerate `C = D` routes to `ll_matrix_point_ii`);
   shared-endpoint overlap ⇒ BB = 0-dim cell; T-junction int×bnd contact ⇒
   IB = 0-dim for `ll_matrix_touches_endpoint`; mutual endpoint contact ⇒
   BB = 0-dim.

   Sections: §4 (no-share), §5 (proper cross), §6 (collinear overlap),
   §7 (interior share), §8 (degenerate C = D), §9 (overlap BB endpoints),
   §10 (T-junction / endpoint contact).

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
  RelateNodingLineLineStrata.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §4  No-share ⇒ meet cells empty (disjoint regime geometry).                *)
(* -------------------------------------------------------------------------- *)

Lemma int_bnd_share :
  forall A B C D p,
    seg_in_stratum LSInt A B p ->
    seg_in_stratum LSBnd C D p ->
    segments_share A B C D.
Proof.
  intros A B C D p HAB HCD.
  exists p. split.
  - apply between_strict_implies_between; exact HAB.
  - apply endpoint_implies_between; exact HCD.
Qed.

Lemma bnd_int_share :
  forall A B C D p,
    seg_in_stratum LSBnd A B p ->
    seg_in_stratum LSInt C D p ->
    segments_share A B C D.
Proof.
  intros A B C D p HAB HCD.
  exists p. split.
  - apply endpoint_implies_between; exact HAB.
  - apply between_strict_implies_between; exact HCD.
Qed.

Lemma bnd_bnd_share :
  forall A B C D p,
    seg_in_stratum LSBnd A B p ->
    seg_in_stratum LSBnd C D p ->
    segments_share A B C D.
Proof.
  intros A B C D p HAB HCD.
  exists p. split; apply endpoint_implies_between; assumption.
Qed.

Lemma int_int_share :
  forall A B C D p,
    seg_in_stratum LSInt A B p ->
    seg_in_stratum LSInt C D p ->
    segments_share A B C D.
Proof.
  intros A B C D p HAB HCD.
  exists p. split; apply between_strict_implies_between; assumption.
Qed.

Lemma no_share_no_int_int :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ (exists p : Point, seg_in_stratum LSInt A B p /\ seg_in_stratum LSInt C D p).
Proof.
  intros A B C D Hnoshare [p [HAB HCD]].
  apply Hnoshare. exact (int_int_share A B C D p HAB HCD).
Qed.

Lemma no_share_no_int_bnd :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ (exists p : Point, seg_in_stratum LSInt A B p /\ seg_in_stratum LSBnd C D p).
Proof.
  intros A B C D Hnoshare [p [HAB HCD]].
  apply Hnoshare. exact (int_bnd_share A B C D p HAB HCD).
Qed.

Lemma no_share_no_bnd_int :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ (exists p : Point, seg_in_stratum LSBnd A B p /\ seg_in_stratum LSInt C D p).
Proof.
  intros A B C D Hnoshare [p [HAB HCD]].
  apply Hnoshare. exact (bnd_int_share A B C D p HAB HCD).
Qed.

Lemma no_share_no_bnd_bnd :
  forall A B C D,
    ~ segments_share A B C D ->
    ~ (exists p : Point, seg_in_stratum LSBnd A B p /\ seg_in_stratum LSBnd C D p).
Proof.
  intros A B C D Hnoshare [p [HAB HCD]].
  apply Hnoshare. exact (bnd_bnd_share A B C D p HAB HCD).
Qed.

Theorem segments_no_share_line_no_ib_meet :
  forall A B C D,
    ~ segments_share A B C D ->
    line_no_ib_meet A B C D ll_matrix_disjoint.
Proof.
  intros A B C D Hnoshare.
  unfold line_no_ib_meet, ll_matrix_disjoint. simpl.
  split; [ apply (line_cell_ok_none_when LSInt LSInt A B C D)
           | split; [ apply (line_cell_ok_none_when LSInt LSBnd A B C D)
                    | split; [ apply (line_cell_ok_none_when LSBnd LSInt A B C D)
                             | apply (line_cell_ok_none_when LSBnd LSBnd A B C D) ] ] ].
  all: eauto using no_share_no_int_int, no_share_no_int_bnd,
    no_share_no_bnd_int, no_share_no_bnd_bnd.
Qed.

Theorem classify_disjoint_line_no_ib_meet :
  forall A B C D,
    classify_line_pair A B C D LPR_Disjoint ->
    line_no_ib_meet A B C D (line_pair_fill LPR_Disjoint).
Proof.
  intros A B C D Hdisj.
  rewrite line_pair_fill_disjoint_eq.
  apply segments_no_share_line_no_ib_meet.
  intro Hshare. apply (rejection_not_share A B C D Hdisj Hshare).
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Proper cross ⇒ II point cell + empty other meet cells.                 *)
(* -------------------------------------------------------------------------- *)

Lemma between_strict_implies_on_line :
  forall P0 P1 Q, between_strict P0 P1 Q -> cross P0 P1 Q = 0.
Proof.
  intros P0 P1 Q Hstrict.
  apply between_implies_on_line.
  apply between_strict_implies_between. exact Hstrict.
Qed.

Lemma endpoint_implies_on_line :
  forall P0 P1 Q, on_segment_endpoint P0 P1 Q -> cross P0 P1 Q = 0.
Proof.
  intros P0 P1 Q [Hbet [Heq | Heq]].
  - subst Q. apply cross_at_P0_is_collinear.
  - subst Q. apply cross_at_P1_is_collinear.
Qed.

Lemma between_strict_of_between_not_endpoints :
  forall P0 P1 Q,
    between P0 P1 Q ->
    Q <> P0 -> Q <> P1 ->
    between_strict P0 P1 Q.
Proof.
  intros P0 P1 Q [t [Ht0 [Ht1 [Hx Hy]]]] Hne0 Hne1.
  destruct (Rlt_dec 0 t) as [Htpos | Htpos].
  - destruct (Rlt_dec t 1) as [Htlt | Htlt].
    + exists t. repeat split; [exact Htpos | exact Htlt | assumption | assumption].
    + exfalso. apply Hne1. assert (Ht : t = 1) by lra.
      subst t. destruct P0, P1, Q; simpl in Hx, Hy. f_equal; lra.
  - exfalso. apply Hne0. assert (Ht : t = 0) by lra.
    subst t. destruct P0, Q; simpl in Hx, Hy. f_equal; lra.
Qed.

Lemma midpoint_not_endpoint_when_distinct :
  forall P0 P1,
    P0 <> P1 ->
    midpoint P0 P1 <> P0 /\ midpoint P0 P1 <> P1.
Proof.
  intros P0 P1 Hne.
  split; intro Heq.
  - apply Hne. destruct P0 as [x0 y0], P1 as [x1 y1].
    simpl in Heq. unfold midpoint in Heq. simpl in Heq.
    inversion Heq. subst. f_equal; lra.
  - apply Hne. destruct P0 as [x0 y0], P1 as [x1 y1].
    simpl in Heq. unfold midpoint in Heq. simpl in Heq.
    inversion Heq. subst. f_equal; lra.
Qed.

Lemma between_strict_midpoint :
  forall P0 P1, P0 <> P1 -> between_strict P0 P1 (midpoint P0 P1).
Proof.
  intros P0 P1 Hne.
  apply between_strict_of_between_not_endpoints.
  - apply midpoint_between.
  - destruct (midpoint_not_endpoint_when_distinct P0 P1 Hne) as [H0 _]. exact H0.
  - destruct (midpoint_not_endpoint_when_distinct P0 P1 Hne) as [_ H1]. exact H1.
Qed.

Lemma proper_cross_no_int_bnd :
  forall A B C D,
    segments_proper_cross A B C D ->
    ~ (exists p : Point, seg_in_stratum LSInt A B p /\ seg_in_stratum LSBnd C D p).
Proof.
  intros A B C D [Hprod _] [p [HAB [Hbet [HeqC | HeqD]]]].
  - rewrite HeqC in HAB.
    assert (Hc0 : cross A B C = 0) by (apply between_strict_implies_on_line; exact HAB).
    rewrite Hc0 in Hprod. lra.
  - rewrite HeqD in HAB.
    assert (Hd0 : cross A B D = 0) by (apply between_strict_implies_on_line; exact HAB).
    rewrite Hd0 in Hprod. lra.
Qed.

Lemma proper_cross_no_bnd_int :
  forall A B C D,
    segments_proper_cross A B C D ->
    ~ (exists p : Point, seg_in_stratum LSBnd A B p /\ seg_in_stratum LSInt C D p).
Proof.
  intros A B C D [_ Hprod] [p [[Hbet [HeqA | HeqB]] HCD]].
  - rewrite HeqA in HCD.
    assert (Hc0 : cross C D A = 0) by (apply between_strict_implies_on_line; exact HCD).
    rewrite Hc0 in Hprod. lra.
  - rewrite HeqB in HCD.
    assert (Hd0 : cross C D B = 0) by (apply between_strict_implies_on_line; exact HCD).
    rewrite Hd0 in Hprod. lra.
Qed.

Lemma proper_cross_no_bnd_bnd :
  forall A B C D,
    segments_proper_cross A B C D ->
    ~ (exists p : Point, seg_in_stratum LSBnd A B p /\ seg_in_stratum LSBnd C D p).
Proof.
  intros A B C D [Hab _] [p [HAB HCD]].
  unfold seg_in_stratum in HAB, HCD. simpl in HAB, HCD.
  destruct HAB as [_ [-> | ->]]; destruct HCD as [_ [-> | ->]];
    simpl in Hab;
    rewrite ?cross_at_P0_is_collinear, ?cross_at_P1_is_collinear in Hab;
    lra.
Qed.

Lemma open_param_between_strict_ab :
  forall P0 P1 Q,
    (exists t : R,
       0 < t < 1 /\
       px Q = (1 - t) * px P0 + t * px P1 /\
       py Q = (1 - t) * py P0 + t * py P1) ->
    between_strict P0 P1 Q.
Proof.
  intros P0 P1 Q [t Ht]. exists t. exact Ht.
Qed.

Lemma proper_cross_interior_share :
  forall A B C D,
    segments_proper_cross A B C D ->
    segments_interior_share A B C D.
Proof.
  intros A B C D [Hab Hcd].
  exists (strict_intersection_point A B C D).
  split.
  - apply open_param_between_strict_ab.
    eauto using strict_intersection_point_open_ab.
  - apply open_param_between_strict_ab.
    eauto using strict_intersection_point_open_cd.
Qed.

Definition line_ii_point_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ii m) LSInt LSInt A B C D.

Theorem segments_proper_cross_line_ii_cell :
  forall A B C D,
    segments_proper_cross A B C D ->
    line_ii_point_cell A B C D ll_matrix_point_ii.
Proof.
  intros A B C D Hcross.
  unfold line_ii_point_cell, ll_matrix_point_ii. simpl.
  destruct (proper_cross_interior_share A B C D Hcross) as [X [HAB HCD]].
  apply (line_cell_ok_dim0 LSInt LSInt A B C D X HAB HCD).
Qed.

Theorem classify_proper_cross_line_ii_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_ProperCross ->
    line_ii_point_cell A B C D (line_pair_fill LPR_ProperCross).
Proof.
  intros A B C D Hcross.
  rewrite line_pair_fill_proper_cross_eq.
  apply segments_proper_cross_line_ii_cell. exact Hcross.
Qed.

Theorem segments_proper_cross_line_point_ii_ib_meet :
  forall A B C D,
    segments_proper_cross A B C D ->
    line_point_ii_ib_meet A B C D ll_matrix_point_ii.
Proof.
  intros A B C D Hcross.
  unfold line_point_ii_ib_meet, ll_matrix_point_ii. simpl.
  split.
  - apply segments_proper_cross_line_ii_cell. exact Hcross.
  - split.
    + apply (line_cell_ok_none_when LSInt LSBnd A B C D).
      eauto using proper_cross_no_int_bnd.
    + split.
      * apply (line_cell_ok_none_when LSBnd LSInt A B C D).
        eauto using proper_cross_no_bnd_int.
      * apply (line_cell_ok_none_when LSBnd LSBnd A B C D).
        eauto using proper_cross_no_bnd_bnd.
Qed.

Theorem classify_proper_cross_line_point_ii_ib_meet :
  forall A B C D,
    classify_line_pair A B C D LPR_ProperCross ->
    line_point_ii_ib_meet A B C D (line_pair_fill LPR_ProperCross).
Proof.
  intros A B C D Hcross.
  rewrite line_pair_fill_proper_cross_eq.
  apply segments_proper_cross_line_point_ii_ib_meet. exact Hcross.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Collinear overlap ⇒ II 1-dimensional cell (distinct endpoints).        *)
(* -------------------------------------------------------------------------- *)

Definition line_ii_dim1_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ii m) LSInt LSInt A B C D.

Lemma between_ab_midpoint_param :
  forall A B C D s t,
    0 <= s -> s <= 1 ->
    px C = (1 - s) * px A + s * px B ->
    py C = (1 - s) * py A + s * py B ->
    0 <= t -> t <= 1 ->
    px D = (1 - t) * px A + t * px B ->
    py D = (1 - t) * py A + t * py B ->
    px (midpoint C D) = (1 - (s + t) / 2) * px A + (s + t) / 2 * px B /\
    py (midpoint C D) = (1 - (s + t) / 2) * py A + (s + t) / 2 * py B.
Proof.
  intros A B C D s t _ _ HxC HyC _ _ HxD HyD.
  split.
  - unfold midpoint. cbn. rewrite HxC, HxD. field.
  - unfold midpoint. cbn. rewrite HyC, HyD. field.
Qed.

Lemma collinear_overlap_midpoint_strict_ab :
  forall A B C D,
    between A B C ->
    between A B D ->
    C <> D ->
    seg_in_stratum LSInt A B (midpoint C D).
Proof.
  intros A B C D HAC HAD Hne.
  unfold seg_in_stratum. simpl.
  destruct HAC as [s [Hs0 [Hs1 [HxC HyC]]]].
  destruct HAD as [t [Ht0 [Ht1 [HxD HyD]]]].
  destruct (between_ab_midpoint_param A B C D s t Hs0 Hs1 HxC HyC Ht0 Ht1 HxD HyD)
    as [HxM HyM].
  exists ((s + t) / 2). repeat split.
  - assert (Hpos : 0 < s + t).
    { apply Rnot_le_lt. intro Hle.
      assert (Hs : s = 0) by lra. assert (Ht : t = 0) by lra.
      subst s t. simpl in HxC, HyC, HxD, HyD.
      destruct A as [ax ay]. destruct C as [cx cy]. destruct D as [dx dy].
      simpl in HxC, HyC, HxD, HyD.
      exfalso. apply Hne.
      f_equal; lra. }
    lra.
  - assert (Hlt2 : s + t < 2).
    { apply Rnot_le_lt. intro Hle.
      assert (Hs : s = 1) by lra. assert (Ht : t = 1) by lra.
      subst s t. simpl in HxC, HyC, HxD, HyD.
      destruct B as [bx b_y]. destruct C as [cx cy]. destruct D as [dx dy].
      simpl in HxC, HyC, HxD, HyD.
      exfalso. apply Hne.
      f_equal; lra. }
    lra.
  - exact HxM.
  - exact HyM.
Qed.

Lemma collinear_overlap_midpoint_strict_cd :
  forall C D,
    C <> D ->
    seg_in_stratum LSInt C D (midpoint C D).
Proof.
  intros C D Hne.
  unfold seg_in_stratum. simpl.
  apply between_strict_midpoint. exact Hne.
Qed.

Theorem segments_collinear_overlap_line_ii_cell :
  forall A B C D,
    segments_collinear A B C D ->
    segments_interior_collinear_overlap A B C D ->
    C <> D ->
    line_ii_dim1_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D _ [HAC HAD] Hne.
  unfold line_ii_dim1_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim1 LSInt LSInt A B C D (midpoint C D)).
  - apply collinear_overlap_midpoint_strict_ab; assumption.
  - apply collinear_overlap_midpoint_strict_cd. exact Hne.
Qed.

Theorem classify_collinear_overlap_line_ii_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    C <> D ->
    line_ii_dim1_cell A B C D (line_pair_fill LPR_CollinearOverlap).
Proof.
  intros A B C D [Hcol Hov] Hne.
  rewrite line_pair_fill_collinear_overlap_eq.
  apply segments_collinear_overlap_line_ii_cell; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Interior share ⇒ II point cell (share regime, strict-interior witness). *)
(* -------------------------------------------------------------------------- *)

Theorem segments_interior_share_line_ii_cell :
  forall A B C D,
    segments_interior_share A B C D ->
    line_ii_point_cell A B C D ll_matrix_point_ii.
Proof.
  intros A B C D [X [HAB HCD]].
  unfold line_ii_point_cell, ll_matrix_point_ii. simpl.
  apply (line_cell_ok_dim0 LSInt LSInt A B C D X).
  - unfold seg_in_stratum. simpl. exact HAB.
  - unfold seg_in_stratum. simpl. exact HCD.
Qed.

Theorem classify_share_interior_line_ii_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_Share ->
    segments_interior_share A B C D ->
    line_ii_point_cell A B C D (line_pair_fill LPR_Share).
Proof.
  intros A B C D _ Hshare.
  rewrite line_pair_fill_share_eq.
  apply segments_interior_share_line_ii_cell. exact Hshare.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Degenerate collinear overlap (`C = D`) ⇒ point II cell.                *)
(* -------------------------------------------------------------------------- *)

Lemma between_strict_self :
  forall P, between_strict P P P.
Proof.
  intros P. exists (1 / 2). split.
  - split; lra.
  - split; simpl; ring.
Qed.

Lemma between_strict_same_endpoints :
  forall P Q, between_strict P P Q -> Q = P.
Proof.
  intros P Q [t [Ht [Hx Hy]]].
  destruct P, Q. simpl in Hx, Hy. f_equal; lra.
Qed.

Theorem segments_collinear_overlap_CeqD_point_ii_cell :
  forall A B C D,
    C = D ->
    between_strict A B C ->
    line_ii_point_cell A B C D ll_matrix_point_ii.
Proof.
  intros A B C D Heq Hstrict.
  subst D.
  unfold line_ii_point_cell, ll_matrix_point_ii. simpl.
  apply (line_cell_ok_dim0 LSInt LSInt A B C C C).
  - unfold seg_in_stratum. simpl. exact Hstrict.
  - unfold seg_in_stratum. simpl. apply between_strict_self.
Qed.

Theorem classify_collinear_overlap_CeqD_point_ii_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    C = D ->
    between_strict A B C ->
    line_ii_point_cell A B C D ll_matrix_point_ii.
Proof.
  intros A B C D _ Heq Hstrict.
  apply segments_collinear_overlap_CeqD_point_ii_cell; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §9  Collinear overlap — BB point cell at a shared segment endpoint.        *)
(* -------------------------------------------------------------------------- *)

Definition line_bb_point_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_bb m) LSBnd LSBnd A B C D.

Theorem collinear_overlap_endpoint_A_C_bb_cell :
  forall A B C D, A = C -> line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D Heq.
  subst C.
  unfold line_bb_point_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim0 LSBnd LSBnd A B A D A).
  - apply seg_in_stratum_bnd_left.
  - apply seg_in_stratum_bnd_left.
Qed.

Theorem collinear_overlap_endpoint_A_D_bb_cell :
  forall A B C D, A = D -> line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D Heq.
  subst D.
  unfold line_bb_point_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim0 LSBnd LSBnd A B C A A).
  - apply seg_in_stratum_bnd_left.
  - apply seg_in_stratum_bnd_right.
Qed.

Theorem collinear_overlap_endpoint_B_C_bb_cell :
  forall A B C D, B = C -> line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D Heq.
  subst C.
  unfold line_bb_point_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim0 LSBnd LSBnd A B B D B).
  - apply seg_in_stratum_bnd_right.
  - apply seg_in_stratum_bnd_left.
Qed.

Theorem collinear_overlap_endpoint_B_D_bb_cell :
  forall A B C D, B = D -> line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D Heq.
  subst D.
  unfold line_bb_point_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim0 LSBnd LSBnd A B C B B).
  - apply seg_in_stratum_bnd_right.
  - apply seg_in_stratum_bnd_right.
Qed.

Theorem classify_collinear_overlap_shared_endpoint_bb_cell :
  forall A B C D,
    classify_line_pair A B C D LPR_CollinearOverlap ->
    (A = C \/ A = D \/ B = C \/ B = D) ->
    line_bb_point_cell A B C D (line_pair_fill LPR_CollinearOverlap).
Proof.
  intros A B C D _ [HAC | [HAD | [HBC | HBD]]].
  - rewrite line_pair_fill_collinear_overlap_eq.
    apply collinear_overlap_endpoint_A_C_bb_cell. exact HAC.
  - rewrite line_pair_fill_collinear_overlap_eq.
    apply collinear_overlap_endpoint_A_D_bb_cell. exact HAD.
  - rewrite line_pair_fill_collinear_overlap_eq.
    apply collinear_overlap_endpoint_B_C_bb_cell. exact HBC.
  - rewrite line_pair_fill_collinear_overlap_eq.
    apply collinear_overlap_endpoint_B_D_bb_cell. exact HBD.
Qed.

(* -------------------------------------------------------------------------- *)
(* §10  T-junction / endpoint contact — Touches and overlap BB witnesses.       *)
(* -------------------------------------------------------------------------- *)

Definition segments_int_bnd_contact (A B C D : Point) : Prop :=
  exists p : Point, seg_in_stratum LSInt A B p /\ seg_in_stratum LSBnd C D p.

Definition line_ib_point_cell (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ib m) LSInt LSBnd A B C D.

Theorem segments_int_bnd_touches_ib_cell :
  forall A B C D,
    segments_int_bnd_contact A B C D ->
    line_ib_point_cell A B C D ll_matrix_touches_endpoint.
Proof.
  intros A B C D [p [HAB HCD]].
  unfold line_ib_point_cell, ll_matrix_touches_endpoint. simpl.
  apply (line_cell_ok_dim0 LSInt LSBnd A B C D p); assumption.
Qed.

Theorem segments_endpoint_contact_bb_cell :
  forall A B C D,
    segments_endpoint_contact A B C D ->
    line_bb_point_cell A B C D ll_matrix_overlap_ii.
Proof.
  intros A B C D [X [HAB [HCD [HendAB HendCD]]]].
  unfold line_bb_point_cell, ll_matrix_overlap_ii. simpl.
  apply (line_cell_ok_dim0 LSBnd LSBnd A B C D X).
  - unfold seg_in_stratum. simpl. exact HendAB.
  - unfold seg_in_stratum. simpl. exact HendCD.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions classify_disjoint_line_no_ib_meet.
Print Assumptions classify_proper_cross_line_ii_cell.
Print Assumptions classify_proper_cross_line_point_ii_ib_meet.
Print Assumptions classify_collinear_overlap_line_ii_cell.
Print Assumptions classify_share_interior_line_ii_cell.
Print Assumptions classify_collinear_overlap_CeqD_point_ii_cell.
Print Assumptions classify_collinear_overlap_shared_endpoint_bb_cell.
Print Assumptions segments_int_bnd_touches_ib_cell.
Print Assumptions segments_endpoint_contact_bb_cell.
