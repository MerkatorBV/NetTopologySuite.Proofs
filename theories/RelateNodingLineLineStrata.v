(* ============================================================================
   NetTopologySuite.Proofs.RelateNodingLineLineStrata
   ----------------------------------------------------------------------------
   Issue #67 S15a: line×line point-set DE-9IM bridge — strata layer.

   Split (2026-08) from the former monolithic RelateNodingLineLine.v; the
   original §-numbers are preserved so the S15 session retros stay accurate.
   RelateNodingLineLine.v remains as the re-export umbrella.

   Closed-segment strata (strict interior / endpoint boundary / exterior),
   the 9-cell `line_de9im_pointset` specification with its per-cell
   `line_cell_ok` contract, the shared-exterior-point substrate
   (`two_segments_exterior_meet`, so EE is always inhabited), and the
   matrix well-formedness corollary `line_de9im_matrix_ok`.

   Sections: §1 (strata), §2 (cell spec), §3 (exterior meet), §13
   (matrix_ok corollary).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals Lra List Lia.
Import ListNotations.
From NTS.Proofs Require Import DE9IM Distance Orientation Segment Intersect
  RelateLineLine RelateBoundary RelateMatrixLineLine.
Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Segment strata (closed segment point-set topology).                    *)
(* -------------------------------------------------------------------------- *)

Inductive LineStratum : Type := LSInt | LSBnd | LSExt.

Definition seg_in_stratum (s : LineStratum) (P0 P1 p : Point) : Prop :=
  match s with
  | LSInt => between_strict P0 P1 p
  | LSBnd => on_segment_endpoint P0 P1 p
  | LSExt => ~ between P0 P1 p
  end.

Lemma between_strict_implies_between :
  forall P0 P1 Q, between_strict P0 P1 Q -> between P0 P1 Q.
Proof.
  intros P0 P1 Q [t [Ht [Hx Hy]]].
  exists t. repeat split; try lra; assumption.
Qed.

Lemma endpoint_implies_between :
  forall P0 P1 Q, on_segment_endpoint P0 P1 Q -> between P0 P1 Q.
Proof.
  intros P0 P1 Q [H _]. exact H.
Qed.

Lemma seg_in_stratum_bnd_left :
  forall P0 P1, seg_in_stratum LSBnd P0 P1 P0.
Proof.
  intros P0 P1. unfold seg_in_stratum. simpl.
  split; [ apply between_P0 | left; reflexivity ].
Qed.

Lemma seg_in_stratum_bnd_right :
  forall P0 P1, seg_in_stratum LSBnd P0 P1 P1.
Proof.
  intros P0 P1. unfold seg_in_stratum. simpl.
  split; [ apply between_P1 | right; reflexivity ].
Qed.

Lemma between_py_le_max :
  forall P0 P1 Q, between P0 P1 Q ->
    py Q <= Rmax (py P0) (py P1).
Proof.
  intros P0 P1 Q Hbet.
  destruct Hbet as [t Ht].
  destruct Ht as [Ht0 [Ht1 [Hx Hy]]].
  rewrite Hy. destruct (Rle_dec (py P0) (py P1)) as [Hle | Hgt].
  - rewrite Rmax_right; [ nra | exact Hle ].
  - rewrite Rmax_left; [ nra | lra ].
Qed.

Lemma above_segment_not_on :
  forall P0 P1 p b,
    (forall Q, between P0 P1 Q -> py Q <= b) ->
    b < py p ->
    ~ between P0 P1 p.
Proof.
  intros P0 P1 p b Hbound Hgt Hbet.
  apply (Rlt_not_le (py p) b); [ exact Hgt | ].
  apply Hbound. exact Hbet.
Qed.

Lemma segment_exterior_above :
  forall P0 P1 b p,
    (forall Q, between P0 P1 Q -> py Q <= b) ->
    py p = b + 1 ->
    seg_in_stratum LSExt P0 P1 p.
Proof.
  intros P0 P1 b p Hbound Hpy.
  unfold seg_in_stratum. simpl.
  apply above_segment_not_on with (b := b); [ exact Hbound | ].
  rewrite Hpy. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Point-set DE-9IM specification for a segment pair.                     *)
(* -------------------------------------------------------------------------- *)

Definition line_cell_ok (d : DimValue) (sX sY : LineStratum)
    (A B C D : Point) : Prop :=
  dim_value_ok d /\
  (dim_nonempty d <->
   exists p : Point, seg_in_stratum sX A B p /\ seg_in_stratum sY C D p).

Definition line_de9im_pointset (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ii m) LSInt LSInt A B C D /\
  line_cell_ok (im_ib m) LSInt LSBnd A B C D /\
  line_cell_ok (im_ie m) LSInt LSExt A B C D /\
  line_cell_ok (im_bi m) LSBnd LSInt A B C D /\
  line_cell_ok (im_bb m) LSBnd LSBnd A B C D /\
  line_cell_ok (im_be m) LSBnd LSExt A B C D /\
  line_cell_ok (im_ei m) LSExt LSInt A B C D /\
  line_cell_ok (im_eb m) LSExt LSBnd A B C D /\
  line_cell_ok (im_ee m) LSExt LSExt A B C D.

Definition line_no_ib_meet (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ii m) LSInt LSInt A B C D /\
  line_cell_ok (im_ib m) LSInt LSBnd A B C D /\
  line_cell_ok (im_bi m) LSBnd LSInt A B C D /\
  line_cell_ok (im_bb m) LSBnd LSBnd A B C D.

Definition line_point_ii_ib_meet (A B C D : Point) (m : IntersectionMatrix) : Prop :=
  line_cell_ok (im_ii m) LSInt LSInt A B C D /\
  line_cell_ok (im_ib m) LSInt LSBnd A B C D /\
  line_cell_ok (im_bi m) LSBnd LSInt A B C D /\
  line_cell_ok (im_bb m) LSBnd LSBnd A B C D.

Lemma line_cell_ok_none_when :
  forall sX sY A B C D,
    ~ (exists p : Point, seg_in_stratum sX A B p /\ seg_in_stratum sY C D p) ->
    line_cell_ok None sX sY A B C D.
Proof.
  intros sX sY A B C D Hempty. split; [ exact I | ].
  split.
  - intro Hdn. exfalso. apply Hdn. reflexivity.
  - intros Hex. exfalso. apply Hempty. exact Hex.
Qed.

(* Parametric core of the dim-indexed family below: any in-range dimension
   value is witnessed by a single shared point.  The three named instances
   (dim0/dim1/dim2) are the citable surface; keep using those downstream. *)
Lemma line_cell_ok_some :
  forall n sX sY A B C D p,
    (n <= 2)%nat ->
    seg_in_stratum sX A B p ->
    seg_in_stratum sY C D p ->
    line_cell_ok (Some n) sX sY A B C D.
Proof.
  intros n sX sY A B C D p Hn HsX HsY.
  split.
  - exact Hn.
  - split; [ intros _; exists p; split; assumption | ].
    intros [p' [Hp' _]]. intro H. discriminate H.
Qed.

Lemma line_cell_ok_dim0 :
  forall sX sY A B C D p,
    seg_in_stratum sX A B p ->
    seg_in_stratum sY C D p ->
    line_cell_ok (Some 0%nat) sX sY A B C D.
Proof.
  intros sX sY A B C D p HsX HsY.
  apply (line_cell_ok_some 0 sX sY A B C D p);
    [ repeat constructor | assumption | assumption ].
Qed.

Lemma line_cell_ok_dim1 :
  forall sX sY A B C D p,
    seg_in_stratum sX A B p ->
    seg_in_stratum sY C D p ->
    line_cell_ok (Some 1%nat) sX sY A B C D.
Proof.
  intros sX sY A B C D p HsX HsY.
  apply (line_cell_ok_some 1 sX sY A B C D p);
    [ repeat constructor | assumption | assumption ].
Qed.

Lemma line_cell_ok_dim2 :
  forall sX sY A B C D p,
    seg_in_stratum sX A B p ->
    seg_in_stratum sY C D p ->
    line_cell_ok (Some 2%nat) sX sY A B C D.
Proof.
  intros sX sY A B C D p HsX HsY.
  apply (line_cell_ok_some 2 sX sY A B C D p);
    [ repeat constructor | assumption | assumption ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Exterior meet — two bounded segments share an exterior point.          *)
(* -------------------------------------------------------------------------- *)

Definition segment_py_ub (P0 P1 : Point) : R :=
  Rmax (py P0) (py P1).

Lemma two_segments_exterior_meet :
  forall A B C D : Point,
    exists p : Point,
      seg_in_stratum LSExt A B p /\ seg_in_stratum LSExt C D p.
Proof.
  intros A B C D.
  set (b := Rmax (segment_py_ub A B) (segment_py_ub C D)).
  exists (mkPoint 0 (b + 1)).
  split.
  - apply segment_exterior_above with (b := b).
    + intros Q Hbet. eapply Rle_trans.
      * apply between_py_le_max; exact Hbet.
      * apply Rmax_l.
    + reflexivity.
  - apply segment_exterior_above with (b := b).
    + intros Q Hbet. eapply Rle_trans.
      * apply between_py_le_max; exact Hbet.
      * apply Rmax_r.
    + reflexivity.
Qed.

Lemma line_de9im_ee_inhabited :
  forall A B C D m,
    line_de9im_pointset A B C D m ->
    dim_nonempty (im_ee m).
Proof.
  intros A B C D m H.
  destruct H as [_ [_ [_ [_ [_ [_ [_ [_ Hee]]]]]]]].
  destruct (two_segments_exterior_meet A B C D) as [p [HA HB]].
  apply Hee. exists p. split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §13  Matrix well-formedness corollary.                                     *)
(* -------------------------------------------------------------------------- *)

Theorem line_de9im_matrix_ok :
  forall A B C D m,
    line_de9im_pointset A B C D m -> matrix_ok m.
Proof.
  intros A B C D m H.
  destruct H as [Hii [Hib [Hie [Hbi [Hbb [Hbe [Hei [Heb Hee]]]]]]]].
  unfold matrix_ok. repeat split;
    [ apply (proj1 Hii) | apply (proj1 Hib) | apply (proj1 Hie)
    | apply (proj1 Hbi) | apply (proj1 Hbb) | apply (proj1 Hbe)
    | apply (proj1 Hei) | apply (proj1 Heb) | apply (proj1 Hee) ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions two_segments_exterior_meet.
Print Assumptions line_de9im_ee_inhabited.
