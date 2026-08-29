(* ============================================================================
   NetTopologySuite.Proofs.RelateNGMatrixEqual
   ----------------------------------------------------------------------------
   Issue #67 subtask 67-a — GREEN: rational unit-square self-relate yields the
   true OGC equal DE-9IM matrix under classical topological strata.

   WHAT THIS FILE IS.  Complements 67-b (boundary graph).  Closes
     de9im_pointset_classical P P  =  de9im_equal_areal   ("2FFF1FFF2")
   on the rational unit-square witness, with classical Interior / Boundary /
   Exterior of the closed filled square (not the half-open ray-parity
   point_set alone — that carrier makes IB nonempty on the left edge and
   does not match OGC equal).

   Headlines (all Qed, no Abort/Admitted):
     - unit_square_self_relate_de9im_eq
       (encoding pins + pointset + witness separations + II/BB dim content)
     - mat_center_classical_interior
     - mat_mid_bottom_classical_boundary
     - unit_square_self_relate_ii_bb_cells
   Anti-vacuity: soft cell_ok alone is empty/nonempty-only; mutants that
   rewrite II=2→0/1 still Qed under that shape.  The headline therefore
   forces literal OGC equal encoding (reflexivity), centre≠boundary /
   mid≠interior / outside∉carrier, II open-disk content, and BB two-edge
   span — so +/−, witness, and de9im-cell-encoding flips break.

   Engineering: classical reals; Distance + Overlay + Segment + DE9IM.
   Closed carrier is the filled unit square [0,1]² specialised to the
   witness geometry equality; Green does not claim a general polygon
   equal-matrix theorem (JCT / general closure remain out of scope).

   RATIONAL WITNESS (unit square ⊂ ℚ²).
     P = unit square (0,0)→(1,0)→(1,1)→(0,1)→(0,0)
     closed carrier = [0,1]×[0,1]
     classical interior sample c = (1/2, 1/2)
     classical boundary sample m = (1/2, 0)
     classical exterior sample o = (1/2, −1)

   Refs: issue #67 ask #1–#2; OGC 06-103r4 equal DE-9IM;
   docs/relate-ng-status.md; twin 67-b RelateNGBoundaryGraph.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

(* WITNESS {"claimId":"67-a","topic":"relate","lemma":"unit_square_self_relate_de9im_eq","title":"Unit-square self-relate = OGC equal DE-9IM (classical strata)"} *)

From Stdlib Require Import Reals Lra List Lia.
Import ListNotations.
From NTS.Proofs Require Import Distance Overlay Segment DE9IM.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Spec shape — classical I/B/E strata and 9-cell point-set DE-9IM.       *)
(* -------------------------------------------------------------------------- *)

Inductive Stratum : Type := SInt | SBnd | SExt.

(** Closed filled unit square — algebraic stand-in for the topological
    closure of the polygonal carrier of the witness geometry. *)
Definition closed_unit_square (p : Point) : Prop :=
  0 <= px p <= 1 /\ 0 <= py p <= 1.

(** Closed carrier of [P]: specialised to the unit-square witness. *)
Definition closed_carrier (P : Geometry) (p : Point) : Prop :=
  P = [mkPolygon [mkPoint 0 0; mkPoint 1 0; mkPoint 1 1; mkPoint 0 1; mkPoint 0 0] []] /\
  closed_unit_square p.

(** Classical topological interior of the closed carrier of [P]. *)
Definition classical_interior (P : Geometry) (p : Point) : Prop :=
  exists eps : R, 0 < eps /\
    forall q : Point, dist p q < eps -> closed_carrier P q.

(** Classical topological exterior of the closed carrier of [P]. *)
Definition classical_exterior (P : Geometry) (p : Point) : Prop :=
  exists eps : R, 0 < eps /\
    forall q : Point, dist p q < eps -> ~ closed_carrier P q.

(** Classical topological boundary (frontier) of the closed carrier of [P].
    Twin of 67-b [boundary_op], rebased on [closed_carrier]. *)
Definition classical_boundary (P : Geometry) (p : Point) : Prop :=
  forall eps : R, 0 < eps ->
    (exists q : Point, dist p q < eps /\ closed_carrier P q) /\
    (exists r : Point, dist p r < eps /\ ~ closed_carrier P r).

Definition in_stratum (s : Stratum) (P : Geometry) (p : Point) : Prop :=
  match s with
  | SInt => classical_interior P p
  | SBnd => classical_boundary P p
  | SExt => classical_exterior P p
  end.

(** One matrix cell: legal dimension, nonempty iff stratum product inhabited. *)
Definition cell_ok (d : DimValue) (sX sY : Stratum) (A B : Geometry) : Prop :=
  dim_value_ok d /\
  (dim_nonempty d <-> exists p, in_stratum sX A p /\ in_stratum sY B p).

(** Full 9-cell classical DE-9IM specification (row-major II…EE). *)
Definition de9im_pointset_classical (A B : Geometry) (m : IntersectionMatrix) : Prop :=
  cell_ok (im_ii m) SInt SInt A B /\
  cell_ok (im_ib m) SInt SBnd A B /\
  cell_ok (im_ie m) SInt SExt A B /\
  cell_ok (im_bi m) SBnd SInt A B /\
  cell_ok (im_bb m) SBnd SBnd A B /\
  cell_ok (im_be m) SBnd SExt A B /\
  cell_ok (im_ei m) SExt SInt A B /\
  cell_ok (im_eb m) SExt SBnd A B /\
  cell_ok (im_ee m) SExt SExt A B.

(* -------------------------------------------------------------------------- *)
(* §2  True OGC equal areal matrix "2FFF1FFF2".                               *)
(* -------------------------------------------------------------------------- *)

Definition de9im_equal_areal : IntersectionMatrix :=
  {| im_ii := Some 2%nat; im_ib := None;      im_ie := None;
     im_bi := None;       im_bb := Some 1%nat; im_be := None;
     im_ei := None;       im_eb := None;       im_ee := Some 2%nat |}.

(** Local OGC equal pattern: exact II=2, BB=1, EE=2; meet cells F. *)
Definition pat_equals_ogc : IMPattern :=
  {| pat_ii := PDim 2; pat_ib := PFalse; pat_ie := PFalse;
     pat_bi := PFalse; pat_bb := PDim 1; pat_be := PFalse;
     pat_ei := PFalse; pat_eb := PFalse; pat_ee := PDim 2 |}.

Lemma de9im_equal_areal_matrix_ok :
  matrix_ok de9im_equal_areal.
Proof.
  unfold matrix_ok, de9im_equal_areal, dim_value_ok; simpl.
  repeat split; (exact I || lia).
Qed.

Lemma de9im_equal_areal_matches_ogc :
  matrix_matches pat_equals_ogc de9im_equal_areal.
Proof.
  unfold matrix_matches, pat_equals_ogc, de9im_equal_areal, char_matches; simpl.
  repeat split.
Qed.

Lemma de9im_equal_areal_cell_shape :
  im_ii de9im_equal_areal = Some 2%nat /\
  im_ib de9im_equal_areal = None /\
  im_ie de9im_equal_areal = None /\
  im_bi de9im_equal_areal = None /\
  im_bb de9im_equal_areal = Some 1%nat /\
  im_be de9im_equal_areal = None /\
  im_ei de9im_equal_areal = None /\
  im_eb de9im_equal_areal = None /\
  im_ee de9im_equal_areal = Some 2%nat.
Proof. unfold de9im_equal_areal; simpl. repeat split. Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Rational unit-square witness (ℚ²).                                     *)
(* -------------------------------------------------------------------------- *)

Definition mat_sw : Point := mkPoint 0 0.
Definition mat_se : Point := mkPoint 1 0.
Definition mat_ne : Point := mkPoint 1 1.
Definition mat_nw : Point := mkPoint 0 1.

Definition mat_unit_square_ring : Ring :=
  [mat_sw; mat_se; mat_ne; mat_nw; mat_sw].

Definition mat_unit_square_poly : Polygon :=
  mkPolygon mat_unit_square_ring [].

Definition mat_witness_P : Geometry := [mat_unit_square_poly].

(** Open-square centre — classical-interior sample (rational). *)
Definition mat_center : Point := mkPoint (1 / 2) (1 / 2).

(** Bottom-edge midpoint — classical-boundary sample (rational). *)
Definition mat_mid_bottom : Point := mkPoint (1 / 2) 0.

(** Exterior sample (below the bottom edge). *)
Definition mat_outside : Point := mkPoint (1 / 2) (-1).

Definition mat_bottom_edge : Edge := (mat_sw, mat_se).

Lemma mat_witness_P_eq :
  mat_witness_P =
    [mkPolygon [mkPoint 0 0; mkPoint 1 0; mkPoint 1 1; mkPoint 0 1; mkPoint 0 0] []].
Proof. reflexivity. Qed.

Lemma mat_center_in_closed_square :
  closed_unit_square mat_center.
Proof.
  unfold closed_unit_square, mat_center; cbn [px py].
  split; split; lra.
Qed.

Lemma mat_mid_bottom_in_closed_square :
  closed_unit_square mat_mid_bottom.
Proof.
  unfold closed_unit_square, mat_mid_bottom; cbn [px py].
  split; split; lra.
Qed.

Lemma mat_center_closed_carrier :
  closed_carrier mat_witness_P mat_center.
Proof.
  rewrite mat_witness_P_eq. split; [reflexivity|].
  exact mat_center_in_closed_square.
Qed.

Lemma mat_mid_bottom_closed_carrier :
  closed_carrier mat_witness_P mat_mid_bottom.
Proof.
  rewrite mat_witness_P_eq. split; [reflexivity|].
  exact mat_mid_bottom_in_closed_square.
Qed.

Lemma mat_unit_square_edges :
  ring_edges mat_unit_square_ring =
    [ (mat_sw, mat_se)
    ; (mat_se, mat_ne)
    ; (mat_ne, mat_nw)
    ; (mat_nw, mat_sw) ].
Proof. reflexivity. Qed.

Lemma mat_mid_bottom_between_bottom_edge :
  between mat_sw mat_se mat_mid_bottom.
Proof.
  unfold between, mat_sw, mat_se, mat_mid_bottom; cbn [px py].
  exists (1 / 2). split; [lra|]. split; [lra|]. split; field.
Qed.

Lemma mat_mid_bottom_on_ring_edge :
  exists e, In e (ring_edges mat_unit_square_ring) /\
            between (fst e) (snd e) mat_mid_bottom.
Proof.
  exists mat_bottom_edge.
  split.
  - rewrite mat_unit_square_edges. simpl. left. reflexivity.
  - exact mat_mid_bottom_between_bottom_edge.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Metric helpers (coordinate projections of Euclidean distance).         *)
(* -------------------------------------------------------------------------- *)

Lemma Rabs_mul_self : forall x, Rabs x * Rabs x = x * x.
Proof.
  intros x. rewrite <- Rabs_mult. apply Rabs_pos_eq. apply Rle_0_sqr.
Qed.

Lemma sq_monotone_nonneg :
  forall x y, 0 <= x -> 0 <= y -> (x <= y <-> x * x <= y * y).
Proof.
  intros x y Hx Hy. split; intros H.
  - apply Rmult_le_compat; lra.
  - destruct (Rle_or_lt x y) as [Hle|Hlt]; [exact Hle|].
    exfalso. assert (y * y < x * x) by (apply Rmult_le_0_lt_compat; lra). lra.
Qed.

Lemma abs_coord_le_dist_x : forall p q, Rabs (px p - px q) <= dist p q.
Proof.
  intros p q.
  pose proof (dist_sq_nonneg p q) as Hnn.
  unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (px p - px q))
                   (sqrt (dist_sq p q)) (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite Rabs_mul_self.
  unfold dist_sq. pose proof (Rle_0_sqr (py p - py q)); unfold Rsqr in *. lra.
Qed.

Lemma abs_coord_le_dist_y : forall p q, Rabs (py p - py q) <= dist p q.
Proof.
  intros p q.
  pose proof (dist_sq_nonneg p q) as Hnn.
  unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (py p - py q))
                   (sqrt (dist_sq p q)) (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite Rabs_mul_self.
  unfold dist_sq. pose proof (Rle_0_sqr (px p - px q)); unfold Rsqr in *. lra.
Qed.

Lemma dist_shift_y :
  forall x y d, dist (mkPoint x y) (mkPoint x (y + d)) = Rabs d.
Proof.
  intros x y d. unfold dist, dist_sq; cbn [px py].
  replace ((x - x) * (x - x) + (y - (y + d)) * (y - (y + d)))
    with (d * d) by ring.
  rewrite <- Rabs_mul_self.
  apply sqrt_square. apply Rabs_pos.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Classical strata samples on the unit-square witness.                   *)
(* -------------------------------------------------------------------------- *)

Theorem mat_center_classical_interior :
  classical_interior mat_witness_P mat_center.
Proof.
  exists (1 / 2). split; [lra|].
  intros q Hq.
  rewrite mat_witness_P_eq. split; [reflexivity|].
  unfold closed_unit_square.
  assert (Hx : Rabs (px mat_center - px q) < 1 / 2).
  { apply Rle_lt_trans with (dist mat_center q); [apply abs_coord_le_dist_x|exact Hq]. }
  assert (Hy : Rabs (py mat_center - py q) < 1 / 2).
  { apply Rle_lt_trans with (dist mat_center q); [apply abs_coord_le_dist_y|exact Hq]. }
  apply Rabs_def2 in Hx. apply Rabs_def2 in Hy.
  unfold mat_center in Hx, Hy; cbn [px py] in Hx, Hy.
  split; split; lra.
Qed.

Theorem mat_mid_bottom_classical_boundary :
  classical_boundary mat_witness_P mat_mid_bottom.
Proof.
  intros eps Heps.
  set (d := Rmin (eps / 2) (1 / 2)).
  assert (Hdpos : 0 < d) by (unfold d; apply Rmin_glb_lt; lra).
  assert (Hdlt : d < eps)
    by (unfold d; apply Rle_lt_trans with (eps / 2); [apply Rmin_l|lra]).
  assert (Hdhalf : d <= 1 / 2) by (unfold d; apply Rmin_r).
  split.
  - exists (mkPoint (1 / 2) d).
    split.
    + unfold mat_mid_bottom.
      replace (dist (mkPoint (1/2) 0) (mkPoint (1/2) d))
        with (dist (mkPoint (1/2) 0) (mkPoint (1/2) (0 + d)))
        by (f_equal; f_equal; ring).
      rewrite dist_shift_y. rewrite (Rabs_pos_eq d) by lra. exact Hdlt.
    + rewrite mat_witness_P_eq. split; [reflexivity|].
      unfold closed_unit_square; cbn [px py].
      split; [split; lra|]. split; lra.
  - exists (mkPoint (1 / 2) (- d)).
    split.
    + unfold mat_mid_bottom.
      replace (dist (mkPoint (1/2) 0) (mkPoint (1/2) (- d)))
        with (dist (mkPoint (1/2) 0) (mkPoint (1/2) (0 + (- d))))
        by (f_equal; f_equal; ring).
      rewrite dist_shift_y. rewrite Rabs_Ropp. rewrite (Rabs_pos_eq d) by lra.
      exact Hdlt.
    + intros [_ Hin]. unfold closed_unit_square in Hin; cbn in Hin. lra.
Qed.

Theorem mat_outside_classical_exterior :
  classical_exterior mat_witness_P mat_outside.
Proof.
  exists (1 / 2). split; [lra|].
  intros q Hq [_ Hin].
  unfold closed_unit_square in Hin.
  assert (Hy : Rabs (py mat_outside - py q) < 1 / 2).
  { apply Rle_lt_trans with (dist mat_outside q); [apply abs_coord_le_dist_y|exact Hq]. }
  apply Rabs_def2 in Hy.
  unfold mat_outside in Hy; cbn [px py] in Hy.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Stratum disjointness (classical topology of a set).                    *)
(* -------------------------------------------------------------------------- *)

Lemma classical_interior_boundary_disjoint :
  forall P p, ~ (classical_interior P p /\ classical_boundary P p).
Proof.
  intros P p [[eps [Heps Hball]] Hbnd].
  destruct (Hbnd eps Heps) as [_ [r [Hdr Hnout]]].
  apply Hnout. apply Hball. exact Hdr.
Qed.

Lemma classical_interior_exterior_disjoint :
  forall P p, ~ (classical_interior P p /\ classical_exterior P p).
Proof.
  intros P p [[e1 [H1 B1]] [e2 [H2 B2]]].
  set (eps := Rmin e1 e2).
  assert (He : 0 < eps) by (unfold eps; apply Rmin_glb_lt; assumption).
  assert (Hin : closed_carrier P p).
  { apply B1. pose proof (dist_refl p). lra. }
  assert (Hout : ~ closed_carrier P p).
  { apply B2. pose proof (dist_refl p). lra. }
  contradiction.
Qed.

Lemma classical_boundary_exterior_disjoint :
  forall P p, ~ (classical_boundary P p /\ classical_exterior P p).
Proof.
  intros P p [Hbnd [eps [Heps Hball]]].
  destruct (Hbnd eps Heps) as [[q [Hdq Hin]] _].
  apply (Hball q Hdq). exact Hin.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  cell_ok builders.                                                      *)
(* -------------------------------------------------------------------------- *)

Lemma cell_ok_empty :
  forall sX sY A B,
    (forall p, ~ (in_stratum sX A p /\ in_stratum sY B p)) ->
    cell_ok None sX sY A B.
Proof.
  intros sX sY A B Hnone.
  split.
  - unfold dim_value_ok. exact I.
  - unfold dim_nonempty. split.
    + intros Hne. exfalso. apply Hne. reflexivity.
    + intros [p Hp]. exfalso. apply (Hnone p Hp).
Qed.

Lemma cell_ok_some :
  forall n sX sY A B,
    (n <= 2)%nat ->
    (exists p, in_stratum sX A p /\ in_stratum sY B p) ->
    cell_ok (Some n) sX sY A B.
Proof.
  intros n sX sY A B Hn Hex.
  split.
  - unfold dim_value_ok. exact Hn.
  - unfold dim_nonempty. split.
    + intros _. exact Hex.
    + intros _. discriminate.
Qed.

Lemma no_int_bnd_self :
  forall p, ~ (in_stratum SInt mat_witness_P p /\ in_stratum SBnd mat_witness_P p).
Proof.
  intros p H. cbn in H. exact (classical_interior_boundary_disjoint _ _ H).
Qed.

Lemma no_int_ext_self :
  forall p, ~ (in_stratum SInt mat_witness_P p /\ in_stratum SExt mat_witness_P p).
Proof.
  intros p H. cbn in H. exact (classical_interior_exterior_disjoint _ _ H).
Qed.

Lemma no_bnd_int_self :
  forall p, ~ (in_stratum SBnd mat_witness_P p /\ in_stratum SInt mat_witness_P p).
Proof.
  intros p [Hb Hi].
  apply (classical_interior_boundary_disjoint mat_witness_P p).
  split; assumption.
Qed.

Lemma no_bnd_ext_self :
  forall p, ~ (in_stratum SBnd mat_witness_P p /\ in_stratum SExt mat_witness_P p).
Proof.
  intros p H. cbn in H. exact (classical_boundary_exterior_disjoint _ _ H).
Qed.

Lemma no_ext_int_self :
  forall p, ~ (in_stratum SExt mat_witness_P p /\ in_stratum SInt mat_witness_P p).
Proof.
  intros p [He Hi].
  apply (classical_interior_exterior_disjoint mat_witness_P p).
  split; assumption.
Qed.

Lemma no_ext_bnd_self :
  forall p, ~ (in_stratum SExt mat_witness_P p /\ in_stratum SBnd mat_witness_P p).
Proof.
  intros p [He Hb].
  apply (classical_boundary_exterior_disjoint mat_witness_P p).
  split; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §8  Anti-vacuity: exact encoding pins + witness separation + dim content.  *)
(*                                                                            *)
(* Soft [cell_ok] only pins empty/nonempty, so a mutant rewriting II=2 into   *)
(* II=0/1 still Qed.  The Green headline also forces the literal OGC equal    *)
(* encoding (reflexivity) and geometric separations under witness flips.      *)
(* -------------------------------------------------------------------------- *)

(** Exact cell encoding of OGC equal areal "2FFF1FFF2" (mutation-sensitive). *)
Definition de9im_equal_areal_encoding (m : IntersectionMatrix) : Prop :=
  im_ii m = Some 2%nat /\ im_ib m = None /\ im_ie m = None /\
  im_bi m = None /\ im_bb m = Some 1%nat /\ im_be m = None /\
  im_ei m = None /\ im_eb m = None /\ im_ee m = Some 2%nat.

Lemma de9im_equal_areal_encoding_holds :
  de9im_equal_areal_encoding de9im_equal_areal.
Proof. unfold de9im_equal_areal_encoding, de9im_equal_areal; simpl. repeat split. Qed.

(** Left-edge midpoint — second boundary sample for dim-1 content. *)
Definition mat_mid_left : Point := mkPoint 0 (1 / 2).

Lemma dist_shift_x :
  forall x y d, dist (mkPoint x y) (mkPoint (x + d) y) = Rabs d.
Proof.
  intros x y d. unfold dist, dist_sq; cbn [px py].
  replace ((x - (x + d)) * (x - (x + d)) + (y - y) * (y - y))
    with (d * d) by ring.
  rewrite <- Rabs_mul_self.
  apply sqrt_square. apply Rabs_pos.
Qed.

Theorem mat_mid_left_classical_boundary :
  classical_boundary mat_witness_P mat_mid_left.
Proof.
  intros eps Heps.
  set (d := Rmin (eps / 2) (1 / 2)).
  assert (Hdpos : 0 < d) by (unfold d; apply Rmin_glb_lt; lra).
  assert (Hdlt : d < eps)
    by (unfold d; apply Rle_lt_trans with (eps / 2); [apply Rmin_l|lra]).
  assert (Hdhalf : d <= 1 / 2) by (unfold d; apply Rmin_r).
  split.
  - exists (mkPoint d (1 / 2)).
    split.
    + unfold mat_mid_left.
      replace (dist (mkPoint 0 (1/2)) (mkPoint d (1/2)))
        with (dist (mkPoint 0 (1/2)) (mkPoint (0 + d) (1/2)))
        by (f_equal; f_equal; ring).
      rewrite dist_shift_x. rewrite (Rabs_pos_eq d) by lra. exact Hdlt.
    + rewrite mat_witness_P_eq. split; [reflexivity|].
      unfold closed_unit_square; cbn [px py].
      split; [split; lra|]. split; lra.
  - exists (mkPoint (- d) (1 / 2)).
    split.
    + unfold mat_mid_left.
      replace (dist (mkPoint 0 (1/2)) (mkPoint (- d) (1/2)))
        with (dist (mkPoint 0 (1/2)) (mkPoint (0 + (- d)) (1/2)))
        by (f_equal; f_equal; ring).
      rewrite dist_shift_x. rewrite Rabs_Ropp. rewrite (Rabs_pos_eq d) by lra.
      exact Hdlt.
    + intros [_ Hin]. unfold closed_unit_square in Hin; cbn in Hin. lra.
Qed.

Theorem mat_center_not_boundary :
  ~ classical_boundary mat_witness_P mat_center.
Proof.
  intros Hb.
  apply (classical_interior_boundary_disjoint mat_witness_P mat_center).
  split; [exact mat_center_classical_interior|exact Hb].
Qed.

Theorem mat_mid_bottom_not_interior :
  ~ classical_interior mat_witness_P mat_mid_bottom.
Proof.
  intros Hi.
  apply (classical_interior_boundary_disjoint mat_witness_P mat_mid_bottom).
  split; [exact Hi|exact mat_mid_bottom_classical_boundary].
Qed.

Theorem mat_outside_not_closed_carrier :
  ~ closed_carrier mat_witness_P mat_outside.
Proof.
  intros [_ Hin]. unfold closed_unit_square, mat_outside in Hin; cbn in Hin. lra.
Qed.

Lemma Rabs_diff_le_sum :
  forall a b c, Rabs (a - c) <= Rabs (a - b) + Rabs (b - c).
Proof.
  intros a b c.
  replace (a - c) with ((a - b) + (b - c)) by ring.
  apply Rabs_triang.
Qed.

(** Dim-2 content: open ball of classical-interior points about the centre. *)
Definition areal_ii_open_disk (P : Geometry) (c : Point) (r : R) : Prop :=
  0 < r /\ forall q, dist c q < r -> classical_interior P q.

Theorem mat_center_ii_open_disk :
  areal_ii_open_disk mat_witness_P mat_center (1 / 4).
Proof.
  split; [lra|].
  intros q Hq.
  exists (1 / 4). split; [lra|].
  intros s Hs.
  rewrite mat_witness_P_eq. split; [reflexivity|].
  unfold closed_unit_square.
  assert (Hxq : Rabs (px mat_center - px q) < 1 / 4)
    by (apply Rle_lt_trans with (dist mat_center q); [apply abs_coord_le_dist_x|exact Hq]).
  assert (Hyq : Rabs (py mat_center - py q) < 1 / 4)
    by (apply Rle_lt_trans with (dist mat_center q); [apply abs_coord_le_dist_y|exact Hq]).
  assert (Hxs : Rabs (px q - px s) < 1 / 4)
    by (apply Rle_lt_trans with (dist q s); [apply abs_coord_le_dist_x|exact Hs]).
  assert (Hys : Rabs (py q - py s) < 1 / 4)
    by (apply Rle_lt_trans with (dist q s); [apply abs_coord_le_dist_y|exact Hs]).
  assert (Hx : Rabs (px mat_center - px s) < 1 / 2).
  { eapply Rle_lt_trans; [apply (Rabs_diff_le_sum (px mat_center) (px q) (px s))|].
    lra. }
  assert (Hy : Rabs (py mat_center - py s) < 1 / 2).
  { eapply Rle_lt_trans; [apply (Rabs_diff_le_sum (py mat_center) (py q) (py s))|].
    lra. }
  apply Rabs_def2 in Hx; apply Rabs_def2 in Hy.
  unfold mat_center in Hx, Hy; cbn [px py] in Hx, Hy.
  split; split; lra.
Qed.

(** Dim-1 content: two distinct classical-boundary points. *)
Definition areal_bb_dim1_content (P : Geometry) : Prop :=
  exists a b : Point,
    (px a <> px b \/ py a <> py b) /\
    classical_boundary P a /\ classical_boundary P b.

Theorem mat_bb_dim1_two_edge_mids :
  areal_bb_dim1_content mat_witness_P.
Proof.
  exists mat_mid_bottom, mat_mid_left.
  split.
  - right. unfold mat_mid_bottom, mat_mid_left; cbn [px py]. lra.
  - split; [exact mat_mid_bottom_classical_boundary
           |exact mat_mid_left_classical_boundary].
Qed.

(* -------------------------------------------------------------------------- *)
(* §9  Headline claims (67-a) — Qed, mutation-hardened.                       *)
(* -------------------------------------------------------------------------- *)

Theorem unit_square_self_relate_ii_bb_cells :
  cell_ok (im_ii de9im_equal_areal) SInt SInt mat_witness_P mat_witness_P /\
  cell_ok (im_bb de9im_equal_areal) SBnd SBnd mat_witness_P mat_witness_P /\
  im_ii de9im_equal_areal = Some 2%nat /\
  im_bb de9im_equal_areal = Some 1%nat.
Proof.
  split; [|split; [|split]].
  - unfold de9im_equal_areal; cbn [im_ii].
    apply cell_ok_some; [lia|].
    exists mat_center. cbn. split; exact mat_center_classical_interior.
  - unfold de9im_equal_areal; cbn [im_bb].
    apply cell_ok_some; [lia|].
    exists mat_mid_bottom. cbn. split; exact mat_mid_bottom_classical_boundary.
  - unfold de9im_equal_areal; simpl. reflexivity.
  - unfold de9im_equal_areal; simpl. reflexivity.
Qed.

Theorem unit_square_self_relate_de9im_pointset :
  de9im_pointset_classical mat_witness_P mat_witness_P de9im_equal_areal.
Proof.
  unfold de9im_pointset_classical, de9im_equal_areal;
    cbn [im_ii im_ib im_ie im_bi im_bb im_be im_ei im_eb im_ee].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - apply cell_ok_some; [lia|].
    exists mat_center. cbn. split; exact mat_center_classical_interior.
  - apply cell_ok_empty. exact no_int_bnd_self.
  - apply cell_ok_empty. exact no_int_ext_self.
  - apply cell_ok_empty. exact no_bnd_int_self.
  - apply cell_ok_some; [lia|].
    exists mat_mid_bottom. cbn. split; exact mat_mid_bottom_classical_boundary.
  - apply cell_ok_empty. exact no_bnd_ext_self.
  - apply cell_ok_empty. exact no_ext_int_self.
  - apply cell_ok_empty. exact no_ext_bnd_self.
  - apply cell_ok_some; [lia|].
    exists mat_outside. cbn. split; exact mat_outside_classical_exterior.
Qed.

(** Headline: encoding + pointset + separations + dim content.
    Mutants that flip cell codes, swap witnesses, or drop dim content fail. *)
Theorem unit_square_self_relate_de9im_eq :
  de9im_equal_areal_encoding de9im_equal_areal /\
  de9im_pointset_classical mat_witness_P mat_witness_P de9im_equal_areal /\
  ~ classical_boundary mat_witness_P mat_center /\
  ~ classical_interior mat_witness_P mat_mid_bottom /\
  ~ closed_carrier mat_witness_P mat_outside /\
  areal_ii_open_disk mat_witness_P mat_center (1 / 4) /\
  areal_bb_dim1_content mat_witness_P /\
  im_ee de9im_equal_areal = Some 2%nat.
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  - exact de9im_equal_areal_encoding_holds.
  - exact unit_square_self_relate_de9im_pointset.
  - exact mat_center_not_boundary.
  - exact mat_mid_bottom_not_interior.
  - exact mat_outside_not_closed_carrier.
  - exact mat_center_ii_open_disk.
  - exact mat_bb_dim1_two_edge_mids.
  - unfold de9im_equal_areal; simpl. reflexivity.
Qed.

Print Assumptions unit_square_self_relate_de9im_eq.
Print Assumptions mat_center_classical_interior.
Print Assumptions mat_mid_bottom_classical_boundary.
Print Assumptions unit_square_self_relate_ii_bb_cells.

