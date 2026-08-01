(* ============================================================================
   nts-eval micro unit — claimId 67-a (GREEN)
   ----------------------------------------------------------------------------
   Unit-square self-relate yields OGC equal DE-9IM under classical strata.
   Self-contained classical-reals micro-kernel; no NTS.Proofs Requires.
   Mirrors theories/RelateNGMatrixEqual.v.

   WITNESS claimId: 67-a
   Lemma: unit_square_self_relate_de9im_eq
   ========================================================================== *)

(* WITNESS {"claimId":"67-a","topic":"relate","lemma":"unit_square_self_relate_de9im_eq","title":"Unit-square self-relate = OGC equal DE-9IM (classical strata)"} *)

From Stdlib Require Import Reals Lra List Lia.
Import ListNotations.
Local Open Scope R_scope.

(* ---- Minimal geometry + DE-9IM carriers ----------------------------------- *)

Record Point : Type := mkPoint { px : R; py : R }.

Definition dist_sq (p q : Point) : R :=
  (px p - px q) * (px p - px q) + (py p - py q) * (py p - py q).
Definition dist (p q : Point) : R := sqrt (dist_sq p q).

Definition Ring : Type := list Point.
Definition Edge : Type := (Point * Point)%type.
Record Polygon : Type := mkPolygon { outer_ring : Ring; hole_rings : list Ring }.
Definition Geometry : Type := list Polygon.

Fixpoint ring_edges (r : Ring) : list Edge :=
  match r with
  | a :: r' => match r' with | b :: _ => (a, b) :: ring_edges r' | nil => nil end
  | nil => nil
  end.

Definition between (P0 P1 Q : Point) : Prop :=
  exists t : R, 0 <= t /\ t <= 1 /\
    px Q = (1 - t) * px P0 + t * px P1 /\
    py Q = (1 - t) * py P0 + t * py P1.

Definition DimValue := option nat.
Definition dim_nonempty (d : DimValue) : Prop := d <> None.
Definition dim_value_ok (d : DimValue) : Prop :=
  match d with | None => True | Some n => (n <= 2)%nat end.

Record IntersectionMatrix : Type := mkIM {
  im_ii : DimValue; im_ib : DimValue; im_ie : DimValue;
  im_bi : DimValue; im_bb : DimValue; im_be : DimValue;
  im_ei : DimValue; im_eb : DimValue; im_ee : DimValue
}.

Definition matrix_ok (m : IntersectionMatrix) : Prop :=
  dim_value_ok (im_ii m) /\ dim_value_ok (im_ib m) /\ dim_value_ok (im_ie m) /\
  dim_value_ok (im_bi m) /\ dim_value_ok (im_bb m) /\ dim_value_ok (im_be m) /\
  dim_value_ok (im_ei m) /\ dim_value_ok (im_eb m) /\ dim_value_ok (im_ee m).

(* ---- Classical strata + 9-cell spec --------------------------------------- *)

Inductive Stratum : Type := SInt | SBnd | SExt.

Definition closed_unit_square (p : Point) : Prop :=
  0 <= px p <= 1 /\ 0 <= py p <= 1.

Definition closed_carrier (P : Geometry) (p : Point) : Prop :=
  P = [mkPolygon [mkPoint 0 0; mkPoint 1 0; mkPoint 1 1; mkPoint 0 1; mkPoint 0 0] []] /\
  closed_unit_square p.

Definition classical_interior (P : Geometry) (p : Point) : Prop :=
  exists eps : R, 0 < eps /\
    forall q : Point, dist p q < eps -> closed_carrier P q.

Definition classical_exterior (P : Geometry) (p : Point) : Prop :=
  exists eps : R, 0 < eps /\
    forall q : Point, dist p q < eps -> ~ closed_carrier P q.

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

Definition cell_ok (d : DimValue) (sX sY : Stratum) (A B : Geometry) : Prop :=
  dim_value_ok d /\
  (dim_nonempty d <-> exists p, in_stratum sX A p /\ in_stratum sY B p).

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

(* ---- OGC equal areal "2FFF1FFF2" ------------------------------------------ *)

Definition de9im_equal_areal : IntersectionMatrix :=
  {| im_ii := Some 2%nat; im_ib := None;      im_ie := None;
     im_bi := None;       im_bb := Some 1%nat; im_be := None;
     im_ei := None;       im_eb := None;       im_ee := Some 2%nat |}.

Lemma de9im_equal_areal_matrix_ok :
  matrix_ok de9im_equal_areal.
Proof.
  unfold matrix_ok, de9im_equal_areal, dim_value_ok; simpl.
  repeat split; (exact I || lia).
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

(* ---- Rational unit-square witness ----------------------------------------- *)

Definition mat_sw : Point := mkPoint 0 0.
Definition mat_se : Point := mkPoint 1 0.
Definition mat_ne : Point := mkPoint 1 1.
Definition mat_nw : Point := mkPoint 0 1.

Definition mat_unit_square_ring : Ring :=
  [mat_sw; mat_se; mat_ne; mat_nw; mat_sw].

Definition mat_witness_P : Geometry :=
  [mkPolygon mat_unit_square_ring []].

Definition mat_center : Point := mkPoint (1 / 2) (1 / 2).
Definition mat_mid_bottom : Point := mkPoint (1 / 2) 0.
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

(* ---- Metric helpers ------------------------------------------------------- *)

Lemma dist_sq_nonneg : forall p q, 0 <= dist_sq p q.
Proof.
  intros p q. unfold dist_sq.
  pose proof (Rle_0_sqr (px p - px q)). pose proof (Rle_0_sqr (py p - py q)).
  unfold Rsqr in *. lra.
Qed.

Lemma dist_nonneg : forall p q, 0 <= dist p q.
Proof. intros p q. unfold dist. apply sqrt_pos. Qed.

Lemma dist_refl : forall p, dist p p = 0.
Proof.
  intros p. unfold dist, dist_sq.
  replace ((px p - px p)*(px p - px p) + (py p - py p)*(py p - py p))
    with 0 by ring.
  apply sqrt_0.
Qed.

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
  intros x y d. unfold dist, dist_sq; cbn.
  replace ((x-x)*(x-x)+(y-(y+d))*(y-(y+d))) with (d*d) by ring.
  destruct (Rle_dec 0 d) as [Hd|Hd].
  - rewrite (Rabs_pos_eq d Hd). rewrite (sqrt_square d Hd). reflexivity.
  - apply Rnot_le_lt in Hd. rewrite (Rabs_left d Hd).
    replace (d * d) with ((- d) * (- d)) by ring.
    rewrite (sqrt_square (- d)) by lra. reflexivity.
Qed.

(* ---- Strata samples ------------------------------------------------------- *)

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

(* ---- Stratum disjointness ------------------------------------------------- *)

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

(* ---- cell_ok builders ----------------------------------------------------- *)

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

(* ---- Headlines (67-a) — Qed ----------------------------------------------- *)

Theorem unit_square_self_relate_ii_bb_cells :
  cell_ok (im_ii de9im_equal_areal) SInt SInt mat_witness_P mat_witness_P /\
  cell_ok (im_bb de9im_equal_areal) SBnd SBnd mat_witness_P mat_witness_P.
Proof.
  split.
  - unfold de9im_equal_areal; cbn [im_ii].
    apply cell_ok_some; [lia|].
    exists mat_center. cbn. split; exact mat_center_classical_interior.
  - unfold de9im_equal_areal; cbn [im_bb].
    apply cell_ok_some; [lia|].
    exists mat_mid_bottom. cbn. split; exact mat_mid_bottom_classical_boundary.
Qed.

Theorem unit_square_self_relate_de9im_eq :
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

Print Assumptions unit_square_self_relate_de9im_eq.
Print Assumptions mat_center_classical_interior.
Print Assumptions mat_mid_bottom_classical_boundary.
