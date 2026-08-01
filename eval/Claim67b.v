(* ============================================================================
   nts-eval micro unit — claimId 67-b (GREEN)
   ----------------------------------------------------------------------------
   Classical boundary operator ∂P equals the RelateNG boundary graph on the
   rational unit-square witness.  Self-contained classical-reals micro-kernel;
   no NTS.Proofs Requires.  Mirrors theories/RelateNGBoundaryGraph.v.

   WITNESS claimId: 67-b
   Lemma: boundary_op_eq_relateng_boundary_graph
   ========================================================================== *)

(* WITNESS {"claimId":"67-b","topic":"relate","lemma":"boundary_op_eq_relateng_boundary_graph","title":"Classical ∂P = RelateNG boundary graph"} *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
Local Open Scope R_scope.

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

Definition poly_edges (poly : Polygon) : list Edge :=
  ring_edges (outer_ring poly) ++ flat_map ring_edges (hole_rings poly).
Definition relateng_boundary_edges (P : Geometry) : list Edge :=
  flat_map poly_edges P.

(** Closed unit square carrier (algebraic stand-in for Overlay.point_set). *)
Definition in_closed_unit_square (p : Point) : Prop :=
  0 <= px p <= 1 /\ 0 <= py p <= 1.

Definition point_set_carrier (P : Geometry) (p : Point) : Prop :=
  P = [mkPolygon [mkPoint 0 0; mkPoint 1 0; mkPoint 1 1; mkPoint 0 1; mkPoint 0 0] []] /\
  in_closed_unit_square p.

Definition boundary_op (P : Geometry) (p : Point) : Prop :=
  forall eps : R, 0 < eps ->
    (exists q : Point, dist p q < eps /\ point_set_carrier P q) /\
    (exists r : Point, dist p r < eps /\ ~ point_set_carrier P r).

Definition RelateNGBoundaryGraph (P : Geometry) (p : Point) : Prop :=
  exists e, In e (relateng_boundary_edges P) /\ between (fst e) (snd e) p.

Definition bnd_sw : Point := mkPoint 0 0.
Definition bnd_se : Point := mkPoint 1 0.
Definition bnd_ne : Point := mkPoint 1 1.
Definition bnd_nw : Point := mkPoint 0 1.
Definition bnd_unit_square_ring : Ring := [bnd_sw; bnd_se; bnd_ne; bnd_nw; bnd_sw].
Definition bnd_witness_P : Geometry := [mkPolygon bnd_unit_square_ring []].
Definition bnd_mid_bottom : Point := mkPoint (1 / 2) 0.
Definition bnd_bottom_edge : Edge := (bnd_sw, bnd_se).

Lemma bnd_witness_P_eq :
  bnd_witness_P =
    [mkPolygon [mkPoint 0 0; mkPoint 1 0; mkPoint 1 1; mkPoint 0 1; mkPoint 0 0] []].
Proof. reflexivity. Qed.

Lemma mid_on_graph : RelateNGBoundaryGraph bnd_witness_P bnd_mid_bottom.
Proof.
  unfold RelateNGBoundaryGraph, relateng_boundary_edges, poly_edges, bnd_witness_P.
  simpl. exists bnd_bottom_edge. split; [left; reflexivity|].
  unfold between, bnd_sw, bnd_se, bnd_mid_bottom, bnd_bottom_edge; cbn.
  exists (1 / 2). split; [lra|]. split; [lra|]. split; field.
Qed.

Lemma dist_sq_nonneg : forall p q, 0 <= dist_sq p q.
Proof.
  intros p q. unfold dist_sq.
  pose proof (Rle_0_sqr (px p - px q)). pose proof (Rle_0_sqr (py p - py q)).
  unfold Rsqr in *. lra.
Qed.

Lemma dist_nonneg : forall p q, 0 <= dist p q.
Proof. intros p q. unfold dist. apply sqrt_pos. Qed.

Lemma sq_monotone_nonneg :
  forall x y, 0 <= x -> 0 <= y -> (x <= y <-> x * x <= y * y).
Proof.
  intros x y Hx Hy. split; intros H.
  - apply Rmult_le_compat; lra.
  - destruct (Rle_or_lt x y) as [Hle|Hlt]; [exact Hle|].
    exfalso. assert (y * y < x * x) by (apply Rmult_le_0_lt_compat; lra). lra.
Qed.

Lemma abs_le_dist_x : forall p q, Rabs (px p - px q) <= dist p q.
Proof.
  intros p q. pose proof (dist_sq_nonneg p q) as Hnn. unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (px p - px q)) (sqrt (dist_sq p q))
                 (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite <- Rabs_mult. rewrite (Rabs_pos_eq (_ * _)) by apply Rle_0_sqr.
  unfold dist_sq. pose proof (Rle_0_sqr (py p - py q)); unfold Rsqr in *.
  replace (Rabs (px p - px q) * Rabs (px p - px q))
    with ((px p - px q) * (px p - px q)) by
    (rewrite <- Rabs_mult; rewrite (Rabs_pos_eq (_ * _)) by apply Rle_0_sqr; ring).
  lra.
Qed.

Lemma abs_le_dist_y : forall p q, Rabs (py p - py q) <= dist p q.
Proof.
  intros p q. pose proof (dist_sq_nonneg p q) as Hnn. unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (py p - py q)) (sqrt (dist_sq p q))
                 (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite <- Rabs_mult. rewrite (Rabs_pos_eq (_ * _)) by apply Rle_0_sqr.
  unfold dist_sq. pose proof (Rle_0_sqr (px p - px q)); unfold Rsqr in *.
  replace (Rabs (py p - py q) * Rabs (py p - py q))
    with ((py p - py q) * (py p - py q)) by
    (rewrite <- Rabs_mult; rewrite (Rabs_pos_eq (_ * _)) by apply Rle_0_sqr; ring).
  lra.
Qed.

Lemma dist_vert : forall x y d,
  dist (mkPoint x y) (mkPoint x (y + d)) = Rabs d.
Proof.
  intros x y d. unfold dist, dist_sq; cbn.
  replace ((x-x)*(x-x)+(y-(y+d))*(y-(y+d))) with (d*d) by ring.
  destruct (Rle_dec 0 d) as [Hd|Hd].
  - rewrite (Rabs_pos_eq d Hd). rewrite (sqrt_square d Hd). reflexivity.
  - apply Rnot_le_lt in Hd. rewrite (Rabs_left d Hd).
    replace (d * d) with ((- d) * (- d)) by ring.
    rewrite (sqrt_square (- d)) by lra. reflexivity.
Qed.

(** Midpoint is classical boundary of the closed unit square. *)
Theorem bnd_mid_bottom_on_classical_boundary :
  boundary_op bnd_witness_P bnd_mid_bottom.
Proof.
  intros eps Heps.
  set (d := Rmin (eps / 2) (1 / 2)).
  assert (Hdpos : 0 < d) by (unfold d; apply Rmin_glb_lt; lra).
  assert (Hdlt : d < eps)
    by (unfold d; apply Rle_lt_trans with (eps / 2); [apply Rmin_l|lra]).
  assert (Hdhalf : d <= 1 / 2) by (unfold d; apply Rmin_r).
  split.
  - (* step up into the square *)
    exists (mkPoint (1 / 2) d).
    split.
    + unfold bnd_mid_bottom.
      replace (dist (mkPoint (1/2) 0) (mkPoint (1/2) d))
        with (dist (mkPoint (1/2) 0) (mkPoint (1/2) (0 + d)))
        by (f_equal; f_equal; ring).
      rewrite dist_vert. rewrite (Rabs_pos_eq d) by lra. exact Hdlt.
    + rewrite bnd_witness_P_eq. split; [reflexivity|].
      unfold in_closed_unit_square; cbn.
      split; [split; lra|]. split; lra.
  - (* step down outside *)
    exists (mkPoint (1 / 2) (- d)).
    split.
    + unfold bnd_mid_bottom.
      replace (dist (mkPoint (1/2) 0) (mkPoint (1/2) (- d)))
        with (dist (mkPoint (1/2) 0) (mkPoint (1/2) (0 + (- d))))
        by (f_equal; f_equal; ring).
      rewrite dist_vert. rewrite Rabs_Ropp. rewrite (Rabs_pos_eq d) by lra.
      exact Hdlt.
    + intros [_ Hin]. unfold in_closed_unit_square in Hin; cbn in Hin. lra.
Qed.

Theorem bnd_mid_bottom_boundary_sides_agree :
  boundary_op bnd_witness_P bnd_mid_bottom /\
  RelateNGBoundaryGraph bnd_witness_P bnd_mid_bottom.
Proof. split; [exact bnd_mid_bottom_on_classical_boundary|exact mid_on_graph]. Qed.

(** On-edge characterisation of the closed unit-square boundary graph. *)
Definition on_unit_box_boundary (p : Point) : Prop :=
  ((py p = 0 \/ py p = 1) /\ 0 <= px p <= 1) \/
  ((px p = 0 \/ px p = 1) /\ 0 <= py p <= 1).

Lemma graph_iff_on_box :
  forall p, RelateNGBoundaryGraph bnd_witness_P p <-> on_unit_box_boundary p.
Proof.
  intros p. split.
  - intros [e [Hin Hb]].
    unfold relateng_boundary_edges, poly_edges, bnd_witness_P in Hin; simpl in Hin.
    destruct Hin as [He|[He|[He|[He|[]]]]]; subst e;
      destruct Hb as [t [Ht0 [Ht1 [Hx Hy]]]]; cbn in Hx, Hy.
    + left; split; [left; rewrite Hy; ring|rewrite Hx; split; nra].
    + right; split; [right; rewrite Hx; ring|rewrite Hy; split; nra].
    + left; split; [right; rewrite Hy; ring|rewrite Hx; split; nra].
    + right; split; [left; rewrite Hx; ring|rewrite Hy; split; nra].
  - intros Hon.
    destruct Hon as [[[Hb|Ht] Hxr]|[[Hl|Hr] Hyr]].
    + exists bnd_bottom_edge.
      split; [unfold relateng_boundary_edges, poly_edges, bnd_witness_P; simpl; left; reflexivity|].
      unfold between, bnd_bottom_edge, bnd_sw, bnd_se; cbn.
      exists (px p). rewrite Hb. split; [lra|]. split; [lra|]. split; ring.
    + exists (bnd_ne, bnd_nw).
      split; [unfold relateng_boundary_edges, poly_edges, bnd_witness_P; simpl;
              right; right; left; reflexivity|].
      unfold between, bnd_ne, bnd_nw; cbn.
      exists (1 - px p). rewrite Ht. split; [lra|]. split; [lra|]. split; ring.
    + exists (bnd_nw, bnd_sw).
      split; [unfold relateng_boundary_edges, poly_edges, bnd_witness_P; simpl;
              right; right; right; left; reflexivity|].
      unfold between, bnd_nw, bnd_sw; cbn.
      exists (1 - py p). rewrite Hl. split; [lra|]. split; [lra|]. split; ring.
    + exists (bnd_se, bnd_ne).
      split; [unfold relateng_boundary_edges, poly_edges, bnd_witness_P; simpl;
              right; left; reflexivity|].
      unfold between, bnd_se, bnd_ne; cbn.
      exists (py p). rewrite Hr. split; [lra|]. split; [lra|]. split; ring.
Qed.

Lemma on_box_to_boundary_op :
  forall p, on_unit_box_boundary p -> boundary_op bnd_witness_P p.
Proof.
  intros p Hon eps Heps.
  set (d := Rmin (eps / 2) (1 / 2)).
  assert (Hdpos : 0 < d) by (unfold d; apply Rmin_glb_lt; lra).
  assert (Hdlt : d < eps)
    by (unfold d; apply Rle_lt_trans with (eps / 2); [apply Rmin_l|lra]).
  (* Meet interior: closed-square center, or step inward if needed for small eps.
     Center works when dist(p,c) < eps; otherwise step fractionally toward center. *)
  set (c := mkPoint (1 / 2) (1 / 2)).
  set (t := Rmin (1 / 2) (eps / (1 + dist p c))).
  assert (Htpos : 0 < t).
  { unfold t. apply Rmin_glb_lt; [lra|].
    apply Rdiv_lt_0_compat; [lra|pose proof (dist_nonneg p c); lra]. }
  assert (Ht1 : t <= 1).
  { unfold t. apply Rle_trans with (1 / 2); [apply Rmin_l|lra]. }
  set (q := mkPoint ((1 - t) * px p + t * (1 / 2))
                    ((1 - t) * py p + t * (1 / 2))).
  assert (Hbd : 0 <= px p <= 1 /\ 0 <= py p <= 1)
    by (destruct Hon as [[[?|?] ?]|[[?|?] ?]]; split; lra).
  assert (Hq_in : point_set_carrier bnd_witness_P q).
  { rewrite bnd_witness_P_eq. split; [reflexivity|].
    unfold in_closed_unit_square, q; cbn.
    destruct Hbd as [[Hxa Hxb] [Hya Hyb]].
    assert (H1t : 0 <= 1 - t) by lra.
    split.
    - split.
      + (* 0 <= (1-t)px + t/2 *)
        apply Rplus_le_le_0_compat; apply Rmult_le_pos; lra.
      + (* (1-t)px + t/2 <= 1 *)
        apply Rle_trans with ((1 - t) * 1 + t * (1 / 2)).
        * apply Rplus_le_compat; apply Rmult_le_compat_l; lra.
        * lra.
    - split.
      + apply Rplus_le_le_0_compat; apply Rmult_le_pos; lra.
      + apply Rle_trans with ((1 - t) * 1 + t * (1 / 2)).
        * apply Rplus_le_compat; apply Rmult_le_compat_l; lra.
        * lra. }
  assert (Hq_dist : dist p q < eps).
  { unfold q, dist, dist_sq; cbn.
    replace (px p - ((1-t)*px p + t*(1/2))) with (t*(px p - 1/2)) by ring.
    replace (py p - ((1-t)*py p + t*(1/2))) with (t*(py p - 1/2)) by ring.
    replace (t*(px p-1/2)*(t*(px p-1/2)) + t*(py p-1/2)*(t*(py p-1/2)))
      with (t*t*((px p-1/2)*(px p-1/2)+(py p-1/2)*(py p-1/2))) by ring.
    assert (Htt : 0 <= t*t) by (apply Rmult_le_pos; lra).
    assert (Hds : 0 <= (px p-1/2)*(px p-1/2)+(py p-1/2)*(py p-1/2)).
    { pose proof (Rle_0_sqr (px p - 1/2)). pose proof (Rle_0_sqr (py p - 1/2)).
      unfold Rsqr in *. lra. }
    rewrite (sqrt_mult _ _ Htt Hds).
    rewrite (sqrt_square t (Rlt_le _ _ Htpos)).
    change (t * dist p c < eps).
    unfold t.
    apply Rle_lt_trans with ((eps / (1 + dist p c)) * dist p c).
    - apply Rmult_le_compat_r; [apply dist_nonneg|apply Rmin_r].
    - pose proof (dist_nonneg p c).
      apply Rmult_lt_reg_r with (1 + dist p c); [lra|].
      replace (eps/(1+dist p c)*dist p c*(1+dist p c))
        with (eps * dist p c) by (field; lra).
      nra. }
  split.
  - exists q. split; assumption.
  - destruct Hon as [[[Hb|Ht'] Hxr]|[[Hl|Hr] Hyr]].
    + set (xp := px p).
      assert (Hp : p = mkPoint xp 0)
        by (destruct p; unfold xp in *; cbn in Hb; subst; reflexivity).
      exists (mkPoint xp (- d)).
      split.
      * rewrite Hp.
        replace (dist (mkPoint xp 0) (mkPoint xp (- d)))
          with (dist (mkPoint xp 0) (mkPoint xp (0 + (- d))))
          by (f_equal; f_equal; ring).
        rewrite dist_vert. rewrite Rabs_Ropp. rewrite (Rabs_pos_eq d) by lra.
        exact Hdlt.
      * intros [_ Hin]; unfold in_closed_unit_square in Hin; cbn in Hin; lra.
    + set (xp := px p).
      assert (Hp : p = mkPoint xp 1)
        by (destruct p; unfold xp in *; cbn in Ht'; subst; reflexivity).
      exists (mkPoint xp (1 + d)).
      split.
      * rewrite Hp. rewrite dist_vert. rewrite (Rabs_pos_eq d) by lra. exact Hdlt.
      * intros [_ Hin]; unfold in_closed_unit_square in Hin; cbn in Hin; lra.
    + set (yp := py p).
      assert (Hp : p = mkPoint 0 yp)
        by (destruct p; unfold yp in *; cbn in Hl; subst; reflexivity).
      exists (mkPoint (- d) yp).
      split.
      * rewrite Hp. unfold dist, dist_sq; cbn.
        replace ((0-(-d))*(0-(-d))+(yp-yp)*(yp-yp)) with (d*d) by ring.
        rewrite (sqrt_square d) by lra. exact Hdlt.
      * intros [_ Hin]; unfold in_closed_unit_square in Hin; cbn in Hin; lra.
    + set (yp := py p).
      assert (Hp : p = mkPoint 1 yp)
        by (destruct p; unfold yp in *; cbn in Hr; subst; reflexivity).
      exists (mkPoint (1 + d) yp).
      split.
      * rewrite Hp. unfold dist, dist_sq; cbn.
        replace ((1-(1+d))*(1-(1+d))+(yp-yp)*(yp-yp)) with (d*d) by ring.
        rewrite (sqrt_square d) by lra. exact Hdlt.
      * intros [_ Hin]; unfold in_closed_unit_square in Hin; cbn in Hin; lra.
Qed.

Lemma boundary_op_to_on_box :
  forall p, boundary_op bnd_witness_P p -> on_unit_box_boundary p.
Proof.
  intros p Hbnd.
  destruct (Rlt_le_dec (px p) 0) as [Hxa|Hxa].
  { set (d := - px p / 2). assert (Hd : 0 < d) by (unfold d; lra).
    destruct (Hbnd d Hd) as [[q [Hdq Hcar]] _].
    destruct Hcar as [_ Hin]. unfold in_closed_unit_square in Hin.
    assert (Habs : Rabs (px p - px q) < d)
      by (apply Rle_lt_trans with (dist p q); [apply abs_le_dist_x|exact Hdq]).
    apply Rabs_def2 in Habs. unfold d in *; lra. }
  destruct (Rlt_le_dec 1 (px p)) as [Hxb|Hxb].
  { set (d := (px p - 1) / 2). assert (Hd : 0 < d) by (unfold d; lra).
    destruct (Hbnd d Hd) as [[q [Hdq Hcar]] _].
    destruct Hcar as [_ Hin]. unfold in_closed_unit_square in Hin.
    assert (Habs : Rabs (px p - px q) < d)
      by (apply Rle_lt_trans with (dist p q); [apply abs_le_dist_x|exact Hdq]).
    apply Rabs_def2 in Habs. unfold d in *; lra. }
  destruct (Rlt_le_dec (py p) 0) as [Hya|Hya].
  { set (d := - py p / 2). assert (Hd : 0 < d) by (unfold d; lra).
    destruct (Hbnd d Hd) as [[q [Hdq Hcar]] _].
    destruct Hcar as [_ Hin]. unfold in_closed_unit_square in Hin.
    assert (Habs : Rabs (py p - py q) < d)
      by (apply Rle_lt_trans with (dist p q); [apply abs_le_dist_y|exact Hdq]).
    apply Rabs_def2 in Habs. unfold d in *; lra. }
  destruct (Rlt_le_dec 1 (py p)) as [Hyb|Hyb].
  { set (d := (py p - 1) / 2). assert (Hd : 0 < d) by (unfold d; lra).
    destruct (Hbnd d Hd) as [[q [Hdq Hcar]] _].
    destruct Hcar as [_ Hin]. unfold in_closed_unit_square in Hin.
    assert (Habs : Rabs (py p - py q) < d)
      by (apply Rle_lt_trans with (dist p q); [apply abs_le_dist_y|exact Hdq]).
    apply Rabs_def2 in Habs. unfold d in *; lra. }
  destruct (Rle_lt_or_eq_dec _ _ Hxa) as [|Hx0];
    [|right; split; [left; symmetry; exact Hx0|lra]].
  destruct (Rle_lt_or_eq_dec _ _ Hxb) as [|Hx1];
    [|right; split; [right; exact Hx1|lra]].
  destruct (Rle_lt_or_eq_dec _ _ Hya) as [|Hy0];
    [|left; split; [left; symmetry; exact Hy0|lra]].
  destruct (Rle_lt_or_eq_dec _ _ Hyb) as [|Hy1];
    [|left; split; [right; exact Hy1|lra]].
  (* strict open interior of closed square: not a frontier point *)
  set (d := Rmin (Rmin (px p) (1 - px p)) (Rmin (py p) (1 - py p))).
  assert (Hdpos : 0 < d) by (unfold d; apply Rmin_glb_lt; apply Rmin_glb_lt; lra).
  destruct (Hbnd d Hdpos) as [_ [s [Hsd Hsnot]]].
  assert (Hsin : point_set_carrier bnd_witness_P s).
  { rewrite bnd_witness_P_eq. split; [reflexivity|].
    unfold in_closed_unit_square.
    assert (Hdx : Rabs (px p - px s) < d)
      by (apply Rle_lt_trans with (dist p s); [apply abs_le_dist_x|exact Hsd]).
    assert (Hdy : Rabs (py p - py s) < d)
      by (apply Rle_lt_trans with (dist p s); [apply abs_le_dist_y|exact Hsd]).
    apply Rabs_def2 in Hdx; apply Rabs_def2 in Hdy.
    unfold d in Hdx, Hdy.
    pose proof (Rmin_l (Rmin (px p) (1-px p)) (Rmin (py p) (1-py p))).
    pose proof (Rmin_r (Rmin (px p) (1-px p)) (Rmin (py p) (1-py p))).
    pose proof (Rmin_l (px p) (1-px p)). pose proof (Rmin_r (px p) (1-px p)).
    pose proof (Rmin_l (py p) (1-py p)). pose proof (Rmin_r (py p) (1-py p)).
    split; split; lra. }
  contradiction.
Qed.

Theorem boundary_op_eq_relateng_boundary_graph :
  forall (p : Point),
    boundary_op bnd_witness_P p <-> RelateNGBoundaryGraph bnd_witness_P p.
Proof.
  intros p. rewrite graph_iff_on_box.
  split; [apply boundary_op_to_on_box|apply on_box_to_boundary_op].
Qed.

Theorem boundary_op_eq_relateng_boundary_graph_on_witness :
  forall (p : Point),
    boundary_op bnd_witness_P p <-> RelateNGBoundaryGraph bnd_witness_P p.
Proof. exact boundary_op_eq_relateng_boundary_graph. Qed.

Print Assumptions boundary_op_eq_relateng_boundary_graph.
Print Assumptions bnd_mid_bottom_on_classical_boundary.
