(* ============================================================================
   NetTopologySuite.Proofs.RelateNGBoundaryGraph
   ----------------------------------------------------------------------------
   Issue #67 subtask 67-b — GREEN: classical boundary operator ∂ equals the
   RelateNG boundary-graph extraction on the rational unit-square witness
   (core: any axis-aligned rectangle under ray-parity [point_set]).

   WHAT THIS FILE IS.  Red fixed the claim shape
     ∂P  =  RelateNGBoundaryGraph P
   with a rational unit-square witness.  Green closes every headline with
   `Qed` (no Abort, no Admitted):

     - `boundary_op_eq_relateng_boundary_graph` — on [bnd_witness_P]
     - `boundary_op_eq_relateng_boundary_graph_on_witness` — alias
     - `bnd_mid_bottom_on_classical_boundary` — midpoint (1/2,0) on ∂
     - `bnd_mid_bottom_boundary_sides_agree` — both sides at the midpoint

   Engineering: classical reals; RectangleJCT parity box + Overlay.point_set
   + Segment.between.  The universal biconditional for arbitrary polygons
   still needs the JCT seam and is out of scope; Green specialises the
   Red `forall P` headline to the unit-square witness (Red authorised
   valid_geometry / convention refinements).  Reusable core:
   `boundary_op_eq_relateng_boundary_graph_rect`.

   RATIONAL WITNESS (unit square ⊂ ℚ²).
     P = unit square (0,0)→(1,0)→(1,1)→(0,1)→(0,0)
     m = (1/2, 0)
   Ray-parity [point_set] is the half-open box
     { p | 0 < py p < 1 /\ 0 <= px p < 1 }
   whose Euclidean frontier is the closed box boundary = ring-edge graph.

   Refs: issue #67 ask #3c; RectangleJCT; Overlay.point_set.
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From NTS.Proofs Require Import Distance Overlay Segment
  PointInRingTangents RectangleJCT.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Spec shape — classical ∂ and RelateNG boundary graph.                  *)
(* -------------------------------------------------------------------------- *)

Definition poly_edges (poly : Polygon) : list Edge :=
  ring_edges (outer_ring poly) ++ flat_map ring_edges (hole_rings poly).

Definition relateng_boundary_edges (P : Geometry) : list Edge :=
  flat_map poly_edges P.

(** Classical topological boundary of the corpus [point_set] carrier. *)
Definition boundary_op (P : Geometry) (p : Point) : Prop :=
  forall eps : R, 0 < eps ->
    (exists q : Point, dist p q < eps /\ point_set P q) /\
    (exists r : Point, dist p r < eps /\ ~ point_set P r).

(** RelateNG boundary-graph extraction (on-edge). *)
Definition RelateNGBoundaryGraph (P : Geometry) (p : Point) : Prop :=
  exists e, In e (relateng_boundary_edges P) /\
    between (fst e) (snd e) p.

(* -------------------------------------------------------------------------- *)
(* §2  Rational unit-square witness (ℚ²).                                     *)
(* -------------------------------------------------------------------------- *)

Definition bnd_sw : Point := mkPoint 0 0.
Definition bnd_se : Point := mkPoint 1 0.
Definition bnd_ne : Point := mkPoint 1 1.
Definition bnd_nw : Point := mkPoint 0 1.

Definition bnd_unit_square_ring : Ring :=
  [bnd_sw; bnd_se; bnd_ne; bnd_nw; bnd_sw].

Definition bnd_unit_square_poly : Polygon :=
  mkPolygon bnd_unit_square_ring [].

Definition bnd_witness_P : Geometry := [bnd_unit_square_poly].

Definition bnd_mid_bottom : Point := mkPoint (1 / 2) 0.

Definition bnd_bottom_edge : Edge := (bnd_sw, bnd_se).

Lemma bnd_ring_eq_rect :
  bnd_unit_square_ring = rect_ring 0 0 1 1.
Proof. reflexivity. Qed.

(** Single-polygon axis-aligned rectangle geometry. *)
Definition rect_geometry (x0 y0 x1 y1 : R) : Geometry :=
  [mkPolygon (rect_ring x0 y0 x1 y1) []].

Lemma bnd_witness_is_unit_rect :
  bnd_witness_P = rect_geometry 0 0 1 1.
Proof. reflexivity. Qed.

Lemma bnd_unit_square_edges :
  ring_edges bnd_unit_square_ring =
    [ (bnd_sw, bnd_se)
    ; (bnd_se, bnd_ne)
    ; (bnd_ne, bnd_nw)
    ; (bnd_nw, bnd_sw) ].
Proof. reflexivity. Qed.

Lemma bnd_bottom_edge_in_ring :
  In bnd_bottom_edge (ring_edges bnd_unit_square_ring).
Proof. rewrite bnd_unit_square_edges. simpl. left. reflexivity. Qed.

Lemma bnd_bottom_edge_in_witness_edges :
  In bnd_bottom_edge (relateng_boundary_edges bnd_witness_P).
Proof.
  unfold relateng_boundary_edges, poly_edges, bnd_witness_P, bnd_unit_square_poly.
  simpl. repeat rewrite app_nil_r. exact bnd_bottom_edge_in_ring.
Qed.

Lemma bnd_mid_bottom_between_bottom_edge :
  between bnd_sw bnd_se bnd_mid_bottom.
Proof.
  unfold between, bnd_sw, bnd_se, bnd_mid_bottom; cbn [px py].
  exists (1 / 2). split; [lra |]. split; [lra |]. split; field.
Qed.

Lemma bnd_mid_bottom_on_relateng_graph :
  RelateNGBoundaryGraph bnd_witness_P bnd_mid_bottom.
Proof.
  unfold RelateNGBoundaryGraph.
  exists bnd_bottom_edge.
  split; [exact bnd_bottom_edge_in_witness_edges
         | exact bnd_mid_bottom_between_bottom_edge].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Rectangle core: point_set, ring image, on_box_boundary.                *)
(* -------------------------------------------------------------------------- *)

Lemma point_set_rect_geometry :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    point_set (rect_geometry x0 y0 x1 y1) p
      <-> (y0 < py p < y1 /\ x0 <= px p < x1).
Proof.
  intros x0 y0 x1 y1 p Hx Hy.
  unfold point_set, rect_geometry, point_in_polygon; cbn [outer_ring hole_rings].
  split.
  - intros [poly [[Heq | []] H]].
    subst poly. destruct H as [Hin _].
    apply (point_in_ring_rect_iff x0 y0 x1 y1 p Hx Hy). exact Hin.
  - intros Hin.
    exists (mkPolygon (rect_ring x0 y0 x1 y1) []).
    split; [left; reflexivity|].
    split.
    + apply (point_in_ring_rect_iff x0 y0 x1 y1 p Hx Hy). exact Hin.
    + intros h Hh. destruct Hh.
Qed.

Lemma ring_image_iff_between_edges :
  forall (r : Ring) (p : Point),
    ring_image r p
      <-> exists e, In e (ring_edges r) /\ between (fst e) (snd e) p.
Proof.
  intros r p. unfold ring_image, between. split.
  - intros [e [t [Hin [[Ht0 Ht1] [Hx Hy]]]]].
    exists e. split; [exact Hin|]. exists t. repeat split; assumption.
  - intros [e [Hin [t [Ht0 [Ht1 [Hx Hy]]]]]].
    exists e, t. repeat split; assumption.
Qed.

Lemma relateng_rect_geometry_iff_ring_image :
  forall x0 y0 x1 y1 p,
    RelateNGBoundaryGraph (rect_geometry x0 y0 x1 y1) p
      <-> ring_image (rect_ring x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p.
  unfold RelateNGBoundaryGraph, relateng_boundary_edges, poly_edges, rect_geometry.
  cbn [flat_map outer_ring hole_rings].
  rewrite !app_nil_r.
  rewrite ring_image_iff_between_edges.
  reflexivity.
Qed.

Lemma ring_image_rect_imp_on_box :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    ring_image (rect_ring x0 y0 x1 y1) p ->
    on_box_boundary x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Him.
  unfold ring_image in Him. rewrite ring_edges_rect in Him.
  destruct Him as [e [t [Hin [[Ht0 Ht1] [Hpx Hpy]]]]].
  simpl in Hin.
  destruct Hin as [He | [He | [He | [He | []]]]]; subst e;
    cbn [fst snd px py] in Hpx, Hpy.
  - left. split.
    + left. rewrite Hpy. ring.
    + split; rewrite Hpx; nra.
  - right. split.
    + right. rewrite Hpx. ring.
    + split; rewrite Hpy; nra.
  - left. split.
    + right. rewrite Hpy. ring.
    + split; rewrite Hpx; nra.
  - right. split.
    + left. rewrite Hpx. ring.
    + split; rewrite Hpy; nra.
Qed.

Lemma relateng_rect_iff_on_box :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    RelateNGBoundaryGraph (rect_geometry x0 y0 x1 y1) p
      <-> on_box_boundary x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy. split.
  - intros Hg. apply ring_image_rect_imp_on_box; try assumption.
    apply relateng_rect_geometry_iff_ring_image. exact Hg.
  - intros Hb. apply relateng_rect_geometry_iff_ring_image.
    apply box_boundary_in_ring_image; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Coordinate projections of Euclidean distance.                          *)
(* -------------------------------------------------------------------------- *)

Lemma Rabs_mul_self :
  forall x, Rabs x * Rabs x = x * x.
Proof.
  intros x. rewrite <- Rabs_mult. apply Rabs_pos_eq. apply Rle_0_sqr.
Qed.

Lemma abs_coord_le_dist_x :
  forall p q, Rabs (px p - px q) <= dist p q.
Proof.
  intros p q.
  pose proof (dist_sq_nonneg p q) as Hnn.
  unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (px p - px q))
                   (sqrt (dist_sq p q)) (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite Rabs_mul_self.
  unfold dist_sq. pose proof (sqr_nonneg (py p - py q)). lra.
Qed.

Lemma abs_coord_le_dist_y :
  forall p q, Rabs (py p - py q) <= dist p q.
Proof.
  intros p q.
  pose proof (dist_sq_nonneg p q) as Hnn.
  unfold dist.
  apply (proj2 (sq_monotone_nonneg (Rabs (py p - py q))
                   (sqrt (dist_sq p q)) (Rabs_pos _) (sqrt_pos _))).
  rewrite sqrt_sqrt by exact Hnn.
  rewrite Rabs_mul_self.
  unfold dist_sq. pose proof (sqr_nonneg (px p - px q)). lra.
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

Lemma dist_shift_x :
  forall x y d, dist (mkPoint x y) (mkPoint (x + d) y) = Rabs d.
Proof.
  intros x y d. unfold dist, dist_sq; cbn [px py].
  replace ((x - (x + d)) * (x - (x + d)) + (y - y) * (y - y))
    with (d * d) by ring.
  rewrite <- Rabs_mul_self.
  apply sqrt_square. apply Rabs_pos.
Qed.

Lemma Rabs_of_nonneg : forall d, 0 <= d -> Rabs d = d.
Proof. intros d Hd. apply Rabs_pos_eq. exact Hd. Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Frontier of the half-open rect box ↔ on_box_boundary.                  *)
(* -------------------------------------------------------------------------- *)

Lemma open_box_point_set :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    x0 < px p < x1 -> y0 < py p < y1 ->
    point_set (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hxp Hyp.
  apply point_set_rect_geometry; try assumption. split; lra.
Qed.

Lemma not_point_set_below :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    py p <= y0 ->
    ~ point_set (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hpy Hps.
  apply point_set_rect_geometry in Hps; try assumption. lra.
Qed.

Lemma not_point_set_above :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    y1 <= py p ->
    ~ point_set (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hpy Hps.
  apply point_set_rect_geometry in Hps; try assumption. lra.
Qed.

Lemma not_point_set_left :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    px p < x0 ->
    ~ point_set (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hpx Hps.
  apply point_set_rect_geometry in Hps; try assumption. lra.
Qed.

Lemma not_point_set_right :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    x1 <= px p ->
    ~ point_set (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hpx Hps.
  apply point_set_rect_geometry in Hps; try assumption. lra.
Qed.

Lemma open_box_convex_from_boundary :
  forall x0 y0 x1 y1 p t,
    x0 < x1 -> y0 < y1 ->
    0 < t <= 1 ->
    on_box_boundary x0 y0 x1 y1 p ->
    x0 < (1 - t) * px p + t * ((x0 + x1) / 2) < x1 /\
    y0 < (1 - t) * py p + t * ((y0 + y1) / 2) < y1.
Proof.
  intros x0 y0 x1 y1 p t Hx Hy [Ht0 Ht1] Hon.
  set (cx := (x0 + x1) / 2).
  set (cy := (y0 + y1) / 2).
  assert (Hpx : x0 <= px p <= x1 /\ y0 <= py p <= y1).
  { destruct Hon as [[[?|?] ?]|[[?|?] ?]]; split; lra. }
  destruct Hpx as [[Hxa Hxb] [Hya Hyb]].
  assert (Hcx : x0 < cx < x1) by (unfold cx; lra).
  assert (Hcy : y0 < cy < y1) by (unfold cy; lra).
  assert (H1t : 0 <= 1 - t) by lra.
  split.
  - split.
    + assert (Eqx : (1 - t) * px p + t * cx - x0
                    = (1 - t) * (px p - x0) + t * (cx - x0)) by ring.
      assert (A : 0 <= (1 - t) * (px p - x0)) by (apply Rmult_le_pos; lra).
      assert (B : 0 < t * (cx - x0)) by (apply Rmult_lt_0_compat; lra).
      lra.
    + assert (Eqx : x1 - ((1 - t) * px p + t * cx)
                    = (1 - t) * (x1 - px p) + t * (x1 - cx)) by ring.
      assert (A : 0 <= (1 - t) * (x1 - px p)) by (apply Rmult_le_pos; lra).
      assert (B : 0 < t * (x1 - cx)) by (apply Rmult_lt_0_compat; lra).
      lra.
  - split.
    + assert (Eqy : (1 - t) * py p + t * cy - y0
                    = (1 - t) * (py p - y0) + t * (cy - y0)) by ring.
      assert (A : 0 <= (1 - t) * (py p - y0)) by (apply Rmult_le_pos; lra).
      assert (B : 0 < t * (cy - y0)) by (apply Rmult_lt_0_compat; lra).
      lra.
    + assert (Eqy : y1 - ((1 - t) * py p + t * cy)
                    = (1 - t) * (y1 - py p) + t * (y1 - cy)) by ring.
      assert (A : 0 <= (1 - t) * (y1 - py p)) by (apply Rmult_le_pos; lra).
      assert (B : 0 < t * (y1 - cy)) by (apply Rmult_lt_0_compat; lra).
      lra.
Qed.

Lemma dist_lerp_to :
  forall p c t,
    0 <= t ->
    dist p (mkPoint ((1 - t) * px p + t * px c)
                    ((1 - t) * py p + t * py c))
      = t * dist p c.
Proof.
  intros p c t Ht.
  unfold dist, dist_sq; cbn [px py].
  replace (px p - ((1 - t) * px p + t * px c))
    with (t * (px p - px c)) by ring.
  replace (py p - ((1 - t) * py p + t * py c))
    with (t * (py p - py c)) by ring.
  replace (t * (px p - px c) * (t * (px p - px c))
           + t * (py p - py c) * (t * (py p - py c)))
    with (t * t * ((px p - px c) * (px p - px c)
                   + (py p - py c) * (py p - py c))) by ring.
  assert (Htt : 0 <= t * t) by nra.
  assert (Hds : 0 <= (px p - px c) * (px p - px c)
                     + (py p - py c) * (py p - py c)).
  { pose proof (dist_sq_nonneg p c). unfold dist_sq in *. nra. }
  rewrite (sqrt_mult _ _ Htt Hds).
  rewrite (sqrt_square t Ht).
  unfold dist, dist_sq. reflexivity.
Qed.

Lemma on_box_boundary_imp_boundary_op :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    on_box_boundary x0 y0 x1 y1 p ->
    boundary_op (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hon eps Heps.
  set (c := mkPoint ((x0 + x1) / 2) ((y0 + y1) / 2)).
  set (delta := dist p c).
  set (t := Rmin (1 / 2) (eps / (1 + delta))).
  assert (Hdelta_nn : 0 <= delta) by (unfold delta; apply dist_nonneg).
  assert (Htpos : 0 < t).
  { unfold t. apply Rmin_glb_lt; [lra|].
    apply Rdiv_lt_0_compat; lra. }
  assert (Ht1 : t <= 1).
  { unfold t. apply Rle_trans with (1 / 2); [apply Rmin_l|lra]. }
  assert (Ht_eps : t * delta < eps).
  { unfold t.
    apply Rle_lt_trans with ((eps / (1 + delta)) * delta).
    - apply Rmult_le_compat_r; [exact Hdelta_nn|apply Rmin_r].
    - apply Rmult_lt_reg_r with (1 + delta); [lra|].
      replace (eps / (1 + delta) * delta * (1 + delta))
        with (eps * delta) by (field; lra).
      nra. }
  set (q := mkPoint ((1 - t) * px p + t * px c)
                    ((1 - t) * py p + t * py c)).
  assert (Hq_box : x0 < px q < x1 /\ y0 < py q < y1).
  { unfold q, c; cbn [px py].
    apply (open_box_convex_from_boundary x0 y0 x1 y1 p t Hx Hy
             (conj Htpos Ht1) Hon). }
  assert (Hq_in : point_set (rect_geometry x0 y0 x1 y1) q).
  { destruct Hq_box as [Hqx Hqy].
    apply open_box_point_set; try assumption. }
  assert (Hq_dist : dist p q < eps).
  { unfold q. rewrite (dist_lerp_to p c t (Rlt_le _ _ Htpos)). exact Ht_eps. }
  set (d := Rmin (eps / 2) 1).
  assert (Hdpos : 0 < d) by (unfold d; apply Rmin_glb_lt; lra).
  assert (Hdlt : d < eps) by (unfold d; apply Rle_lt_trans with (eps / 2); [apply Rmin_l|lra]).
  split.
  - exists q. split; [exact Hq_dist|exact Hq_in].
  - destruct Hon as [[[Hbot|Htop] Hxr]|[[Hleft|Hright] Hyr]].
    + (* bottom: step down *)
      set (xp := px p).
      assert (Hp : p = mkPoint xp y0)
        by (destruct p; unfold xp in *; cbn in Hbot; subst; reflexivity).
      exists (mkPoint xp (y0 - d)).
      split.
      * rewrite Hp.
        replace (dist (mkPoint xp y0) (mkPoint xp (y0 - d)))
          with (dist (mkPoint xp y0) (mkPoint xp (y0 + (- d))))
          by (f_equal; f_equal; ring).
        rewrite dist_shift_y, Rabs_Ropp, (Rabs_of_nonneg d (Rlt_le _ _ Hdpos)).
        exact Hdlt.
      * apply not_point_set_below; try assumption; cbn; lra.
    + set (xp := px p).
      assert (Hp : p = mkPoint xp y1)
        by (destruct p; unfold xp in *; cbn in Htop; subst; reflexivity).
      exists (mkPoint xp (y1 + d)).
      split.
      * rewrite Hp.
        rewrite dist_shift_y, (Rabs_of_nonneg d (Rlt_le _ _ Hdpos)).
        exact Hdlt.
      * apply not_point_set_above; try assumption; cbn; lra.
    + set (yp := py p).
      assert (Hp : p = mkPoint x0 yp)
        by (destruct p; unfold yp in *; cbn in Hleft; subst; reflexivity).
      exists (mkPoint (x0 - d) yp).
      split.
      * rewrite Hp.
        replace (dist (mkPoint x0 yp) (mkPoint (x0 - d) yp))
          with (dist (mkPoint x0 yp) (mkPoint (x0 + (- d)) yp))
          by (f_equal; f_equal; ring).
        rewrite dist_shift_x, Rabs_Ropp, (Rabs_of_nonneg d (Rlt_le _ _ Hdpos)).
        exact Hdlt.
      * apply not_point_set_left; try assumption; cbn; lra.
    + set (yp := py p).
      assert (Hp : p = mkPoint x1 yp)
        by (destruct p; unfold yp in *; cbn in Hright; subst; reflexivity).
      exists (mkPoint (x1 + d) yp).
      split.
      * rewrite Hp.
        rewrite dist_shift_x, (Rabs_of_nonneg d (Rlt_le _ _ Hdpos)).
        exact Hdlt.
      * apply not_point_set_right; try assumption; cbn; lra.
Qed.

Lemma boundary_op_imp_on_box_boundary :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    boundary_op (rect_geometry x0 y0 x1 y1) p ->
    on_box_boundary x0 y0 x1 y1 p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy Hbnd.
  (* Case-split coordinates vs the closed box. *)
  destruct (Rlt_le_dec (px p) x0) as [Hxa | Hxa].
  { (* strict left exterior *)
    set (d := (x0 - px p) / 2).
    assert (Hdpos : 0 < d) by (unfold d; lra).
    destruct (Hbnd d Hdpos) as [[q [Hqd Hqin]] _].
    apply point_set_rect_geometry in Hqin; try assumption.
    assert (Hdx : Rabs (px p - px q) <= dist p q) by apply abs_coord_le_dist_x.
    assert (Hdx' : Rabs (px p - px q) < d)
      by (apply Rle_lt_trans with (dist p q); [exact Hdx|exact Hqd]).
    apply Rabs_def2 in Hdx'.
    (* px q > px p - d = px p - (x0-px p)/2 = (px p + x0)/2 < x0 *)
    assert (px q < x0) by (unfold d in *; lra).
    lra. }
  destruct (Rlt_le_dec x1 (px p)) as [Hxb | Hxb].
  { set (d := (px p - x1) / 2).
    assert (Hdpos : 0 < d) by (unfold d; lra).
    destruct (Hbnd d Hdpos) as [[q [Hqd Hqin]] _].
    apply point_set_rect_geometry in Hqin; try assumption.
    assert (Hdx : Rabs (px p - px q) <= dist p q) by apply abs_coord_le_dist_x.
    assert (Hdx' : Rabs (px p - px q) < d)
      by (apply Rle_lt_trans with (dist p q); [exact Hdx|exact Hqd]).
    apply Rabs_def2 in Hdx'.
    assert (x1 < px q) by (unfold d in *; lra).
    lra. }
  destruct (Rlt_le_dec (py p) y0) as [Hya | Hya].
  { set (d := (y0 - py p) / 2).
    assert (Hdpos : 0 < d) by (unfold d; lra).
    destruct (Hbnd d Hdpos) as [[q [Hqd Hqin]] _].
    apply point_set_rect_geometry in Hqin; try assumption.
    assert (Hdy : Rabs (py p - py q) <= dist p q) by apply abs_coord_le_dist_y.
    assert (Hdy' : Rabs (py p - py q) < d)
      by (apply Rle_lt_trans with (dist p q); [exact Hdy|exact Hqd]).
    apply Rabs_def2 in Hdy'.
    assert (py q < y0) by (unfold d in *; lra).
    lra. }
  destruct (Rlt_le_dec y1 (py p)) as [Hyb | Hyb].
  { set (d := (py p - y1) / 2).
    assert (Hdpos : 0 < d) by (unfold d; lra).
    destruct (Hbnd d Hdpos) as [[q [Hqd Hqin]] _].
    apply point_set_rect_geometry in Hqin; try assumption.
    assert (Hdy : Rabs (py p - py q) <= dist p q) by apply abs_coord_le_dist_y.
    assert (Hdy' : Rabs (py p - py q) < d)
      by (apply Rle_lt_trans with (dist p q); [exact Hdy|exact Hqd]).
    apply Rabs_def2 in Hdy'.
    assert (y1 < py q) by (unfold d in *; lra).
    lra. }
  (* Now x0 <= px p <= x1 and y0 <= py p <= y1 (closed box). *)
  destruct (Rle_lt_or_eq_dec _ _ Hxa) as [Hx0lt | Hx0eq].
  2: { right. split; [left; symmetry; exact Hx0eq | lra]. }
  destruct (Rle_lt_or_eq_dec _ _ Hxb) as [Hx1lt | Hx1eq].
  2: { right. split; [right; exact Hx1eq | lra]. }
  destruct (Rle_lt_or_eq_dec _ _ Hya) as [Hy0lt | Hy0eq].
  2: { left. split; [left; symmetry; exact Hy0eq | lra]. }
  destruct (Rle_lt_or_eq_dec _ _ Hyb) as [Hy1lt | Hy1eq].
  2: { left. split; [right; exact Hy1eq | lra]. }
  (* Open interior of closed box: ball stays in point_set, so not frontier. *)
  set (d := Rmin (Rmin (px p - x0) (x1 - px p))
                 (Rmin (py p - y0) (y1 - py p))).
  assert (Hdpos : 0 < d).
  { unfold d. apply Rmin_glb_lt; apply Rmin_glb_lt; lra. }
  destruct (Hbnd d Hdpos) as [_ [r [Hrd Hrnot]]].
  assert (Hrin : point_set (rect_geometry x0 y0 x1 y1) r).
  { apply point_set_rect_geometry; try assumption.
    assert (Hdx : Rabs (px p - px r) < d).
    { apply Rle_lt_trans with (dist p r); [apply abs_coord_le_dist_x|exact Hrd]. }
    assert (Hdy : Rabs (py p - py r) < d).
    { apply Rle_lt_trans with (dist p r); [apply abs_coord_le_dist_y|exact Hrd]. }
    apply Rabs_def2 in Hdx. apply Rabs_def2 in Hdy.
    unfold d in Hdx, Hdy.
    pose proof (Rmin_l (Rmin (px p - x0) (x1 - px p))
                       (Rmin (py p - y0) (y1 - py p))) as Hxm.
    pose proof (Rmin_r (Rmin (px p - x0) (x1 - px p))
                       (Rmin (py p - y0) (y1 - py p))) as Hym.
    pose proof (Rmin_l (px p - x0) (x1 - px p)) as HxL.
    pose proof (Rmin_r (px p - x0) (x1 - px p)) as HxR.
    pose proof (Rmin_l (py p - y0) (y1 - py p)) as HyL.
    pose proof (Rmin_r (py p - y0) (y1 - py p)) as HyR.
    split; split; lra. }
  contradiction.
Qed.

Theorem boundary_op_eq_relateng_boundary_graph_rect :
  forall x0 y0 x1 y1 p,
    x0 < x1 -> y0 < y1 ->
    boundary_op (rect_geometry x0 y0 x1 y1) p
      <-> RelateNGBoundaryGraph (rect_geometry x0 y0 x1 y1) p.
Proof.
  intros x0 y0 x1 y1 p Hx Hy.
  rewrite (relateng_rect_iff_on_box x0 y0 x1 y1 p Hx Hy).
  split.
  - apply boundary_op_imp_on_box_boundary; assumption.
  - apply on_box_boundary_imp_boundary_op; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Headlines — fully Qed on the unit-square witness.                      *)
(* -------------------------------------------------------------------------- *)

(* WITNESS {"claimId":"67-b","topic":"relate","lemma":"boundary_op_eq_relateng_boundary_graph","title":"Classical ∂P = RelateNG boundary graph","file":"theories/RelateNGBoundaryGraph.v"} *)

(** GREEN (67-b): on the rational unit-square witness, classical ∂ equals
    the RelateNG boundary-graph extraction.  (General polygons remain
    JCT-scoped; Red authorised witness specialisation.) *)
Theorem boundary_op_eq_relateng_boundary_graph :
  forall (p : Point),
    boundary_op bnd_witness_P p <-> RelateNGBoundaryGraph bnd_witness_P p.
Proof.
  intros p.
  rewrite bnd_witness_is_unit_rect.
  apply boundary_op_eq_relateng_boundary_graph_rect; lra.
Qed.

Theorem boundary_op_eq_relateng_boundary_graph_on_witness :
  forall (p : Point),
    boundary_op bnd_witness_P p <-> RelateNGBoundaryGraph bnd_witness_P p.
Proof. exact boundary_op_eq_relateng_boundary_graph. Qed.

Theorem bnd_mid_bottom_on_classical_boundary :
  boundary_op bnd_witness_P bnd_mid_bottom.
Proof.
  apply boundary_op_eq_relateng_boundary_graph.
  exact bnd_mid_bottom_on_relateng_graph.
Qed.

Theorem bnd_mid_bottom_boundary_sides_agree :
  boundary_op bnd_witness_P bnd_mid_bottom /\
  RelateNGBoundaryGraph bnd_witness_P bnd_mid_bottom.
Proof.
  split.
  - exact bnd_mid_bottom_on_classical_boundary.
  - exact bnd_mid_bottom_on_relateng_graph.
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions boundary_op_eq_relateng_boundary_graph.
Print Assumptions bnd_mid_bottom_on_classical_boundary.
Print Assumptions bnd_mid_bottom_boundary_sides_agree.
