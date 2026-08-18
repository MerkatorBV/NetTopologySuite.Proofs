(* ============================================================================
   NetTopologySuite.Proofs.GeometricInteriorBound
   ----------------------------------------------------------------------------
   Ring-generic AABB layer extracted from the convex two-component discharge
   so Phase-3 consumers can use `geometric_interior_uniform_bound` without
   pulling ConvexField / DiamondOffringSeam.

topic: overlay
claimId: jordancurveseam-jct-two-components-cont-simple
witness: none

   `edges_maxX` already lives in JordanCurveSeam.  The other three sides
   use the same dummy-empty = 0 convention.  Every continuous geometric
   interior point sits in that box, so one radius confines the interior
   of any closed polygonal ring — no convexity, no simplicity.

   Pure-R; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ============================================================================ *)

From Stdlib Require Import Reals Lra List.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam JCT.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Axis-aligned bounds of a ring skeleton.                                *)
(*                                                                            *)
(* `edges_maxX` already lives in JordanCurveSeam.  The other three sides      *)
(* follow the same dummy-empty = 0 convention: the resulting box always       *)
(* contains the skeleton (the dummy only loosens one side), so the four       *)
(* "strictly outside the box" regions remain a *sufficient* off-ring test.    *)
(* -------------------------------------------------------------------------- *)

Fixpoint edges_minX (es : list Edge) : R :=
  match es with
  | [] => 0
  | (a, b) :: es' => Rmin (Rmin (px a) (px b)) (edges_minX es')
  end.

Fixpoint edges_maxY (es : list Edge) : R :=
  match es with
  | [] => 0
  | (a, b) :: es' => Rmax (Rmax (py a) (py b)) (edges_maxY es')
  end.

Fixpoint edges_minY (es : list Edge) : R :=
  match es with
  | [] => 0
  | (a, b) :: es' => Rmin (Rmin (py a) (py b)) (edges_minY es')
  end.

Lemma in_edges_minX :
  forall es e, In e es ->
    edges_minX es <= px (fst e) /\ edges_minX es <= px (snd e).
Proof.
  induction es as [|[a b] es' IH]; intros e Hin; simpl in *.
  - contradiction.
  - destruct Hin as [He | He].
    + subst e. simpl. split.
      * eapply Rle_trans; [apply Rmin_l | apply Rmin_l].
      * eapply Rle_trans; [apply Rmin_l | apply Rmin_r].
    + destruct (IH e He) as [H1 H2]. split; eapply Rle_trans;
        try eassumption; apply Rmin_r.
Qed.

Lemma in_edges_maxY :
  forall es e, In e es ->
    py (fst e) <= edges_maxY es /\ py (snd e) <= edges_maxY es.
Proof.
  induction es as [|[a b] es' IH]; intros e Hin; simpl in *.
  - contradiction.
  - destruct Hin as [He | He].
    + subst e. simpl. split.
      * eapply Rle_trans; [apply Rmax_l | apply Rmax_l].
      * eapply Rle_trans; [apply Rmax_r | apply Rmax_l].
    + destruct (IH e He) as [H1 H2]. split; eapply Rle_trans;
        try eassumption; apply Rmax_r.
Qed.

Lemma in_edges_minY :
  forall es e, In e es ->
    edges_minY es <= py (fst e) /\ edges_minY es <= py (snd e).
Proof.
  induction es as [|[a b] es' IH]; intros e Hin; simpl in *.
  - contradiction.
  - destruct Hin as [He | He].
    + subst e. simpl. split.
      * eapply Rle_trans; [apply Rmin_l | apply Rmin_l].
      * eapply Rle_trans; [apply Rmin_l | apply Rmin_r].
    + destruct (IH e He) as [H1 H2]. split; eapply Rle_trans;
        try eassumption; apply Rmin_r.
Qed.

Lemma ring_image_px_lower :
  forall r q, ring_image r q -> edges_minX (ring_edges r) <= px q.
Proof.
  intros r q [e [t [Hin [Ht [Hx _]]]]].
  rewrite Hx. eapply Rle_trans; [| apply convex_ge_min; exact Ht].
  destruct (in_edges_minX _ _ Hin) as [H1 H2]. apply Rmin_glb; assumption.
Qed.

Lemma ring_image_py_bound :
  forall r q, ring_image r q -> py q <= edges_maxY (ring_edges r).
Proof.
  intros r q [e [t [Hin [Ht [_ Hy]]]]].
  rewrite Hy. eapply Rle_trans; [apply convex_le_max; exact Ht |].
  destruct (in_edges_maxY _ _ Hin) as [H1 H2]. apply Rmax_lub; assumption.
Qed.

Lemma ring_image_py_lower :
  forall r q, ring_image r q -> edges_minY (ring_edges r) <= py q.
Proof.
  intros r q [e [t [Hin [Ht [_ Hy]]]]].
  rewrite Hy. eapply Rle_trans; [| apply convex_ge_min; exact Ht].
  destruct (in_edges_minY _ _ Hin) as [H1 H2]. apply Rmin_glb; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Segment and axis-aligned connectors in the complement.                 *)
(* -------------------------------------------------------------------------- *)

Lemma segment_connected_off_ring :
  forall (r : Ring) (p q : Point),
    (forall t, 0 <= t <= 1 ->
       ring_complement r
         (mkPoint ((1 - t) * px p + t * px q)
                  ((1 - t) * py p + t * py q))) ->
    connected_in_complement_cont r p q.
Proof.
  intros r p q Hfree.
  exists (fun t => mkPoint ((1 - t) * px p + t * px q)
                           ((1 - t) * py p + t * py q)).
  split; [apply straight_path_continuous |]. split; [| split].
  - destruct p as [x y]; cbn [px py]; f_equal; lra.
  - destruct q as [x y]; cbn [px py]; f_equal; lra.
  - intros t Ht. apply Hfree. exact Ht.
Qed.

Lemma far_right_connected :
  forall (r : Ring) (p q : Point),
    px p > edges_maxX (ring_edges r) ->
    px q > edges_maxX (ring_edges r) ->
    connected_in_complement_cont r p q.
Proof.
  intros r p q Hp Hq.
  apply segment_connected_off_ring.
  intros t Ht Himg. apply ring_image_px_bound in Himg. simpl in Himg.
  pose proof (convex_ge_min (px p) (px q) t Ht) as Hge.
  pose proof (Rmin_glb_lt (px p) (px q) (edges_maxX (ring_edges r)) Hp Hq).
  lra.
Qed.

Lemma far_left_connected :
  forall (r : Ring) (p q : Point),
    px p < edges_minX (ring_edges r) ->
    px q < edges_minX (ring_edges r) ->
    connected_in_complement_cont r p q.
Proof.
  intros r p q Hp Hq.
  apply segment_connected_off_ring.
  intros t Ht Himg. apply ring_image_px_lower in Himg. simpl in Himg.
  pose proof (convex_le_max (px p) (px q) t Ht) as Hle.
  assert (Hmax : Rmax (px p) (px q) < edges_minX (ring_edges r))
    by (apply Rmax_lub_lt; assumption).
  lra.
Qed.

Lemma far_top_connected :
  forall (r : Ring) (p q : Point),
    py p > edges_maxY (ring_edges r) ->
    py q > edges_maxY (ring_edges r) ->
    connected_in_complement_cont r p q.
Proof.
  intros r p q Hp Hq.
  apply segment_connected_off_ring.
  intros t Ht Himg. apply ring_image_py_bound in Himg. simpl in Himg.
  pose proof (convex_ge_min (py p) (py q) t Ht) as Hge.
  pose proof (Rmin_glb_lt (py p) (py q) (edges_maxY (ring_edges r)) Hp Hq).
  lra.
Qed.

Lemma far_bottom_connected :
  forall (r : Ring) (p q : Point),
    py p < edges_minY (ring_edges r) ->
    py q < edges_minY (ring_edges r) ->
    connected_in_complement_cont r p q.
Proof.
  intros r p q Hp Hq.
  apply segment_connected_off_ring.
  intros t Ht Himg. apply ring_image_py_lower in Himg. simpl in Himg.
  pose proof (convex_le_max (py p) (py q) t Ht) as Hle.
  assert (Hmax : Rmax (py p) (py q) < edges_minY (ring_edges r))
    by (apply Rmax_lub_lt; assumption).
  lra.
Qed.

Definition far_right_pt (r : Ring) : Point :=
  mkPoint (edges_maxX (ring_edges r) + 1) 0.

Lemma far_right_pt_is_far :
  forall r, px (far_right_pt r) > edges_maxX (ring_edges r).
Proof. intros r. unfold far_right_pt. simpl. lra. Qed.

(* A point strictly outside the (possibly dummy-loosened) AABB joins the
   canonical far-right point by at most three axis-aligned complement
   segments. *)
Lemma outside_aabb_to_far_right :
  forall (r : Ring) (p : Point),
    px p > edges_maxX (ring_edges r) \/
    px p < edges_minX (ring_edges r) \/
    py p > edges_maxY (ring_edges r) \/
    py p < edges_minY (ring_edges r) ->
    connected_in_complement_cont r p (far_right_pt r).
Proof.
  intros r p Hout.
  set (xmax := edges_maxX (ring_edges r)).
  set (xmin := edges_minX (ring_edges r)).
  set (ymax := edges_maxY (ring_edges r)).
  set (ymin := edges_minY (ring_edges r)).
  subst xmax xmin ymax ymin.
  destruct Hout as [Hr | [Hl | [Ht | Hb]]].
  - apply far_right_connected; [exact Hr | apply far_right_pt_is_far].
  - set (p_top := mkPoint (px p) (edges_maxY (ring_edges r) + 1)).
    set (p_tr := mkPoint (edges_maxX (ring_edges r) + 1)
                         (edges_maxY (ring_edges r) + 1)).
    assert (H1 : connected_in_complement_cont r p p_top).
    { apply far_left_connected; [exact Hl |].
      unfold p_top. simpl. exact Hl. }
    assert (H2 : connected_in_complement_cont r p_top p_tr).
    { apply far_top_connected; unfold p_top, p_tr; simpl; lra. }
    assert (H3 : connected_in_complement_cont r p_tr (far_right_pt r)).
    { apply far_right_connected; unfold p_tr, far_right_pt; simpl; lra. }
    eapply connected_in_complement_cont_trans; [exact H1 |].
    eapply connected_in_complement_cont_trans; [exact H2 | exact H3].
  - set (p_tr := mkPoint (edges_maxX (ring_edges r) + 1) (py p)).
    assert (H1 : connected_in_complement_cont r p p_tr).
    { apply far_top_connected; [exact Ht |].
      unfold p_tr. simpl. exact Ht. }
    assert (H2 : connected_in_complement_cont r p_tr (far_right_pt r)).
    { apply far_right_connected; unfold p_tr, far_right_pt; simpl; lra. }
    eapply connected_in_complement_cont_trans; [exact H1 | exact H2].
  - set (p_br := mkPoint (edges_maxX (ring_edges r) + 1) (py p)).
    assert (H1 : connected_in_complement_cont r p p_br).
    { apply far_bottom_connected; [exact Hb |].
      unfold p_br. simpl. exact Hb. }
    assert (H2 : connected_in_complement_cont r p_br (far_right_pt r)).
    { apply far_right_connected; unfold p_br, far_right_pt; simpl; lra. }
    eapply connected_in_complement_cont_trans; [exact H1 | exact H2].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Geometric interior sits in the AABB — uniform bound, any ring.         *)
(* -------------------------------------------------------------------------- *)

Lemma radius_defeated_by_abscissa :
  forall x y M, M > 0 -> M + 1 <= x \/ x <= - (M + 1) ->
    ~ (x * x + y * y <= M * M).
Proof.
  intros x y M HM Hor Hle.
  assert (Hsq : 0 <= y * y) by nra.
  destruct Hor as [Hpos | Hneg].
  - assert (M < x) by lra. nra.
  - assert (x < - M) by lra. nra.
Qed.

Lemma right_of_aabb_unbounded :
  forall (r : Ring) (p : Point),
    px p > edges_maxX (ring_edges r) ->
    ~ in_bounded_component_cont r p.
Proof.
  intros r p Hp [M [HM Hbnd]].
  set (X := Rmax (px p) (M + 1)).
  set (q := mkPoint X (py p)).
  assert (HXpx : px p <= X) by apply Rmax_l.
  assert (HXM : M + 1 <= X) by apply Rmax_r.
  assert (Hcon : connected_in_complement_cont r p q).
  { apply far_right_connected; [exact Hp |].
    unfold q. simpl.
    apply Rlt_le_trans with (px p); [exact Hp | apply Rmax_l]. }
  specialize (Hbnd q Hcon). unfold q in Hbnd. simpl in Hbnd.
  apply (radius_defeated_by_abscissa X (py p) M HM); [| exact Hbnd].
  left. apply Rmax_r.
Qed.

Lemma left_of_aabb_unbounded :
  forall (r : Ring) (p : Point),
    px p < edges_minX (ring_edges r) ->
    ~ in_bounded_component_cont r p.
Proof.
  intros r p Hp [M [HM Hbnd]].
  set (X := Rmin (px p) (- (M + 1))).
  set (q := mkPoint X (py p)).
  assert (HXpx : X <= px p) by apply Rmin_l.
  assert (HXM : X <= - (M + 1)) by apply Rmin_r.
  assert (Hcon : connected_in_complement_cont r p q).
  { apply far_left_connected; [exact Hp |].
    unfold q. simpl.
    apply Rle_lt_trans with (px p); [apply Rmin_l | exact Hp]. }
  specialize (Hbnd q Hcon). unfold q in Hbnd. simpl in Hbnd.
  apply (radius_defeated_by_abscissa X (py p) M HM); [| exact Hbnd].
  right. apply Rmin_r.
Qed.

Lemma above_aabb_unbounded :
  forall (r : Ring) (p : Point),
    py p > edges_maxY (ring_edges r) ->
    ~ in_bounded_component_cont r p.
Proof.
  intros r p Hp [M [HM Hbnd]].
  set (Y := Rmax (py p) (M + 1)).
  set (q := mkPoint (px p) Y).
  assert (Hcon : connected_in_complement_cont r p q).
  { apply far_top_connected; [exact Hp |].
    unfold q. simpl.
    apply Rlt_le_trans with (py p); [exact Hp | apply Rmax_l]. }
  specialize (Hbnd q Hcon). unfold q in Hbnd. simpl in Hbnd.
  apply (radius_defeated_by_abscissa Y (px p) M HM); [| nra].
  left. apply Rmax_r.
Qed.

Lemma below_aabb_unbounded :
  forall (r : Ring) (p : Point),
    py p < edges_minY (ring_edges r) ->
    ~ in_bounded_component_cont r p.
Proof.
  intros r p Hp [M [HM Hbnd]].
  set (Y := Rmin (py p) (- (M + 1))).
  set (q := mkPoint (px p) Y).
  assert (Hcon : connected_in_complement_cont r p q).
  { apply far_bottom_connected; [exact Hp |].
    unfold q. simpl.
    apply Rle_lt_trans with (py p); [apply Rmin_l | exact Hp]. }
  specialize (Hbnd q Hcon). unfold q in Hbnd. simpl in Hbnd.
  apply (radius_defeated_by_abscissa Y (px p) M HM); [| nra].
  right. apply Rmin_r.
Qed.

Theorem geometric_interior_in_aabb :
  forall (r : Ring) (p : Point),
    geometric_interior_cont p r ->
    edges_minX (ring_edges r) <= px p <= edges_maxX (ring_edges r) /\
    edges_minY (ring_edges r) <= py p <= edges_maxY (ring_edges r).
Proof.
  intros r p [Hoff Hbnd]. split; split.
  - destruct (Rle_dec (edges_minX (ring_edges r)) (px p)) as [H | H];
      [exact H |].
    exfalso. apply (left_of_aabb_unbounded r p); [lra | exact Hbnd].
  - destruct (Rle_dec (px p) (edges_maxX (ring_edges r))) as [H | H];
      [exact H |].
    exfalso. apply (right_of_aabb_unbounded r p); [lra | exact Hbnd].
  - destruct (Rle_dec (edges_minY (ring_edges r)) (py p)) as [H | H];
      [exact H |].
    exfalso. apply (below_aabb_unbounded r p); [lra | exact Hbnd].
  - destruct (Rle_dec (py p) (edges_maxY (ring_edges r))) as [H | H];
      [exact H |].
    exfalso. apply (above_aabb_unbounded r p); [lra | exact Hbnd].
Qed.

(* A single radius that confines every geometric-interior point of any
   closed polygonal ring — the uniform-bound clause of
   `JCT_two_components_cont`, for free, with no simplicity hypothesis.
   Dummy-0 AABB corners only loosen the radius. *)
Lemma abs_le_of_interval :
  forall a x b, a <= x <= b -> Rabs x <= Rmax (Rabs a) (Rabs b).
Proof.
  intros a x b [Hax Hxb].
  destruct (Rle_dec 0 x) as [Hx0 | Hx0].
  - rewrite (Rabs_right x) by lra.
    apply Rle_trans with b; [exact Hxb |].
    apply Rle_trans with (Rabs b); [apply Rle_abs | apply Rmax_r].
  - rewrite (Rabs_left x) by lra.
    apply Rle_trans with (Rabs a).
    + rewrite (Rabs_left1 a) by lra. lra.
    + apply Rmax_l.
Qed.

Lemma sq_le_of_abs_le :
  forall x w, 0 <= w -> Rabs x <= w -> x * x <= w * w.
Proof.
  intros x w Hw H.
  replace (x * x) with (Rabs x * Rabs x).
  2:{ rewrite <- Rabs_mult. apply Rabs_pos_eq. nra. }
  pose proof (Rabs_pos x). nra.
Qed.

Theorem geometric_interior_uniform_bound :
  forall (r : Ring),
    exists M : R,
      M > 0 /\
      forall p, geometric_interior_cont p r ->
        px p * px p + py p * py p <= M * M.
Proof.
  intros r.
  set (xmin := edges_minX (ring_edges r)).
  set (xmax := edges_maxX (ring_edges r)).
  set (ymin := edges_minY (ring_edges r)).
  set (ymax := edges_maxY (ring_edges r)).
  set (Wx := Rmax (Rabs xmin) (Rabs xmax)).
  set (Wy := Rmax (Rabs ymin) (Rabs ymax)).
  set (M := 1 + Wx + Wy).
  assert (HWx : 0 <= Wx).
  { unfold Wx. eapply Rle_trans; [apply Rabs_pos | apply Rmax_l]. }
  assert (HWy : 0 <= Wy).
  { unfold Wy. eapply Rle_trans; [apply Rabs_pos | apply Rmax_l]. }
  exists M. split.
  - unfold M. lra.
  - intros p Hint.
    destruct (geometric_interior_in_aabb r p Hint) as [Hx Hy].
    pose proof (abs_le_of_interval xmin (px p) xmax Hx) as Hxabs.
    pose proof (abs_le_of_interval ymin (py p) ymax Hy) as Hyabs.
    unfold Wx in Hxabs. unfold Wy in Hyabs.
    pose proof (sq_le_of_abs_le (px p) Wx HWx Hxabs) as Hpx.
    pose proof (sq_le_of_abs_le (py p) Wy HWy Hyabs) as Hpy.
    unfold M. nra.
Qed.

Print Assumptions geometric_interior_uniform_bound.
Print Assumptions geometric_interior_in_aabb.
Print Assumptions outside_aabb_to_far_right.
