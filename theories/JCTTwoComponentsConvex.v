(* ============================================================================
   NetTopologySuite.Proofs.JCTTwoComponentsConvex
   ----------------------------------------------------------------------------
   The highest named Phase-3 residual, discharged for every half-plane-
   presented convex ring: `JCT_two_components_cont_simple`.

   `JordanCurveSeam.JCT_two_components_cont_simple` is the canonical
   two-component Jordan Prop (partition + path-connected components +
   separation + interior bounded + exterior unbounded), guarded by
   `ring_vertices_distinct` so the bowtie does not refute it.  Until this
   file it was a named, unproved hypothesis.  The H1 campaign already
   closed the *parity* seam for taut rings (`parity_seam_offring_taut`)
   and for convex families (`convex_parity_seam_offring_of`).  What that
   campaign does not give is that the two components are each
   path-connected — the load-bearing half of the two-component statement.

   For a ring presented as the intersection of nonempty, non-degenerate
   half-planes (`conv_min`), that half is algebraic:

     interior  :=  0 < conv_min hps
     exterior  :=  conv_min hps < 0

   - Off-ring points trichotomise (zero-set on the skeleton).
   - The open intersection of half-planes is convex, so any two interior
     points join by a segment that stays strictly positive, hence off
     the skeleton.
   - An exterior point violates some half-plane; the outward-normal ray
     stays exterior and eventually leaves the axis-aligned bounding box
     of the skeleton.  Any two points outside that box join through the
     far-right half-plane `x > edges_maxX` (a straight segment, or an
     L-walk around the box).
   - Separation is the IVT on `conv_min` along a complement path
     (sign change would hit the skeleton).
   - Interior boundedness is the family's radius obligation (already
     required by `convex_parity_seam_offring_of`).
   - Exterior unboundedness is the same outward ray, from any one
     half-plane, to arbitrary radius.

   Instantiation: the diamond (`diamond_ring` + `diamond_hps`) inherits
   the four presentation facts from `DiamondOffringSeam.v`, so
   `JCT_two_components_cont_simple diamond_ring` is a theorem.

   Honest residual (unchanged): the same Prop for a *general* simple
   ring, and interior/exterior path-connectedness for taut non-convex
   rings.  This file does not claim those.

   Pure-R; three-axiom.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Grok 4.6
   ========================================================================== *)

From Stdlib Require Import Reals Lra List.
From Stdlib Require Import Ranalysis Ranalysis5.
From NTS.Proofs Require Import Distance Overlay PointInRingTangents JordanCurveSeam.
From NTS.Proofs Require Import JCT ConvexField ConvexOffringSeam.
From NTS.Proofs Require Import ConvexChainSplit DiamondOffringSeam.

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

(* -------------------------------------------------------------------------- *)
(* §4  Convex-field algebra: slacks along segments and outward rays.          *)
(* -------------------------------------------------------------------------- *)

Lemma hp_slack_affine :
  forall (hp : R * R * R) (p q : Point) (t : R),
    hp_slack hp
      (mkPoint ((1 - t) * px p + t * px q)
               ((1 - t) * py p + t * py q)) =
    (1 - t) * hp_slack hp p + t * hp_slack hp q.
Proof.
  intros [[a b] c] p q t. unfold hp_slack. cbn [px py]. ring.
Qed.

Lemma conv_min_segment_pos :
  forall (hps : list (R * R * R)) (p q : Point) (t : R),
    0 < conv_min hps p ->
    0 < conv_min hps q ->
    0 <= t <= 1 ->
    0 < conv_min hps
      (mkPoint ((1 - t) * px p + t * px q)
               ((1 - t) * py p + t * py q)).
Proof.
  intros hps p q t Hp Hq Ht.
  apply conv_min_pos_iff.
  apply conv_min_pos_iff in Hp. apply conv_min_pos_iff in Hq.
  rewrite Forall_forall in Hp, Hq. apply Forall_forall.
  intros hp Hin. rewrite hp_slack_affine.
  pose proof (Hp hp Hin). pose proof (Hq hp Hin). nra.
Qed.

Lemma hp_slack_ray :
  forall (a b c u v T : R),
    hp_slack (a, b, c) (mkPoint (u + T * a) (v + T * b)) =
    hp_slack (a, b, c) (mkPoint u v) - T * (a * a + b * b).
Proof. intros. unfold hp_slack. cbn [px py]. ring. Qed.

Lemma hp_nondeg_of :
  forall (hps : list (R * R * R)) (hp : R * R * R),
    Forall (fun hp0 : R * R * R =>
              let '(a, b, _) := hp0 in 0 < a * a + b * b) hps ->
    In hp hps ->
    let '(a, b, _) := hp in 0 < a * a + b * b.
Proof.
  intros hps hp HF Hin. rewrite Forall_forall in HF. exact (HF hp Hin).
Qed.

(* Outward-normal ray from a violated half-plane stays off the skeleton. *)
Lemma convex_ray_off_ring :
  forall (r : Ring) (a b c : R) (p : Point) (T t : R),
    0 < a * a + b * b ->
    vertices_in_halfplane r (a, b, c) ->
    hp_slack (a, b, c) p < 0 ->
    0 <= T ->
    0 <= t <= 1 ->
    ring_complement r
      (mkPoint (px p + (t * T) * a) (py p + (t * T) * b)).
Proof.
  intros r a b c p T t Hs Hv Hp HT Ht Himg.
  destruct p as [u v]. cbn [px py] in *.
  pose proof (image_slack_nonneg r (a, b, c)
                (mkPoint (u + (t * T) * a) (v + (t * T) * b))
                Hv Himg) as Hske.
  unfold hp_slack in Hp, Hske. cbn [px py] in Hp, Hske.
  assert (Hexp : c - (a * (u + t * T * a) + b * (v + t * T * b))
                 = (c - (a * u + b * v)) - t * T * (a * a + b * b))
    by ring.
  rewrite Hexp in Hske.
  assert (Ht0 : 0 <= t) by lra.
  assert (Hs0 : 0 <= a * a + b * b) by nra.
  assert (Htt : 0 <= t * T) by (apply Rmult_le_pos; lra).
  assert (Hprod : 0 <= t * T * (a * a + b * b))
    by (apply Rmult_le_pos; lra).
  lra.
Qed.

Lemma convex_ray_connected :
  forall (r : Ring) (a b c : R) (p : Point) (T : R),
    0 < a * a + b * b ->
    vertices_in_halfplane r (a, b, c) ->
    hp_slack (a, b, c) p < 0 ->
    0 <= T ->
    connected_in_complement_cont r p
      (mkPoint (px p + T * a) (py p + T * b)).
Proof.
  intros r a b c p T Hs Hv Hp HT.
  apply segment_connected_off_ring.
  intros t Ht. cbn [px py].
  replace ((1 - t) * px p + t * (px p + T * a))
    with (px p + (t * T) * a) by ring.
  replace ((1 - t) * py p + t * (py p + T * b))
    with (py p + (t * T) * b) by ring.
  apply (convex_ray_off_ring r a b c p T t Hs Hv Hp HT Ht).
Qed.

(* A large enough time pushes the outward ray strictly outside the AABB. *)
Definition escape_time (a b u v xmax xmin ymax ymin : R) : R :=
  match Rlt_dec 0 a with
  | left _ => Rmax 0 ((xmax + 1 - u) / a) + 1
  | right _ =>
    match Rlt_dec a 0 with
    | left _ => Rmax 0 ((xmin - 1 - u) / a) + 1
    | right _ =>
      match Rlt_dec 0 b with
      | left _ => Rmax 0 ((ymax + 1 - v) / b) + 1
      | right _ => Rmax 0 ((ymin - 1 - v) / b) + 1
      end
    end
  end.

Lemma escape_time_nonneg :
  forall a b u v xmax xmin ymax ymin,
    0 <= escape_time a b u v xmax xmin ymax ymin.
Proof.
  intros a b u v xmax xmin ymax ymin.
  unfold escape_time.
  destruct (Rlt_dec 0 a); [| destruct (Rlt_dec a 0); [| destruct (Rlt_dec 0 b)]];
    pose proof (Rmax_l 0 ((xmax + 1 - u) / a));
    pose proof (Rmax_l 0 ((xmin - 1 - u) / a));
    pose proof (Rmax_l 0 ((ymax + 1 - v) / b));
    pose proof (Rmax_l 0 ((ymin - 1 - v) / b)); lra.
Qed.

Lemma escape_time_leaves_aabb :
  forall a b u v xmax xmin ymax ymin,
    0 < a * a + b * b ->
    let T := escape_time a b u v xmax xmin ymax ymin in
    u + T * a > xmax \/
    u + T * a < xmin \/
    v + T * b > ymax \/
    v + T * b < ymin.
Proof.
  intros a b u v xmax xmin ymax ymin Hs T.
  unfold T, escape_time.
  destruct (Rlt_dec 0 a) as [Ha | Hna].
  - left.
    set (k := (xmax + 1 - u) / a).
    assert (HT : Rmax 0 k + 1 >= k + 1) by (pose proof (Rmax_r 0 k); lra).
    assert (Hk : k * a = xmax + 1 - u) by (unfold k; field; lra).
    nra.
  - destruct (Rlt_dec a 0) as [Ha | Hna'].
    + right. left.
      set (k := (xmin - 1 - u) / a).
      assert (HT : Rmax 0 k + 1 >= k + 1) by (pose proof (Rmax_r 0 k); lra).
      assert (Hk : k * a = xmin - 1 - u) by (unfold k; field; lra).
      nra.
    + assert (Hb0 : b <> 0) by nra.
      destruct (Rlt_dec 0 b) as [Hb | Hnb].
      * right. right. left.
        set (k := (ymax + 1 - v) / b).
        assert (HT : Rmax 0 k + 1 >= k + 1) by (pose proof (Rmax_r 0 k); lra).
        assert (Hk : k * b = ymax + 1 - v) by (unfold k; field; lra).
        nra.
      * right. right. right.
        assert (Hb : b < 0) by lra.
        set (k := (ymin - 1 - v) / b).
        assert (HT : Rmax 0 k + 1 >= k + 1) by (pose proof (Rmax_r 0 k); lra).
        assert (Hk : k * b = ymin - 1 - v) by (unfold k; field; lra).
        nra.
Qed.

Lemma convex_exterior_to_far_right :
  forall (r : Ring) (a b c : R) (p : Point),
    0 < a * a + b * b ->
    vertices_in_halfplane r (a, b, c) ->
    hp_slack (a, b, c) p < 0 ->
    connected_in_complement_cont r p (far_right_pt r).
Proof.
  intros r a b c p Hs Hv Hp.
  set (T := escape_time a b (px p) (py p)
              (edges_maxX (ring_edges r))
              (edges_minX (ring_edges r))
              (edges_maxY (ring_edges r))
              (edges_minY (ring_edges r))).
  pose proof (escape_time_nonneg a b (px p) (py p)
                (edges_maxX (ring_edges r))
                (edges_minX (ring_edges r))
                (edges_maxY (ring_edges r))
                (edges_minY (ring_edges r))) as HT.
  set (q := mkPoint (px p + T * a) (py p + T * b)).
  assert (Hray : connected_in_complement_cont r p q).
  { apply (convex_ray_connected r a b c p T Hs Hv Hp HT). }
  assert (Hout : px q > edges_maxX (ring_edges r) \/
                 px q < edges_minX (ring_edges r) \/
                 py q > edges_maxY (ring_edges r) \/
                 py q < edges_minY (ring_edges r)).
  { unfold q. simpl.
    apply (escape_time_leaves_aabb a b (px p) (py p)
             (edges_maxX (ring_edges r))
             (edges_minX (ring_edges r))
             (edges_maxY (ring_edges r))
             (edges_minY (ring_edges r)) Hs). }
  eapply connected_in_complement_cont_trans; [exact Hray |].
  apply outside_aabb_to_far_right. exact Hout.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Interior / exterior connectivity and IVT separation.                   *)
(*                                                                            *)
(* Tightness (`0 < conv_min → off-ring`) is the converse direction the        *)
(* zero-set obligation does not give: a half-plane list that fails to cut     *)
(* the skeleton can have skeleton points sitting in the *open* intersection.  *)
(* Every honest edge-half-plane presentation satisfies it (a supporting       *)
(* slack vanishes on each edge).                                              *)
(* -------------------------------------------------------------------------- *)

Lemma convex_interior_connected :
  forall (r : Ring) (hps : list (R * R * R)) (a b : Point),
    (forall pt, 0 < conv_min hps pt -> ring_complement r pt) ->
    0 < conv_min hps a ->
    0 < conv_min hps b ->
    connected_in_complement_cont r a b.
Proof.
  intros r hps a b Htight Ha Hb.
  apply segment_connected_off_ring.
  intros t Ht.
  apply Htight.
  apply (conv_min_segment_pos hps a b t Ha Hb Ht).
Qed.

Lemma convex_exterior_connected :
  forall (r : Ring) (hps : list (R * R * R)) (a b : Point),
    Forall (vertices_in_halfplane r) hps ->
    Forall (fun hp : R * R * R =>
              let '(x, y, _) := hp in 0 < x * x + y * y) hps ->
    conv_min hps a < 0 ->
    conv_min hps b < 0 ->
    connected_in_complement_cont r a b.
Proof.
  intros r hps a b Hverts Hnd Ha Hb.
  destruct (conv_min_neg_inv hps a Ha) as [hpa [Hina Hsa]].
  destruct (conv_min_neg_inv hps b Hb) as [hpb [Hinb Hsb]].
  destruct hpa as [[aa ba] ca].
  destruct hpb as [[ab bb] cb].
  pose proof (hp_nondeg_of hps (aa, ba, ca) Hnd Hina) as Hnda.
  pose proof (hp_nondeg_of hps (ab, bb, cb) Hnd Hinb) as Hndb.
  rewrite Forall_forall in Hverts.
  pose proof (Hverts (aa, ba, ca) Hina) as Hva.
  pose proof (Hverts (ab, bb, cb) Hinb) as Hvb.
  pose proof (convex_exterior_to_far_right r aa ba ca a Hnda Hva Hsa) as HaF.
  pose proof (convex_exterior_to_far_right r ab bb cb b Hndb Hvb Hsb) as HbF.
  apply connected_in_complement_cont_trans with (q := far_right_pt r).
  - exact HaF.
  - apply connected_in_complement_cont_sym. exact HbF.
Qed.

Lemma convex_field_ivt_zero :
  forall (hps : list (R * R * R)) (g : R -> Point),
    path_continuous g ->
    0 < conv_min hps (g 0) ->
    conv_min hps (g 1) < 0 ->
    exists t, 0 <= t <= 1 /\ conv_min hps (g t) = 0.
Proof.
  intros hps g [Hcx Hcy] Hpos Hneg.
  set (F := fun t => conv_min hps (g t)).
  assert (HcF : forall a, 0 <= a <= 1 -> continuity_pt F a).
  { intros a _. unfold F. apply continuity_pt_conv_min_path;
      [apply Hcx | apply Hcy]. }
  assert (Hc' : forall a, 0 <= a <= 1 -> continuity_pt (fun t => - F t) a)
    by (intros a Ha; apply continuity_pt_opp; apply HcF; exact Ha).
  destruct (IVT_interv (fun t => - F t) 0 1 Hc' Rlt_0_1) as [z [Hz Hzeq]];
    [unfold F; lra | unfold F; lra |].
  exists z. split; [exact Hz |]. unfold F in Hzeq. lra.
Qed.

Lemma convex_components_separated :
  forall (r : Ring) (hps : list (R * R * R)) (a b : Point),
    (forall pt, conv_min hps pt = 0 -> ring_image r pt) ->
    0 < conv_min hps a ->
    conv_min hps b < 0 ->
    ~ connected_in_complement_cont r a b.
Proof.
  intros r hps a b Hzero Ha Hb [g [Hcont [Hg0 [Hg1 Hcompl]]]].
  rewrite <- Hg0 in Ha. rewrite <- Hg1 in Hb.
  destruct (convex_field_ivt_zero hps g Hcont Ha Hb) as [t [Ht Hz]].
  apply (Hcompl t Ht). apply Hzero. exact Hz.
Qed.

Lemma convex_exterior_unbounded :
  forall (r : Ring) (hps : list (R * R * R)),
    hps <> [] ->
    Forall (fun hp : R * R * R =>
              let '(x, y, _) := hp in 0 < x * x + y * y) hps ->
    (forall pt, conv_min hps pt = 0 -> ring_image r pt) ->
    forall M : R,
      exists q : Point,
        conv_min hps q < 0 /\
        px q * px q + py q * py q > M * M.
Proof.
  intros r hps Hne Hnd Hzero M.
  destruct hps as [| hp rest]; [congruence |].
  destruct hp as [[a b] c].
  assert (Hs : 0 < a * a + b * b).
  { inversion Hnd. exact H1. }
  set (s := a * a + b * b).
  set (K := Rabs M + Rabs c + 1).
  set (T := Rabs M + 1 + K / s).
  assert (HK : 0 < K).
  { unfold K. pose proof (Rabs_pos M). pose proof (Rabs_pos c). lra. }
  assert (HT : 0 < T).
  { unfold T. apply Rplus_lt_0_compat.
    - pose proof (Rabs_pos M). lra.
    - apply Rdiv_lt_0_compat; [exact HK | unfold s; exact Hs]. }
  set (q := mkPoint (T * a) (T * b)).
  exists q. split.
  - assert (Hsl : hp_slack (a, b, c) q = c - T * s).
    { unfold q, hp_slack, s. cbn [px py]. ring. }
    assert (Hneg : hp_slack (a, b, c) q < 0).
    { rewrite Hsl.
      assert (HTs : T * s = (Rabs M + 1) * s + K).
      { unfold T. field. unfold s. lra. }
      rewrite HTs. unfold K, s.
      pose proof (Rabs_pos M). pose proof (Rabs_pos c).
      assert (Hcabs : c <= Rabs c) by apply Rle_abs.
      assert (0 < (Rabs M + 1) * (a * a + b * b)) by nra.
      lra. }
    apply Rle_lt_trans with (hp_slack (a, b, c) q); [| exact Hneg].
    apply conv_min_le_in. left. reflexivity.
  - unfold q. cbn [px py].
    assert (HCS : (T * a) * (T * a) + (T * b) * (T * b) = T * T * s)
      by (unfold s; ring).
    rewrite HCS.
    assert (HTs : T * s = (Rabs M + 1) * s + K).
    { unfold T. field. unfold s. lra. }
    assert (HT1 : Rabs M + 1 < T).
    { unfold T. rewrite <- (Rplus_0_r (Rabs M + 1)) at 1.
      apply Rplus_lt_compat_l.
      apply Rdiv_lt_0_compat; [exact HK | unfold s; exact Hs]. }
    assert (HTs1 : Rabs M + 1 < T * s).
    { rewrite HTs. unfold K. pose proof (Rabs_pos M). pose proof (Rabs_pos c).
      nra. }
    assert (HM2 : M * M <= (Rabs M + 1) * (Rabs M + 1)).
    { pose proof (Rabs_pos M).
      replace (M * M) with (Rabs M * Rabs M)
        by (rewrite <- Rabs_mult, Rabs_pos_eq; nra). nra. }
    apply Rle_lt_trans with ((Rabs M + 1) * (Rabs M + 1)); [exact HM2 |].
    replace (T * T * s) with (T * (T * s)) by ring.
    pose proof (Rabs_pos M) as HMabs.
    nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  HEADLINE: the two-component JCT Prop for a half-plane presentation.    *)
(* -------------------------------------------------------------------------- *)

Theorem convex_hp_jct_two_components_cont_simple :
  forall (r : Ring) (hps : list (R * R * R)) (M : R),
    hps <> [] ->
    (forall pt, conv_min hps pt = 0 -> ring_image r pt) ->
    (forall pt, 0 < conv_min hps pt -> ring_complement r pt) ->
    Forall (vertices_in_halfplane r) hps ->
    Forall (fun hp : R * R * R =>
              let '(x, y, _) := hp in 0 < x * x + y * y) hps ->
    0 < M ->
    (forall pt, 0 < conv_min hps pt ->
                px pt * px pt + py pt * py pt <= M * M) ->
    JCT_two_components_cont_simple r.
Proof.
  intros r hps M Hne Hzero Htight Hverts Hnd HM Hbound.
  intros _Hs _Hc _Hm _Hvd.
  exists (fun q => 0 < conv_min hps q),
         (fun q => conv_min hps q < 0).
  split; [| split; [| split; [| split; [| split]]]].
  - intros q Hoff. split.
    + destruct (Rtotal_order (conv_min hps q) 0) as [Hneg | [Hz | Hpos]].
      * right. exact Hneg.
      * exfalso. apply Hoff. apply Hzero. exact Hz.
      * left. exact Hpos.
    + intros [Hpos Hneg]. lra.
  - intros a b Ha Hb.
    apply (convex_interior_connected r hps a b Htight Ha Hb).
  - intros a b Ha Hb.
    apply (convex_exterior_connected r hps a b Hverts Hnd Ha Hb).
  - intros a b Ha Hb.
    apply (convex_components_separated r hps a b Hzero Ha Hb).
  - exists M. split; [exact HM |].
    intros q Hq. apply Hbound. exact Hq.
  - intros N.
    destruct (convex_exterior_unbounded r hps Hne Hnd Hzero N)
      as [q [Hqext Hqbig]].
    exists q. split; [exact Hqext | exact Hqbig].
Qed.

(* -------------------------------------------------------------------------- *)
(* §7  Diamond instance — first concrete discharge of the two-component Prop. *)
(* -------------------------------------------------------------------------- *)

Lemma diamond_hps_nonempty : diamond_hps <> [].
Proof. unfold diamond_hps. discriminate. Qed.

Lemma diamond_pos_off_ring :
  forall pt, 0 < conv_min diamond_hps pt -> ring_complement diamond_ring pt.
Proof.
  intros pt Hpos Himg.
  assert (Hall : Forall (fun hp => 0 <= hp_slack hp pt) diamond_hps).
  { rewrite Forall_forall. intros hp Hhp.
    apply (image_slack_nonneg diamond_ring hp pt).
    - pose proof (proj1 (Forall_forall (vertices_in_halfplane diamond_ring)
                         diamond_hps) diamond_vertices_in_hps hp Hhp) as Hv.
      exact Hv.
    - exact Himg. }
  assert (Hnn : 0 <= conv_min diamond_hps pt)
    by (apply conv_min_nonneg; exact Hall).
  (* supporting slack vanishes on each diamond edge *)
  destruct Himg as [e [t [Hin [Ht [Hx Hy]]]]].
  rewrite ring_edges_diamond in Hin.
  assert (Hle0 : conv_min diamond_hps pt <= 0).
  { destruct Hin as [He | [He | [He | [He | []]]]]; subst e;
      cbn [fst snd px py] in Hx, Hy.
    - eapply Rle_trans;
        [apply (conv_min_le_in diamond_hps pt (1, -1, 2));
         unfold diamond_hps; left; reflexivity |].
      unfold hp_slack; cbn [px py]; rewrite Hx, Hy; lra.
    - eapply Rle_trans;
        [apply (conv_min_le_in diamond_hps pt (1, 1, 2));
         unfold diamond_hps; right; left; reflexivity |].
      unfold hp_slack; cbn [px py]; rewrite Hx, Hy; lra.
    - eapply Rle_trans;
        [apply (conv_min_le_in diamond_hps pt (-1, 1, 2));
         unfold diamond_hps; right; right; left; reflexivity |].
      unfold hp_slack; cbn [px py]; rewrite Hx, Hy; lra.
    - eapply Rle_trans;
        [apply (conv_min_le_in diamond_hps pt (-1, -1, 2));
         unfold diamond_hps; right; right; right; left; reflexivity |].
      unfold hp_slack; cbn [px py]; rewrite Hx, Hy; lra. }
  lra.
Qed.

Theorem diamond_jct_two_components_cont_simple :
  JCT_two_components_cont_simple diamond_ring.
Proof.
  apply (convex_hp_jct_two_components_cont_simple
           diamond_ring diamond_hps 2
           diamond_hps_nonempty
           diamond_zero_on_skeleton
           diamond_pos_off_ring
           diamond_vertices_in_hps
           diamond_hps_nondeg).
  - lra.
  - exact diamond_bounded.
Qed.

(* -------------------------------------------------------------------------- *)
(* Audit footprint.                                                           *)
(* -------------------------------------------------------------------------- *)

Print Assumptions geometric_interior_uniform_bound.
Print Assumptions convex_hp_jct_two_components_cont_simple.
Print Assumptions diamond_jct_two_components_cont_simple.
