(* ============================================================================
   NetTopologySuite.Proofs.RelateNGContains
   ----------------------------------------------------------------------------
   Issue #67: RelateNG pipeline — TPR_Contains regime correctness.

   Split (2026-08) from the former monolithic RelateNG.v; RelateNG.v remains
   as the re-export umbrella, so existing `Require Import RelateNG` clients
   (RelatePrepared.v) are unaffected.  Original section banners preserved.

   `gtri` is non-positive at a triangle's own vertices, so a strictly
   interior point can never be one of them; hence CCW + three strictly
   interior B-vertices force the classifier to TPR_Contains outright
   (`triangle_pair_regime_contains`, with `touch_edge_b`'s falsity DERIVED,
   not assumed).  Via TriangleContainmentConvex the flag is geometrically
   meaningful on B's whole boundary: closed (`contains_b_ring_inside`) and
   strict (`contains_b_ring_strictly_inside` — B's boundary never touches
   A's).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lia Lra Ranalysis Bool Btauto.
From NTS.Proofs Require Import Real.
From NTS.Proofs Require Import DE9IM Distance Overlay Segment RelateBoundary
  RelateLineLine RelateAreaPoint RelateAreaLine RelateAreaArea
  RelateMatrixLineLine RelateMatrixAreaLine RelateMatrixRect RelateMatrixTriangle
  RelateCurveMatrix RectangleJCT Intersect Orientation.  (* cross for between collinear *)
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity.  (* gtri / JCT planar covering for triangle interiors & exterior signs *)
From NTS.Proofs Require Import GeneralTriangleJCT GeneralTriangleExterior
  TriangleValidPolygon JCTSeamAssembly PointInRingCorrect PointInRingTangents
  JordanCurveSeam.  (* assembled in-house JCT converse: point_in_ring -> 0 < gtri *)
From NTS.Proofs Require Import TriangleContainmentConvex.
  (* gtri_region_is_convex / gtri_region_contains_segment: the closed gtri
     region is convex, so a segment with both endpoints inside stays inside --
     the missing step to lift a vertex-only containment test to a whole-edge
     containment fact for triangle_pair_regime's TPR_Contains case below. *)
From NTS.Proofs Require Import RelateNGCore.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Containment regime correctness.                                            *)
(* -------------------------------------------------------------------------- *)

(* `gtri` at A's own vertices is <= 0 (one of the three inward half-plane      *)
(* tests is exactly 0 there), so a strictly-interior point (0 < gtri) can      *)
(* never equal a vertex of A -- the fact `touch_edge_b`'s falsity rests on.    *)
Lemma gtri_at_own_vertex_a_le0 : forall ax ay bx by_ cx cy,
  gtri ax ay bx by_ cx cy (mkPoint ax ay) <= 0.
Proof.
  intros ax ay bx by_ cx cy. unfold gtri.
  assert (H : gsA ax ay bx by_ (mkPoint ax ay) = 0) by (unfold gsA; simpl; ring).
  rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ].
Qed.

Lemma gtri_at_own_vertex_b_le0 : forall ax ay bx by_ cx cy,
  gtri ax ay bx by_ cx cy (mkPoint bx by_) <= 0.
Proof.
  intros ax ay bx by_ cx cy. unfold gtri.
  assert (H : gsB bx by_ cx cy (mkPoint bx by_) = 0) by (unfold gsB; simpl; ring).
  rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_r_le ].
Qed.

Lemma gtri_at_own_vertex_c_le0 : forall ax ay bx by_ cx cy,
  gtri ax ay bx by_ cx cy (mkPoint cx cy) <= 0.
Proof.
  intros ax ay bx by_ cx cy. unfold gtri.
  assert (H : gsC ax ay cx cy (mkPoint cx cy) = 0) by (unfold gsC; simpl; ring).
  rewrite H. apply Rmin_r_le.
Qed.

Lemma gtri_pos_ne_vertex_a : forall ax ay bx by_ cx cy p,
  0 < gtri ax ay bx by_ cx cy p -> p <> mkPoint ax ay.
Proof.
  intros ax ay bx by_ cx cy p Hpos ->.
  pose proof (gtri_at_own_vertex_a_le0 ax ay bx by_ cx cy). lra.
Qed.

Lemma gtri_pos_ne_vertex_b : forall ax ay bx by_ cx cy p,
  0 < gtri ax ay bx by_ cx cy p -> p <> mkPoint bx by_.
Proof.
  intros ax ay bx by_ cx cy p Hpos ->.
  pose proof (gtri_at_own_vertex_b_le0 ax ay bx by_ cx cy). lra.
Qed.

Lemma gtri_pos_ne_vertex_c : forall ax ay bx by_ cx cy p,
  0 < gtri ax ay bx by_ cx cy p -> p <> mkPoint cx cy.
Proof.
  intros ax ay bx by_ cx cy p Hpos ->.
  pose proof (gtri_at_own_vertex_c_le0 ax ay bx by_ cx cy). lra.
Qed.

Lemma point_eqb_false : forall p q, p <> q -> point_eqb p q = false.
Proof.
  intros p q Hne. unfold point_eqb.
  destruct (Req_dec_T (px p) (px q)) as [Hx | Hx]; [ | reflexivity ].
  destruct (Req_dec_T (py p) (py q)) as [Hy | Hy]; [ | reflexivity ].
  exfalso. apply Hne. destruct p as [px0 py0], q as [px1 py1]. simpl in *. subst. reflexivity.
Qed.

(* touch_edge_b is false whenever B's three vertices are each distinct from    *)
(* all three of A's vertices: every `shares_edge_b` disjunct needs an          *)
(* A-vertex to literally equal a B-vertex, which is exactly what is ruled out. *)
Lemma touch_edge_b_false_of_ne :
  forall a1 a2 a3 b1 b2 b3 : Point,
    a1 <> b1 -> a1 <> b2 -> a1 <> b3 ->
    a2 <> b1 -> a2 <> b2 -> a2 <> b3 ->
    a3 <> b1 -> a3 <> b2 -> a3 <> b3 ->
    touch_edge_b a1 a2 a3 b1 b2 b3 = false.
Proof.
  intros a1 a2 a3 b1 b2 b3 H11 H12 H13 H21 H22 H23 H31 H32 H33.
  unfold touch_edge_b, shares_edge_b.
  rewrite (point_eqb_false a1 b1 H11), (point_eqb_false a1 b2 H12), (point_eqb_false a1 b3 H13),
          (point_eqb_false a2 b1 H21), (point_eqb_false a2 b2 H22), (point_eqb_false a2 b3 H23),
          (point_eqb_false a3 b1 H31), (point_eqb_false a3 b2 H32), (point_eqb_false a3 b3 H33).
  reflexivity.
Qed.

(* The headline: 0<gdbl A plus all three of B's vertices strictly interior to A
   forces the classifier to TPR_Contains -- unconditionally (touch_edge_b's
   falsity is DERIVED, not assumed, from the same three hypotheses). *)
Theorem triangle_pair_regime_contains :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy : R,
    0 < gdbl ax ay bx by_ cx cy ->
    0 < gtri ax ay bx by_ cx cy (mkPoint dx dy) ->
    0 < gtri ax ay bx by_ cx cy (mkPoint ex ey) ->
    0 < gtri ax ay bx by_ cx cy (mkPoint fx fy) ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy = TPR_Contains.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Hccw Hd He Hf.
  assert (Hda : mkPoint ax ay <> mkPoint dx dy)
    by (intro Heq; exact (gtri_pos_ne_vertex_a ax ay bx by_ cx cy _ Hd (eq_sym Heq))).
  assert (Hea : mkPoint ax ay <> mkPoint ex ey)
    by (intro Heq; exact (gtri_pos_ne_vertex_a ax ay bx by_ cx cy _ He (eq_sym Heq))).
  assert (Hfa : mkPoint ax ay <> mkPoint fx fy)
    by (intro Heq; exact (gtri_pos_ne_vertex_a ax ay bx by_ cx cy _ Hf (eq_sym Heq))).
  assert (Hdb : mkPoint bx by_ <> mkPoint dx dy)
    by (intro Heq; exact (gtri_pos_ne_vertex_b ax ay bx by_ cx cy _ Hd (eq_sym Heq))).
  assert (Heb : mkPoint bx by_ <> mkPoint ex ey)
    by (intro Heq; exact (gtri_pos_ne_vertex_b ax ay bx by_ cx cy _ He (eq_sym Heq))).
  assert (Hfb : mkPoint bx by_ <> mkPoint fx fy)
    by (intro Heq; exact (gtri_pos_ne_vertex_b ax ay bx by_ cx cy _ Hf (eq_sym Heq))).
  assert (Hdc : mkPoint cx cy <> mkPoint dx dy)
    by (intro Heq; exact (gtri_pos_ne_vertex_c ax ay bx by_ cx cy _ Hd (eq_sym Heq))).
  assert (Hec : mkPoint cx cy <> mkPoint ex ey)
    by (intro Heq; exact (gtri_pos_ne_vertex_c ax ay bx by_ cx cy _ He (eq_sym Heq))).
  assert (Hfc : mkPoint cx cy <> mkPoint fx fy)
    by (intro Heq; exact (gtri_pos_ne_vertex_c ax ay bx by_ cx cy _ Hf (eq_sym Heq))).
  unfold triangle_pair_regime.
  rewrite (touch_edge_b_false_of_ne (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
             (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy)
             Hda Hea Hfa Hdb Heb Hfb Hdc Hec Hfc).
  unfold contains_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [_ | Hn]; [ | contradiction ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint dx dy))) as [_ | Hn]; [ | contradiction ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint ex ey))) as [_ | Hn]; [ | contradiction ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint fx fy))) as [_ | Hn]; [ | contradiction ].
  reflexivity.
Qed.

(* Geometric correctness: whenever `contains_b` flags containment, every point
   on any of B's three EDGES (not just its vertices) is inside A's closed
   region.  This is the honest content behind wiring TPR_Contains: the
   vertex-only test would be unsound without it (an edge could otherwise dip
   outside A between two vertices that individually pass). *)
Theorem contains_b_ring_inside :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy p,
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    (between (mkPoint dx dy) (mkPoint ex ey) p \/
     between (mkPoint ex ey) (mkPoint fx fy) p \/
     between (mkPoint fx fy) (mkPoint dx dy) p) ->
    0 <= gtri ax ay bx by_ cx cy p.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy p Hc Hb.
  unfold contains_b in Hc.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [_ | Hn]; [ | discriminate ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint dx dy))) as [Hd | Hn]; [ | discriminate ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint ex ey))) as [He | Hn]; [ | discriminate ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint fx fy))) as [Hf | Hn]; [ | discriminate ].
  clear Hc.
  destruct Hb as [Hb | [Hb | Hb]].
  - exact (gtri_region_contains_segment ax ay bx by_ cx cy (mkPoint dx dy) (mkPoint ex ey) p
             (Rlt_le _ _ Hd) (Rlt_le _ _ He) Hb).
  - exact (gtri_region_contains_segment ax ay bx by_ cx cy (mkPoint ex ey) (mkPoint fx fy) p
             (Rlt_le _ _ He) (Rlt_le _ _ Hf) Hb).
  - exact (gtri_region_contains_segment ax ay bx by_ cx cy (mkPoint fx fy) (mkPoint dx dy) p
             (Rlt_le _ _ Hf) (Rlt_le _ _ Hd) Hb).
Qed.

(* RGR pivot (risk/cost): the sharper cousin of `contains_b_ring_inside`,
   costing nothing extra now that `TriangleContainmentConvex` supplies the
   strict-region convexity lemma (the extra work is a single three-way case
   split on the convex-combination parameter t -- see that file's §5 -- since
   strict positivity of a convex combination is a disjunctive fact
   (endpoint-vs-interior) that isn't a one-shot `nra` certificate the way the
   non-strict `0 <= gtri` version is). Every point on B's boundary is not
   merely in A's CLOSURE but STRICTLY interior to A -- B's boundary never
   touches A's boundary.  Closes the boundary-separation half of the
   `geom_de9im_pointset` obligation for TPR_Contains flagged in
   `RelateCurveMatrix.geom_de9im_ii_cell_dim2_sound`'s comment.

   The exact-matrix gap this comment used to leave open is the #576 /
   522-h contains split (`RelateNGContainsCells.v`): it names
   `aa_matrix_contains_ogc` = 212FF1FF2 and proves the nine gtri cells
   on the #567 pair, including IB dim-1.  It does not remint
   `aa_matrix_contains` (still empty IB).  `geom_de9im_pointset` on
   `point_set` remains open (ADR-0003). *)
Theorem contains_b_ring_strictly_inside :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy p,
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    (between (mkPoint dx dy) (mkPoint ex ey) p \/
     between (mkPoint ex ey) (mkPoint fx fy) p \/
     between (mkPoint fx fy) (mkPoint dx dy) p) ->
    0 < gtri ax ay bx by_ cx cy p.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy p Hc Hb.
  unfold contains_b in Hc.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [_ | Hn]; [ | discriminate ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint dx dy))) as [Hd | Hn]; [ | discriminate ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint ex ey))) as [He | Hn]; [ | discriminate ].
  destruct (Rlt_dec 0 (gtri ax ay bx by_ cx cy (mkPoint fx fy))) as [Hf | Hn]; [ | discriminate ].
  clear Hc.
  destruct Hb as [Hb | [Hb | Hb]].
  - exact (gtri_region_strict_contains_segment ax ay bx by_ cx cy (mkPoint dx dy) (mkPoint ex ey) p
             Hd He Hb).
  - exact (gtri_region_strict_contains_segment ax ay bx by_ cx cy (mkPoint ex ey) (mkPoint fx fy) p
             He Hf Hb).
  - exact (gtri_region_strict_contains_segment ax ay bx by_ cx cy (mkPoint fx fy) (mkPoint dx dy) p
             Hf Hd Hb).
Qed.

Print Assumptions triangle_pair_regime_contains.
Print Assumptions contains_b_ring_inside.
Print Assumptions contains_b_ring_strictly_inside.
