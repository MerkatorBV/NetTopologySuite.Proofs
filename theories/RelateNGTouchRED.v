(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchRED
   ----------------------------------------------------------------------------
   Issue #67: RelateNG pipeline — touch II point-set separation is NOT
   unconditional (RED refutation).

   Split (2026-08) from the former monolithic RelateNG.v; RelateNG.v remains
   as the re-export umbrella, so existing `Require Import RelateNG` clients
   (RelatePrepared.v) are unaffected.  Original section banners preserved.

   Two CCW triangles touching on the shared edge (0,0)-(0,2) whose parity
   SInt point-sets genuinely overlap at the vertex-grazing witness
   p = (-1,1): membership in B is genuine (0 < gtri), membership in A is
   SPURIOUS (the rightward ray grazes A's far vertex (4,1) while
   gtri A p < 0).  Hence a guard-free II `cell_ok None SInt SInt` for the
   touch regime would be a FALSE theorem — the ray-genericity guard carried
   by `touch_triangle_pair_ii_cell_via_seam` (RelateNGTouchCells.v) is
   essential.

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
From NTS.Proofs Require Import RelateNGCore RelateNGTouch.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* NECESSITY of the guard: the point-set II separation is NOT unconditional.   *)
(*                                                                            *)
(* `touch_triangle_pair_ii_cell_via_seam` (RelateNGTouchCells.v) carries a     *)
(* genericity residual (every common interior witness is off both ring images  *)
(* AND ray-generic for both).                                                  *)
(* This section proves that residual CANNOT be dropped -- an unconditional     *)
(* (guard-free) lift of H_ii_disjoint would be a FALSE theorem -- by a         *)
(* concrete, Qed-closed refutation:                                           *)
(*                                                                            *)
(*     A = (0,0),(4,1),(0,2)   and   B = (0,0),(0,2),(-4,1)                     *)
(*                                                                            *)
(* are BOTH CCW and touch on the shared edge (0,0)-(0,2) (third vertices       *)
(* (4,1),(-4,1) on opposite sides), yet the point p = (-1,1) lies in the       *)
(* parity point-set (in_stratum SInt) of BOTH.  For B the membership is        *)
(* genuine (0 < gtri B p).  For A it is SPURIOUS: p's rightward ray GRAZES     *)
(* A's vertex (4,1) -- ray_avoids_vertices FAILS -- so the parity count reads  *)
(* "inside" while p is algebraically EXTERIOR (gtri A p < 0).  This is exactly *)
(* the false-POSITIVE that the ray-genericity guard exists to exclude, and it  *)
(* is distinct from the false-NEGATIVE diamond graze in                        *)
(* JCT_VertexGrazingCounterexample.v (there parity misses a true interior      *)
(* point; here parity invents a spurious one).  Because p is off both ring     *)
(* images, ring_complement alone does NOT rescue the lift: the ray-genericity  *)
(* premise is essential, so `touch_triangle_pair_ii_cell_via_seam` is maximal. *)
(*                                                                            *)
(*        (0,2)                                                              *)
(*         /|\                                                               *)
(*        / | \                                                              *)
(*   B   /  |  \   A         p = (-1,1) --------> ray (rightward, height 1)  *)
(*      /   |   \                          |                                *)
(* (-4,1)   |   (4,1)  <--- ray GRAZES this vertex: A's parity count is       *)
(*      \   |   /            ambiguous here, miscounted as "inside" even     *)
(*       \  |  /              though p is on A's OUTWARD side (gtri A p < 0) *)
(*        \ | /                                                              *)
(*         \|/                                                               *)
(*        (0,0)                                                              *)
(*                                                                            *)
(* p sits genuinely inside B (left of the shared edge) but only APPEARS      *)
(* inside A (right of the shared edge) because its ray exits exactly through *)
(* A's far vertex instead of cleanly crossing or missing an edge.            *)
(* 3-axiom (classical-reals trio only). *)

Definition ttc_A : R * R * R * R * R * R := (0, 0, 4, 1, 0, 2).
Definition ttc_B : R * R * R * R * R * R := (0, 0, 0, 2, -4, 1).
Definition ttc_p : Point := mkPoint (-1) 1.

(* Both triangles are counter-clockwise. *)
Lemma ttc_A_ccw : 0 < gdbl 0 0 4 1 0 2.
Proof. unfold gdbl; lra. Qed.

Lemma ttc_B_ccw : 0 < gdbl 0 0 0 2 (-4) 1.
Proof. unfold gdbl; lra. Qed.

(* They touch on the shared edge (0,0)-(0,2): A's edge a3-a1 = B's edge b1-b2. *)
Lemma ttc_touch :
  triangles_touch_on_shared_edge
    (mkPoint 0 0) (mkPoint 4 1) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 0 2) (mkPoint (-4) 1).
Proof.
  right; right; right; right; right; right; left.
  split.
  - unfold shares_edge. right. split; reflexivity.
  - unfold opposite_sides, cross; cbn [px py]; lra.
Qed.

(* p is genuinely interior to B (0 < gtri) ... *)
Lemma ttc_gtri_B_pos : 0 < gtri 0 0 0 2 (-4) 1 ttc_p.
Proof.
  apply (proj2 (gtri_pos_iff 0 0 0 2 (-4) 1 ttc_p)).
  unfold gsA, gsB, gsC, ttc_p; cbn [px py]; repeat split; lra.
Qed.

(* ... but algebraically EXTERIOR to A (gtri < 0): the parity "inside" verdict
   for A is spurious. *)
Lemma ttc_gtri_A_neg : gtri 0 0 4 1 0 2 ttc_p < 0.
Proof.
  unfold gtri, ttc_p. eapply Rle_lt_trans; [ apply Rmin_r | ].
  unfold gsC; cbn [px py]; lra.
Qed.

(* p is in the parity point-set of A (spurious: ray grazes vertex (4,1)). *)
Lemma ttc_in_A : RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
                   (triangle_geometry 0 0 4 1 0 2) ttc_p.
Proof.
  unfold RelateCurveMatrix.in_stratum, point_set, triangle_geometry.
  exists (triangle_polygon 0 0 4 1 0 2). split; [ left; reflexivity | ].
  unfold point_in_polygon, triangle_polygon, outer_ring, hole_rings, triangle_ring.
  split; [ | intros h [] ].
  unfold point_in_ring, ttc_p. cbn.
  apply rpo_skip;
    [ intro H; unfold edge_crosses_ray in H; cbn in H;
      destruct H as [[[??]?]|[[??]?]]; lra | ].
  apply rpo_skip;
    [ intro H; unfold edge_crosses_ray in H; cbn in H;
      destruct H as [[[??]?]|[[??]?]]; lra | ].
  apply rpo_cross;
    [ unfold edge_crosses_ray; cbn; right; repeat split; lra | ].
  apply rpe_nil.
Qed.

(* p is in the parity point-set of B (genuine interior). *)
Lemma ttc_in_B : RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
                   (triangle_geometry 0 0 0 2 (-4) 1) ttc_p.
Proof.
  unfold RelateCurveMatrix.in_stratum, point_set, triangle_geometry.
  exists (triangle_polygon 0 0 0 2 (-4) 1). split; [ left; reflexivity | ].
  unfold point_in_polygon, triangle_polygon, outer_ring, hole_rings, triangle_ring.
  split; [ | intros h [] ].
  unfold point_in_ring, ttc_p. cbn.
  apply rpo_cross;
    [ unfold edge_crosses_ray; cbn; left; repeat split; lra | ].
  apply rpe_skip;
    [ intro H; unfold edge_crosses_ray in H; cbn in H;
      destruct H as [[[??]?]|[[??]?]]; lra | ].
  apply rpe_skip;
    [ intro H; unfold edge_crosses_ray in H; cbn in H;
      destruct H as [[[??]?]|[[??]?]]; lra | ].
  apply rpe_nil.
Qed.

(* HEADLINE (RED): the two CCW triangles touch on a shared edge, yet their
   SInt point-sets are NOT disjoint.  Hence the H_ii_disjoint premise of
   touch_triangle_pair_ii_cell (RelateNGTouchCells.v) is unsatisfiable for
   this pair, so no guard-free (unconditional) II-cell separation lemma can
   exist -- the ray-genericity guard in touch_triangle_pair_ii_cell_via_seam
   is ESSENTIAL. *)
Theorem touch_triangle_ii_separation_not_unconditional :
  triangles_touch_on_shared_edge
    (mkPoint 0 0) (mkPoint 4 1) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 0 2) (mkPoint (-4) 1)
  /\ 0 < gdbl 0 0 4 1 0 2
  /\ 0 < gdbl 0 0 0 2 (-4) 1
  /\ (exists p,
        RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
          (triangle_geometry 0 0 4 1 0 2) p /\
        RelateCurveMatrix.in_stratum RelateCurveMatrix.SInt
          (triangle_geometry 0 0 0 2 (-4) 1) p).
Proof.
  split; [ exact ttc_touch | ].
  split; [ exact ttc_A_ccw | ].
  split; [ exact ttc_B_ccw | ].
  exists ttc_p. split; [ exact ttc_in_A | exact ttc_in_B ].
Qed.

Print Assumptions touch_triangle_ii_separation_not_unconditional.
