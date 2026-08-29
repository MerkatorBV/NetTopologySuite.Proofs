(* ============================================================================
   NetTopologySuite.Proofs.RelateNGComplete
   ----------------------------------------------------------------------------
   Issue #577 / #522 claimId 522-j: leftover-decline finding.

   Ticket #577 asked either a completeness theorem (every nondegenerate
   CCW triangle pair answers a named regime) or a documented
   counterexample that becomes the next certificate's spec.  Completeness
   is FALSE: the compiled T-junction / partial-edge kiss
   `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)` is both-CCW and still emits
   `TPR_Unsupported`.  Obtuse-at-v is the other leftover family named
   in Core; it is not invented as a certificate here.

   Hard pairs that DO classify are cited, not re-proved: disjoint
   (#571), overlap (#570), vertex-touch (#572), shared-edge touch.

   Domain boundary: the three both-CCW certificates (`overlap_b`,
   `separated_b`, `touch_vertex_b`) are false when either orientation
   fails.  That is NOT "non-CCW ⇒ Unsupported" — `touch_edge_b` has no
   CCW guard, and `contains_b` guards only A.

   Five names are not a partition.  Do not invent a T-junction or
   obtuse-at-v certificate in this file.  Not an ADR-0004 remint.
   `522-j` is the existing #577 ticket id.

   WITNESS topic: relate · claimId: 522-j · witness: 522-j-sentinel-cex
   macro: relate
   lane: proofs
   issue: #577 / #522
   ADR-0004: not a remint. 522-j is the existing #577 ticket id.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

(* WITNESS {"claimId":"522-j","topic":"relate","lemma":"triangle_pair_regime_incomplete_tjunction","title":"Classifier completeness is false: a both-CCW T-junction still emits TPR_Unsupported","file":"theories/RelateNGComplete.v","witness":"522-j-sentinel-cex","board":"#577"} *)

From Stdlib Require Import Reals List Lia Lra Ranalysis Bool Btauto.
From NTS.Proofs Require Import Real.
From NTS.Proofs Require Import DE9IM Distance Overlay Segment RelateBoundary
  RelateLineLine RelateAreaPoint RelateAreaLine RelateAreaArea
  RelateMatrixLineLine RelateMatrixAreaLine RelateMatrixRect RelateMatrixTriangle
  RelateCurveMatrix RectangleJCT Intersect Orientation Convex Lattice Centroid.
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity
  RectangleSeparation.
From NTS.Proofs Require Import GeneralTriangleJCT GeneralTriangleExterior
  TriangleValidPolygon JCTSeamAssembly PointInRingCorrect PointInRingTangents
  JordanCurveSeam TriangleContainmentConvex.
From NTS.Proofs Require Import RelateNGCore RelateNGContains RelateNGOverlap
  RelateNGDisjoint RelateNGTouchVertex RelateNGTouch.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Compiled cex: T-junction / partial-edge kiss.                              *)
(*                                                                            *)
(* A = (0,0)(2,0)(0,1), B = (1,0)(3,0)(2,1).  Both gdbl = 2.  No shared      *)
(* vertex, no full shared edge, no separating edge.  The pin itself lives     *)
(* in RelateNGDisjoint (`tjunction_pair_unsupported`); this module records    *)
(* that the pair is inside the ticket's nondegenerate-CCW domain.             *)
(* -------------------------------------------------------------------------- *)

Lemma tjunction_pair_both_ccw :
  0 < gdbl 0 0 2 0 0 1 /\ 0 < gdbl 1 0 3 0 2 1.
Proof. unfold gdbl; split; lra. Qed.

(* WITNESS topic: relate · claimId: 522-j · witness: 522-j-sentinel-cex *)
(* WITNESS {"claimId":"522-j","topic":"relate","lemma":"triangle_pair_regime_incomplete_tjunction","title":"Classifier completeness is false: a both-CCW T-junction still emits TPR_Unsupported","file":"theories/RelateNGComplete.v","witness":"522-j-sentinel-cex","board":"#577"} *)
Theorem triangle_pair_regime_incomplete_tjunction :
  0 < gdbl 0 0 2 0 0 1 /\
  0 < gdbl 1 0 3 0 2 1 /\
  triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_Unsupported.
Proof.
  split; [unfold gdbl; lra|].
  split; [unfold gdbl; lra|].
  exact tjunction_pair_unsupported.
Qed.

Theorem triangle_pair_regime_ccw_incomplete :
  exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
    0 < gdbl ax ay bx by_ cx cy /\
    0 < gdbl dx dy ex ey fx fy /\
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_Unsupported.
Proof.
  exists 0, 0, 2, 0, 0, 1, 1, 0, 3, 0, 2, 1.
  exact triangle_pair_regime_incomplete_tjunction.
Qed.

(* -------------------------------------------------------------------------- *)
(* Hard-pair family that does classify.  Cite existing, do not re-prove.      *)
(* -------------------------------------------------------------------------- *)

Lemma classified_disjoint_pair :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint.
Proof.
  exact (triangle_pair_regime_disjoint 0 0 1 0 0 1 2 0 3 0 2 1
           dispatch_pair_separated_b).
Qed.

Lemma classified_overlap_pair :
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap.
Proof.
  exact (triangle_pair_regime_overlap 0 0 1 0 0 1
           (1/4) (1/4) (5/4) (1/4) (1/4) (5/4) overlap_ex_overlap_b).
Qed.

Lemma classified_touchvertex_pair :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex.
Proof.
  exact (triangle_pair_regime_touchvertex 0 0 2 0 0 2
           0 0 (-2) 0 0 (-2) touchvertex_ex_touch_vertex_b).
Qed.

Lemma classified_touch_pair :
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  exact (triangle_pair_regime_touch 0 0 1 0 0 1 1 0 1 1 0 1
           ex_triangles_touch_on_shared_edge).
Qed.

Lemma classified_hard_pairs :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint /\
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap /\
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex /\
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  split; [exact classified_disjoint_pair|].
  split; [exact classified_overlap_pair|].
  split; [exact classified_touchvertex_pair|].
  exact classified_touch_pair.
Qed.

(* -------------------------------------------------------------------------- *)
(* Domain boundary.  The three both-CCW certificates refuse a non-CCW         *)
(* argument.  This is NOT "non-CCW ⇒ Unsupported": `touch_edge_b` has no      *)
(* orientation guard, and `contains_b` guards only A.                         *)
(* -------------------------------------------------------------------------- *)

Lemma overlap_b_false_of_non_ccw :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold overlap_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [| reflexivity ].
  exfalso. destruct H as [Hn | Hn]; apply Hn; assumption.
Qed.

Lemma separated_b_false_of_non_ccw :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [| reflexivity ].
  exfalso. destruct H as [Hn | Hn]; apply Hn; assumption.
Qed.

Lemma touch_vertex_b_false_of_non_ccw :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold touch_vertex_b.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [| reflexivity ].
  exfalso. destruct H as [Hn | Hn]; apply Hn; assumption.
Qed.

Lemma non_ccw_pair_no_overlap_disjoint_vertex :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    ~ (0 < gdbl ax ay bx by_ cx cy)
    \/ ~ (0 < gdbl dx dy ex ey fx fy) ->
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = false /\
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = false /\
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  split; [exact (overlap_b_false_of_non_ccw _ _ _ _ _ _ _ _ _ _ _ _ H)|].
  split; [exact (separated_b_false_of_non_ccw _ _ _ _ _ _ _ _ _ _ _ _ H)|].
  exact (touch_vertex_b_false_of_non_ccw _ _ _ _ _ _ _ _ _ _ _ _ H).
Qed.

(* Next certificate specs (not invented here): T-junction / partial-edge
   kiss, and obtuse-at-v.  Five names remain not a partition. *)

Print Assumptions triangle_pair_regime_incomplete_tjunction.
Print Assumptions triangle_pair_regime_ccw_incomplete.
Print Assumptions classified_hard_pairs.
Print Assumptions non_ccw_pair_no_overlap_disjoint_vertex.
