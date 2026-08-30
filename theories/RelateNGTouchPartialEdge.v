(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchPartialEdge
   ----------------------------------------------------------------------------
   Leftover Ⅰ: T-junction / partial-edge kiss at relate bar 1.

   Map: docs/scout/map-tjunction-cert.md. Compiled pair
   A = (0,0)(2,0)(0,1), B = (1,0)(3,0)(2,1). Detector
   `touch_partial_edge_b` is mutual vertex-in-open-edge (not a widening
   of `shares_edge_b`). Constructor `TPR_TouchPartialEdge` stays on
   `im_unsupported` until a fill is named. After `touch_edge_b`. False
   on `classified_hard_pairs`. Completeness stays false (obtuse / ⅠⅠ).
   Do not steal 522-j / 522-m / 522-f. Do not mint 522-n. Do not
   remint aa_matrix_*. Do not invent leftover ⅠⅠ.

   WITNESS topic: relate · claimId: Ⅰ · witness: Ⅰ-partial-edge-bar1
   macro: relate
   lane: proofs
   issue: leftover Ⅰ / #522
   ADR-0004: not a remint.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

From Stdlib Require Import Reals Lra Bool.
From NTS.Proofs Require Import Distance Orientation RelateMatrixTriangle
  RelateNGCore RelateNGDisjoint RelateNGComplete.
Local Open Scope R_scope.

Lemma hard_disjoint_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = false.
Proof.
  unfold touch_partial_edge_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_overlap_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4)) (mkPoint (1/4) (5/4))
  = false.
Proof.
  unfold touch_partial_edge_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchvertex_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 0 (-2)) = false.
Proof.
  unfold touch_partial_edge_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchedge_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 1 1) (mkPoint 0 1) = false.
Proof.
  unfold touch_partial_edge_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma obtuse_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1)) = false.
Proof.
  unfold touch_partial_edge_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma classified_hard_pairs_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = false /\
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4)) (mkPoint (1/4) (5/4))
  = false /\
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 0 (-2)) = false /\
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 1 1) (mkPoint 0 1) = false.
Proof.
  split; [exact hard_disjoint_no_partial_edge|].
  split; [exact hard_overlap_no_partial_edge|].
  split; [exact hard_touchvertex_no_partial_edge|].
  exact hard_touchedge_no_partial_edge.
Qed.

(* WITNESS {"claimId":"Ⅰ","topic":"relate","lemma":"triangle_pair_regime_touchpartial","title":"TPR_TouchPartialEdge reachable at relate bar 1 on the compiled leftover-Ⅰ kiss","file":"theories/RelateNGTouchPartialEdge.v","witness":"Ⅰ-partial-edge-bar1","board":"leftover-Ⅰ"} *)
Theorem triangle_pair_regime_touchpartial :
  triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_TouchPartialEdge.
Proof.
  exact tjunction_pair_touch_partial.
Qed.

Theorem triangle_pair_regime_touchpartial_of :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_edge_b (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = false ->
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    touch_partial_edge_b
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = true ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_TouchPartialEdge.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy He Hc Ho Hs Hv Hp.
  unfold triangle_pair_regime.
  rewrite He, Hc, Ho, Hs, Hv, Hp. reflexivity.
Qed.

Theorem classified_hard_pairs_still :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint /\
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap /\
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex /\
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  exact classified_hard_pairs.
Qed.

Theorem tjunction_fill_still_unsupported :
  triangle_pair_fill TPR_TouchPartialEdge = im_unsupported.
Proof.
  exact triangle_pair_fill_touch_partial_eq.
Qed.

Print Assumptions triangle_pair_regime_touchpartial.
Print Assumptions classified_hard_pairs_no_partial_edge.
Print Assumptions obtuse_no_partial_edge.
