(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchOnesided
   ----------------------------------------------------------------------------
   Leftover Ⅲ: one-sided vertex-in-open-edge detector.

   Map: docs/scout/map-522-leftovers.md. Compiled pair
   A = (0,0)(2,0)(0,1), B = (1,0)(1/2,-1)(3/2,-1) is an exterior-side
   stem (II empty, BB dim 0). Detector `touch_onesided_t_b` is the
   exclusive-or of the two `some_vertex_on_open_edges` directions
   (not a widening of leftover Ⅰ's mutual `touch_partial_edge_b`).
   Constructor `TPR_TouchOnesided` stays on `im_unsupported`
   (load-bearing; do not remint to a Touches fill). After leftover Ⅰ
   and after `touch_vertex_b`. True on leftover Ⅲ; false on leftover
   Ⅰ (mutual), leftover Ⅱ, `classified_hard_pairs`, and the #567
   contains pair. Completeness stays false (obtuse / Ⅱ).
   `classify_triangle_pair` arm is `True` — leftover Ⅰ honesty, not
   CONTEXT Bar 1. The xor also fires on leftover Ⅳ (interior-side
   stem; named only). Do not steal 522-j / 522-m / 522-f / leftover Ⅰ.
   Do not invent leftover Ⅱ. Do not compile leftover Ⅳ. Do not
   mint 522-n / Ⅴ. Do not remint aa_matrix_*.

   WITNESS topic: relate · claimId: Ⅲ · witness: Ⅲ-onesided-t-detector
   macro: relate
   lane: proofs
   issue: leftover Ⅲ / #522
   ADR-0004: leftover numerals stay off the 522-* board catalog
   (not a partial mint). JSON blob on the headline is the leftover
   tag. Not requesting mutation pins this letter.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

From Stdlib Require Import Reals Lra Bool.
From NTS.Proofs Require Import DE9IM Distance Orientation RelateMatrixTriangle
  RelateNGCore RelateNGDisjoint RelateNGComplete.
Local Open Scope R_scope.

Lemma andb_true_xorb_false : forall a b : bool,
  a && b = true -> xorb a b = false.
Proof.
  intros a b H. destruct a, b; simpl in *; try discriminate; reflexivity.
Qed.

Lemma leftover_I_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 3 0) (mkPoint 2 1) = false.
Proof.
  unfold touch_onesided_t_b.
  apply andb_true_xorb_false.
  exact tjunction_touch_partial_edge_b.
Qed.

Lemma leftover_III_onesided_true :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint (1/2) (-1)) (mkPoint (3/2) (-1)) = true.
Proof.
  exact onesided_t_onesided_true.
Qed.

Lemma hard_disjoint_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = false.
Proof.
  unfold touch_onesided_t_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_overlap_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4)) (mkPoint (1/4) (5/4))
  = false.
Proof.
  unfold touch_onesided_t_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchvertex_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 0 (-2)) = false.
Proof.
  unfold touch_onesided_t_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchedge_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 1 1) (mkPoint 0 1) = false.
Proof.
  unfold touch_onesided_t_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_contains_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint (1/4) (1/4)) (mkPoint (1/2) (1/4)) (mkPoint (1/4) (1/2))
  = false.
Proof.
  unfold touch_onesided_t_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma obtuse_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1)) = false.
Proof.
  unfold touch_onesided_t_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma classified_hard_pairs_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 2 0) (mkPoint 3 0) (mkPoint 2 1) = false /\
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint (1/4) (1/4)) (mkPoint (5/4) (1/4)) (mkPoint (1/4) (5/4))
  = false /\
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 0 (-2)) = false /\
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 1 1) (mkPoint 0 1) = false /\
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint (1/4) (1/4)) (mkPoint (1/2) (1/4)) (mkPoint (1/4) (1/2))
  = false.
Proof.
  split; [exact hard_disjoint_no_onesided|].
  split; [exact hard_overlap_no_onesided|].
  split; [exact hard_touchvertex_no_onesided|].
  split; [exact hard_touchedge_no_onesided|].
  exact hard_contains_no_onesided.
Qed.

(* WITNESS {"claimId":"Ⅲ","topic":"relate","lemma":"triangle_pair_regime_onesided","title":"TPR_TouchOnesided reachable on the compiled leftover-Ⅲ exterior-side stem","file":"theories/RelateNGTouchOnesided.v","witness":"Ⅲ-onesided-t-detector","board":"leftover-Ⅲ"} *)
Theorem triangle_pair_regime_onesided :
  triangle_pair_regime 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1)
    = TPR_TouchOnesided.
Proof.
  exact onesided_t_pair_onesided.
Qed.

Theorem triangle_pair_regime_onesided_of :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_edge_b (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                 (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = false ->
    contains_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    overlap_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    separated_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    touch_partial_edge_b
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = false ->
    touch_onesided_t_b
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = true ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_TouchOnesided.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy He Hc Ho Hs Hv Hp Ho1.
  unfold triangle_pair_regime.
  rewrite He, Hc, Ho, Hs, Hv, Hp, Ho1. reflexivity.
Qed.

Theorem leftover_I_still_partial :
  triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_TouchPartialEdge.
Proof.
  exact tjunction_pair_touch_partial.
Qed.

Theorem classified_hard_pairs_still_onesided :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint /\
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap /\
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex /\
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  exact classified_hard_pairs.
Qed.

Theorem onesided_fill_still_unsupported :
  triangle_pair_fill TPR_TouchOnesided = im_unsupported.
Proof.
  exact triangle_pair_fill_touch_onesided_eq.
Qed.

Print Assumptions triangle_pair_regime_onesided.
Print Assumptions leftover_I_no_onesided.
Print Assumptions leftover_III_onesided_true.
Print Assumptions classified_hard_pairs_no_onesided.
Print Assumptions obtuse_no_onesided.
Print Assumptions hard_contains_no_onesided.
Print Assumptions leftover_I_still_partial.
Print Assumptions onesided_fill_still_unsupported.
