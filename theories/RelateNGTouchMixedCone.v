(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchMixedCone
   ----------------------------------------------------------------------------
   Leftover Ⅴ: opposite-sign cone at a shared vertex.

   Map: docs/scout/map-mixed-cone-cert.md. Compiled pair
   A = (0,0)(2,0)(0,2), B = (0,0)(-1,-1)(3,1) is the leftover-Ⅱ
   completeness residue. Shared origin. Cone normal nA = (2,2) puts
   B's remaining vertices on opposite sides (side_dot (−1,−1) = −4,
   side_dot (3,1) = 8). Sibling of leftover Ⅱ (same A; B third
   vertex (1,−1) is TPR_TouchObtuse, product 0) and of #572
   (B third vertex (0,−2) is TPR_TouchVertex, same-sign). Detector
   `mixed_cone_vertex_b` is opposite-sign `side_dot` plus
   `negb cone_separates_b` plus `negb closed_cone_separates_b` —
   not a remint of `cone_separates_b` / `touch_vertex_b` /
   `touch_obtuse_vertex_b`. Constructor `TPR_MixedCone` stays on
   `im_unsupported` (load-bearing: do not emit `FFFF1FFF2`; that
   pin is #572). After leftover Ⅱ. False on
   `classified_hard_pairs`, leftover Ⅰ, leftover Ⅱ, leftover Ⅲ,
   leftover Ⅳ, and the #567 contains pair. Completeness stays
   false on an unnamed CCW pair (not leftover `Ⅵ`).
   #577 Green is completeness (QED) or a documented cex (QEX).
   `triangle_pair_regime_ccw_stop` is that disjunction, discharged
   QEX. Leftover `Ⅴ` itself is QED (`leftover_v_qed_or_qex`).
   `classify_triangle_pair` arm is `True` — leftover Ⅰ honesty,
   not CONTEXT Bar 1. Nothing that mentions `TPR_MixedCone` may
   be proved through `classify_triangle_pair`. Do not steal 522-j /
   522-m / 522-f / 522-i / leftover Ⅰ / leftover Ⅱ. Do not remint
   `cone_separates_b`. Do not mint 522-n / `Ⅵ`. Do not remint
   aa_matrix_*.

   WITNESS topic: relate · claimId: Ⅴ · witness: Ⅴ-mixed-cone-cex
   macro: relate
   lane: proofs
   issue: leftover Ⅴ / #522
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
  GeneralTriangleSeparation
  RelateNGCore RelateNGDisjoint RelateNGTouchVertex RelateNGUnnamedCex
  RelateNGComplete.
Local Open Scope R_scope.

Lemma leftover_I_no_mixedcone :
  mixed_cone_vertex_b 0 0 2 0 0 1 1 0 3 0 2 1 = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_II_no_mixedcone :
  mixed_cone_vertex_b 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold mixed_cone_from_v, others_fst, others_snd, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold opposite_side_dot_b, closed_cone_separates_b,
         both_closed_pos_b, both_closed_neg_b,
         cone_separates_b, both_strict_pos_b, both_strict_neg_b,
         vec_sum_from, side_dot.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_III_no_mixedcone :
  mixed_cone_vertex_b 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1) = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (1/2) (-1) (3/2) (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_IV_no_mixedcone :
  mixed_cone_vertex_b 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (5/4) (1/4) (3/4) (1/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_disjoint_no_mixedcone :
  mixed_cone_vertex_b 0 0 1 0 0 1 2 0 3 0 2 1 = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 2 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_overlap_no_mixedcone :
  mixed_cone_vertex_b 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
  = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl (1/4) (1/4) (5/4) (1/4) (1/4) (5/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchvertex_no_mixedcone :
  mixed_cone_vertex_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 0 (-2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold mixed_cone_from_v, others_fst, others_snd, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold opposite_side_dot_b, closed_cone_separates_b,
         both_closed_pos_b, both_closed_neg_b,
         cone_separates_b, both_strict_pos_b, both_strict_neg_b,
         vec_sum_from, side_dot.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchedge_no_mixedcone :
  mixed_cone_vertex_b 0 0 1 0 0 1 1 0 1 1 0 1 = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 1 1 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_contains_no_mixedcone :
  mixed_cone_vertex_b 0 0 1 0 0 1 (1/4) (1/4) (1/2) (1/4) (1/4) (1/2)
  = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl (1/4) (1/4) (1/2) (1/4) (1/4) (1/2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_V_mixedcone_true :
  mixed_cone_vertex_b 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = true.
Proof.
  exact mixed_cone_vertex_b_true.
Qed.

Lemma classified_hard_pairs_no_mixedcone :
  mixed_cone_vertex_b 0 0 1 0 0 1 2 0 3 0 2 1 = false /\
  mixed_cone_vertex_b 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
  = false /\
  mixed_cone_vertex_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = false /\
  mixed_cone_vertex_b 0 0 1 0 0 1 1 0 1 1 0 1 = false /\
  mixed_cone_vertex_b 0 0 1 0 0 1 (1/4) (1/4) (1/2) (1/4) (1/4) (1/2)
  = false.
Proof.
  split; [exact hard_disjoint_no_mixedcone|].
  split; [exact hard_overlap_no_mixedcone|].
  split; [exact hard_touchvertex_no_mixedcone|].
  split; [exact hard_touchedge_no_mixedcone|].
  exact hard_contains_no_mixedcone.
Qed.

(* WITNESS {"claimId":"Ⅴ","topic":"relate","lemma":"triangle_pair_regime_mixedcone","title":"TPR_MixedCone reachable on the compiled leftover-Ⅴ mixed-cone pair","file":"theories/RelateNGTouchMixedCone.v","witness":"Ⅴ-mixed-cone-cex","board":"leftover-Ⅴ"} *)
Theorem triangle_pair_regime_mixedcone :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = TPR_MixedCone.
Proof.
  exact mixed_cone_pair_mixedcone.
Qed.

Theorem triangle_pair_regime_mixedcone_of :
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
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = false ->
    touch_obtuse_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    mixed_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_MixedCone.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy He Hc Ho Hs Hv Hp Ho1 Hob Hm.
  unfold triangle_pair_regime.
  rewrite He, Hc, Ho, Hs, Hv, Hp, Ho1, Hob, Hm. reflexivity.
Qed.

Theorem leftover_I_still_partial :
  triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_TouchPartialEdge.
Proof.
  exact tjunction_pair_touch_partial.
Qed.

Theorem leftover_II_still_obtuse :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = TPR_TouchObtuse.
Proof.
  exact obtuse_pair_touch_obtuse.
Qed.

Theorem leftover_III_still_onesided :
  triangle_pair_regime 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1)
    = TPR_TouchOnesided.
Proof.
  exact onesided_t_pair_onesided.
Qed.

Theorem leftover_IV_still_onesided :
  triangle_pair_regime 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4)
    = TPR_TouchOnesided.
Proof.
  exact interior_side_pair_onesided.
Qed.

Theorem classified_hard_pairs_still_mixedcone :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint /\
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap /\
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex /\
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  exact classified_hard_pairs.
Qed.

Theorem unnamed_ccw_still_unsupported :
  triangle_pair_regime 0 0 2 0 0 2 0 0 3 1 1 3 = TPR_Unsupported.
Proof.
  exact unnamed_ccw_pair_unsupported.
Qed.

(* Epic #522 / #577 stop: completeness (QED) or a documented CCW
   unsupported pair (QEX). Discharged QEX — unnamed, not leftover
   `Ⅵ`. Leftover-Ⅴ classify does not take the left. Not a 522-j
   remint. *)
(* WITNESS {"claimId":"Ⅴ","topic":"relate","lemma":"triangle_pair_regime_ccw_stop","title":"Epic #522 stop is completeness (QED) or a documented CCW unsupported pair (QEX); discharged QEX on an unnamed pair","file":"theories/RelateNGTouchMixedCone.v","witness":"Ⅴ-mixed-cone-cex","board":"leftover-Ⅴ"} *)
Theorem triangle_pair_regime_ccw_stop :
  (forall ax ay bx by_ cx cy dx dy ex ey fx fy : R,
     0 < gdbl ax ay bx by_ cx cy ->
     0 < gdbl dx dy ex ey fx fy ->
     triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
       <> TPR_Unsupported)
  \/
  (exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
     0 < gdbl ax ay bx by_ cx cy /\
     0 < gdbl dx dy ex ey fx fy /\
     triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
       = TPR_Unsupported).
Proof.
  right.
  exact triangle_pair_regime_ccw_incomplete.
Qed.

Theorem triangle_pair_regime_ccw_stop_not_tjunction :
  (forall ax ay bx by_ cx cy dx dy ex ey fx fy : R,
     0 < gdbl ax ay bx by_ cx cy ->
     0 < gdbl dx dy ex ey fx fy ->
     ~ tjunction_pair_coords ax ay bx by_ cx cy dx dy ex ey fx fy ->
     triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
       <> TPR_Unsupported)
  \/
  (exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
     0 < gdbl ax ay bx by_ cx cy /\
     0 < gdbl dx dy ex ey fx fy /\
     ~ tjunction_pair_coords ax ay bx by_ cx cy dx dy ex ey fx fy /\
     triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
       = TPR_Unsupported).
Proof.
  right.
  exact triangle_pair_regime_ccw_incomplete_not_tjunction.
Qed.

(* Leftover Ⅴ Green: classify (QED) or remain the documented
   unsupported (QEX). This letter is QED. *)
Theorem leftover_v_qed_or_qex :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = TPR_MixedCone
  \/
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = TPR_Unsupported.
Proof.
  left.
  exact triangle_pair_regime_mixedcone.
Qed.

Theorem mixedcone_fill_still_unsupported :
  triangle_pair_fill TPR_MixedCone = im_unsupported.
Proof.
  exact triangle_pair_fill_touch_mixed_eq.
Qed.

Print Assumptions triangle_pair_regime_mixedcone.
Print Assumptions leftover_I_no_mixedcone.
Print Assumptions leftover_II_no_mixedcone.
Print Assumptions leftover_III_no_mixedcone.
Print Assumptions leftover_IV_no_mixedcone.
Print Assumptions leftover_V_mixedcone_true.
Print Assumptions classified_hard_pairs_no_mixedcone.
Print Assumptions hard_touchvertex_no_mixedcone.
Print Assumptions hard_contains_no_mixedcone.
Print Assumptions leftover_I_still_partial.
Print Assumptions leftover_II_still_obtuse.
Print Assumptions leftover_III_still_onesided.
Print Assumptions leftover_IV_still_onesided.
Print Assumptions unnamed_ccw_still_unsupported.
Print Assumptions triangle_pair_regime_ccw_stop.
Print Assumptions triangle_pair_regime_ccw_stop_not_tjunction.
Print Assumptions leftover_v_qed_or_qex.
Print Assumptions mixedcone_fill_still_unsupported.
