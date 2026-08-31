(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchInside
   ----------------------------------------------------------------------------
   Leftover Ⅷ: A strictly inside B.

   Map: docs/scout/map-inside-cert.md. Compiled pair
   A = (1,1)(2,1)(1,2), B = (0,0)(4,0)(0,4) is the leftover-Ⅶ
   completeness residue. Both CCW. A sits strictly inside B.
   No shared vertex. `contains_b` misses (B-in-A). `overlap_b`
   misses (no B vertex in A). Detector `inside_b` is B CCW plus
   all three A vertices strictly interior to B — not a remint of
   `contains_b` / `aa_matrix_contains`. Constructor `TPR_Inside`
   stays on `im_unsupported` (load-bearing: do not emit
   `2FFFFFFF2`; that pin is #567). After leftover Ⅶ.
   False on leftover Ⅰ–Ⅶ regimes and the hard pairs (classifier
   order). Completeness stays false on an unnamed swapped nest
   pair (not leftover `Ⅹ`). #577 Green is
   completeness (QED) or a documented cex (QEX).
   `triangle_pair_regime_ccw_stop` is that disjunction, discharged
   QEX. Leftover `Ⅷ` itself is QED (`leftover_viii_qed_or_qex`).
   `classify_triangle_pair` arm is `True` — leftover Ⅰ honesty,
   not CONTEXT Bar 1. Nothing that mentions `TPR_Inside` may be
   proved through `classify_triangle_pair`. Do not steal 522-j /
   522-m / 522-f / 522-i / leftover Ⅰ–Ⅶ. Do not remint
   `contains_b` / `cone_separates_b` / `overlap_b`. Do not mint
   522-n / `Ⅹ`. Do not remint aa_matrix_*.

   WITNESS topic: relate · claimId: Ⅷ · witness: Ⅷ-inside-cex
   macro: relate
   lane: proofs
   issue: leftover Ⅷ / #522
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

Lemma leftover_I_no_inside :
  inside_b 0 0 2 0 0 1 1 0 3 0 2 1 = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 1 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 1 0 3 0 2 1 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma leftover_II_no_inside :
  inside_b 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 (-2) 0 1 (-1) (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma leftover_III_no_inside :
  inside_b 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1) = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 1 0 (1/2) (-1) (3/2) (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 1 0 (1/2) (-1) (3/2) (-1) (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma leftover_IV_no_inside :
  inside_b 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 1 0 (5/4) (1/4) (3/4) (1/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 1 0 (5/4) (1/4) (3/4) (1/4) (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma leftover_V_no_inside :
  inside_b 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 0 0 (-1) (-1) 3 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 (-1) (-1) 3 1 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma leftover_VI_no_inside :
  inside_b 0 0 2 0 0 2 0 0 3 1 1 3 = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 0 0 3 1 1 3)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 3 1 1 3 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma leftover_VII_no_inside :
  inside_b 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 2 (-1) 2 2 (-1) 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 2 (-1) 2 2 (-1) 2 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma hard_disjoint_no_inside :
  inside_b 0 0 1 0 0 1 2 0 3 0 2 1 = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 2 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 2 0 3 0 2 1 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma hard_touchvertex_no_inside :
  inside_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 0 (-2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 (-2) 0 0 (-2) (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma hard_touchedge_no_inside :
  inside_b 0 0 1 0 0 1 1 0 1 1 0 1 = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 1 0 1 1 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 1 0 1 1 0 1 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma hard_contains_no_inside :
  inside_b 0 0 1 0 0 1 (1/4) (1/4) (1/2) (1/4) (1/4) (1/2)
  = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl (1/4) (1/4) (1/2) (1/4) (1/4) (1/2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri (1/4) (1/4) (1/2) (1/4) (1/4) (1/2) (mkPoint 0 0)))
    as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma leftover_VIII_inside_true :
  inside_b 1 1 2 1 1 2 0 0 4 0 0 4 = true.
Proof.
  exact inside_b_true.
Qed.

Lemma classified_hard_pairs_no_inside :
  inside_b 0 0 1 0 0 1 2 0 3 0 2 1 = false /\
  inside_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = false /\
  inside_b 0 0 1 0 0 1 1 0 1 1 0 1 = false /\
  inside_b 0 0 1 0 0 1 (1/4) (1/4) (1/2) (1/4) (1/4) (1/2)
  = false.
Proof.
  split; [exact hard_disjoint_no_inside|].
  split; [exact hard_touchvertex_no_inside|].
  split; [exact hard_touchedge_no_inside|].
  exact hard_contains_no_inside.
Qed.

(* WITNESS {"claimId":"Ⅷ","topic":"relate","lemma":"triangle_pair_regime_inside","title":"TPR_Inside reachable on the compiled leftover-Ⅷ inside pair","file":"theories/RelateNGTouchInside.v","witness":"Ⅷ-inside-cex","board":"leftover-Ⅷ"} *)
Theorem triangle_pair_regime_inside :
  triangle_pair_regime 1 1 2 1 1 2 0 0 4 0 0 4 = TPR_Inside.
Proof.
  exact inside_pair_inside.
Qed.

Theorem triangle_pair_regime_inside_of :
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
    mixed_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    same_cone_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    lens_edges_cross_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    inside_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_Inside.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy
         He Hc Ho Hs Hv Hp Ho1 Hob Hm Hsc Hl Hi.
  unfold triangle_pair_regime.
  rewrite He, Hc, Ho, Hs, Hv, Hp, Ho1, Hob, Hm, Hsc, Hl, Hi. reflexivity.
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

Theorem leftover_V_still_mixedcone :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = TPR_MixedCone.
Proof.
  exact mixed_cone_pair_mixedcone.
Qed.

Theorem leftover_VI_still_samecone :
  triangle_pair_regime 0 0 2 0 0 2 0 0 3 1 1 3 = TPR_SameCone.
Proof.
  exact same_cone_pair_samecone.
Qed.

Theorem leftover_VII_still_lens :
  triangle_pair_regime 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = TPR_Lens.
Proof.
  exact lens_pair_lens.
Qed.

Theorem classified_hard_pairs_still_inside :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint /\
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap /\
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex /\
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  exact classified_hard_pairs.
Qed.

Theorem unnamed_ccw_still_unsupported :
  triangle_pair_regime 0 0 4 0 1 1 0 0 4 0 0 4 = TPR_Unsupported.
Proof.
  exact unnamed_ccw_pair_unsupported.
Qed.

(* Epic #522 / #577 stop: completeness (QED) or a documented CCW
   unsupported pair (QEX). Discharged QEX — unnamed same-side
   swapped nest pair, not leftover `Ⅹ`. Leftover-Ⅷ classify does
   not take the left. Not a 522-j remint. *)
(* WITNESS {"claimId":"Ⅷ","topic":"relate","lemma":"triangle_pair_regime_ccw_stop","title":"Epic #522 stop is completeness (QED) or a documented CCW unsupported pair (QEX); discharged QEX on an unnamed same-side shared-edge pair","file":"theories/RelateNGTouchInside.v","witness":"Ⅷ-inside-cex","board":"leftover-Ⅷ"} *)
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

(* Leftover Ⅷ Green: classify (QED) or remain the documented
   unsupported (QEX). This letter is QED. *)
Theorem leftover_viii_qed_or_qex :
  triangle_pair_regime 1 1 2 1 1 2 0 0 4 0 0 4 = TPR_Inside
  \/
  triangle_pair_regime 1 1 2 1 1 2 0 0 4 0 0 4 = TPR_Unsupported.
Proof.
  left.
  exact triangle_pair_regime_inside.
Qed.

Theorem inside_fill_still_unsupported :
  triangle_pair_fill TPR_Inside = im_unsupported.
Proof.
  exact triangle_pair_fill_touch_inside_eq.
Qed.

Print Assumptions triangle_pair_regime_inside.
Print Assumptions leftover_I_no_inside.
Print Assumptions leftover_II_no_inside.
Print Assumptions leftover_III_no_inside.
Print Assumptions leftover_IV_no_inside.
Print Assumptions leftover_V_no_inside.
Print Assumptions leftover_VI_no_inside.
Print Assumptions leftover_VII_no_inside.
Print Assumptions leftover_VIII_inside_true.
Print Assumptions classified_hard_pairs_no_inside.
Print Assumptions leftover_I_still_partial.
Print Assumptions leftover_II_still_obtuse.
Print Assumptions leftover_III_still_onesided.
Print Assumptions leftover_IV_still_onesided.
Print Assumptions leftover_V_still_mixedcone.
Print Assumptions leftover_VI_still_samecone.
Print Assumptions leftover_VII_still_lens.
Print Assumptions unnamed_ccw_still_unsupported.
Print Assumptions triangle_pair_regime_ccw_stop.
Print Assumptions triangle_pair_regime_ccw_stop_not_tjunction.
Print Assumptions leftover_viii_qed_or_qex.
Print Assumptions inside_fill_still_unsupported.
