(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchLens
   ----------------------------------------------------------------------------
   Leftover Ⅶ: proper edge-cross lens.

   Map: docs/scout/map-lens-cert.md. Compiled pair
   A = (0,0)(3,0)(0,3), B = (2,-1)(2,2)(-1,2) is the leftover-Ⅵ
   completeness residue. Both CCW. (1,1) is strictly in both
   interiors. No shared vertex. `overlap_b` misses (no vertex
   stab). A's hypotenuse x+y=3 crosses B's vertical x=2 at (2,1).
   Detector `lens_edges_cross_b` is a boolean proper-cross of some
   A-edge with some B-edge (`opposite_sides_b` both ways) — not a
   remint of the noding-lane Prop `segments_proper_cross`.
   Constructor `TPR_Lens` stays on `im_unsupported` (load-bearing:
   do not emit `2FFF1FFF2`; that pin is #570). After leftover Ⅵ.
   False on leftover Ⅰ–Ⅵ regimes and the hard pairs (classifier
   order). Completeness stays false on an unnamed inside pair
   (not leftover `Ⅷ`). #577 Green is completeness (QED) or a
   documented cex (QEX). `triangle_pair_regime_ccw_stop` is that
   disjunction, discharged QEX. Leftover `Ⅶ` itself is QED
   (`leftover_vii_qed_or_qex`). `classify_triangle_pair` arm is
   `True` — leftover Ⅰ honesty, not CONTEXT Bar 1. Nothing that
   mentions `TPR_Lens` may be proved through
   `classify_triangle_pair`. Do not steal 522-j / 522-m / 522-f /
   522-i / leftover Ⅰ–Ⅵ. Do not remint `cone_separates_b` /
   `overlap_b`. Do not mint 522-n / `Ⅷ`. Do not remint
   aa_matrix_*.

   WITNESS topic: relate · claimId: Ⅶ · witness: Ⅶ-lens-cex
   macro: relate
   lane: proofs
   issue: leftover Ⅶ / #522
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

Lemma leftover_II_no_lens :
  lens_edges_cross_b 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = false.
Proof.
  unfold lens_edges_cross_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_proper_cross_b, segments_proper_cross_b,
         opposite_sides_b, cross.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_III_no_lens :
  lens_edges_cross_b 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1) = false.
Proof.
  unfold lens_edges_cross_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (1/2) (-1) (3/2) (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_proper_cross_b, segments_proper_cross_b,
         opposite_sides_b, cross.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_IV_no_lens :
  lens_edges_cross_b 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) = false.
Proof.
  unfold lens_edges_cross_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (5/4) (1/4) (3/4) (1/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_proper_cross_b, segments_proper_cross_b,
         opposite_sides_b, cross.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_disjoint_no_lens :
  lens_edges_cross_b 0 0 1 0 0 1 2 0 3 0 2 1 = false.
Proof.
  unfold lens_edges_cross_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 2 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_proper_cross_b, segments_proper_cross_b,
         opposite_sides_b, cross.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchvertex_no_lens :
  lens_edges_cross_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = false.
Proof.
  unfold lens_edges_cross_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 0 (-2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_proper_cross_b, segments_proper_cross_b,
         opposite_sides_b, cross.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchedge_no_lens :
  lens_edges_cross_b 0 0 1 0 0 1 1 0 1 1 0 1 = false.
Proof.
  unfold lens_edges_cross_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 1 1 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_proper_cross_b, segments_proper_cross_b,
         opposite_sides_b, cross.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_contains_no_lens :
  lens_edges_cross_b 0 0 1 0 0 1 (1/4) (1/4) (1/2) (1/4) (1/4) (1/2)
  = false.
Proof.
  unfold lens_edges_cross_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl (1/4) (1/4) (1/2) (1/4) (1/4) (1/2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_proper_cross_b, segments_proper_cross_b,
         opposite_sides_b, cross.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_VII_lens_true :
  lens_edges_cross_b 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = true.
Proof.
  exact lens_edges_cross_b_true.
Qed.

Lemma classified_hard_pairs_no_lens :
  lens_edges_cross_b 0 0 1 0 0 1 2 0 3 0 2 1 = false /\
  lens_edges_cross_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = false /\
  lens_edges_cross_b 0 0 1 0 0 1 1 0 1 1 0 1 = false /\
  lens_edges_cross_b 0 0 1 0 0 1 (1/4) (1/4) (1/2) (1/4) (1/4) (1/2)
  = false.
Proof.
  split; [exact hard_disjoint_no_lens|].
  split; [exact hard_touchvertex_no_lens|].
  split; [exact hard_touchedge_no_lens|].
  exact hard_contains_no_lens.
Qed.

(* WITNESS {"claimId":"Ⅶ","topic":"relate","lemma":"triangle_pair_regime_lens","title":"TPR_Lens reachable on the compiled leftover-Ⅶ lens pair","file":"theories/RelateNGTouchLens.v","witness":"Ⅶ-lens-cex","board":"leftover-Ⅶ"} *)
Theorem triangle_pair_regime_lens :
  triangle_pair_regime 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = TPR_Lens.
Proof.
  exact lens_pair_lens.
Qed.

Theorem triangle_pair_regime_lens_of :
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
    lens_edges_cross_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_Lens.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy He Hc Ho Hs Hv Hp Ho1 Hob Hm Hsc Hl.
  unfold triangle_pair_regime.
  rewrite He, Hc, Ho, Hs, Hv, Hp, Ho1, Hob, Hm, Hsc, Hl. reflexivity.
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

Theorem classified_hard_pairs_still_lens :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint /\
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap /\
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex /\
  triangle_pair_regime 0 0 1 0 0 1 1 0 1 1 0 1 = TPR_TouchEdge.
Proof.
  exact classified_hard_pairs.
Qed.

Theorem unnamed_ccw_still_unsupported :
  triangle_pair_regime 1 1 2 1 1 2 0 0 4 0 0 4 = TPR_Unsupported.
Proof.
  exact unnamed_ccw_pair_unsupported.
Qed.

(* Epic #522 / #577 stop: completeness (QED) or a documented CCW
   unsupported pair (QEX). Discharged QEX — unnamed inside pair, not
   leftover `Ⅷ`. Leftover-Ⅶ classify does not take the left. Not a
   522-j remint. *)
(* WITNESS {"claimId":"Ⅶ","topic":"relate","lemma":"triangle_pair_regime_ccw_stop","title":"Epic #522 stop is completeness (QED) or a documented CCW unsupported pair (QEX); discharged QEX on an unnamed inside pair","file":"theories/RelateNGTouchLens.v","witness":"Ⅶ-lens-cex","board":"leftover-Ⅶ"} *)
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

(* Leftover Ⅶ Green: classify (QED) or remain the documented
   unsupported (QEX). This letter is QED. *)
Theorem leftover_vii_qed_or_qex :
  triangle_pair_regime 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = TPR_Lens
  \/
  triangle_pair_regime 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = TPR_Unsupported.
Proof.
  left.
  exact triangle_pair_regime_lens.
Qed.

Theorem lens_fill_still_unsupported :
  triangle_pair_fill TPR_Lens = im_unsupported.
Proof.
  exact triangle_pair_fill_touch_lens_eq.
Qed.

Print Assumptions triangle_pair_regime_lens.
Print Assumptions leftover_II_no_lens.
Print Assumptions leftover_III_no_lens.
Print Assumptions leftover_IV_no_lens.
Print Assumptions leftover_VII_lens_true.
Print Assumptions classified_hard_pairs_no_lens.
Print Assumptions leftover_I_still_partial.
Print Assumptions leftover_II_still_obtuse.
Print Assumptions leftover_III_still_onesided.
Print Assumptions leftover_IV_still_onesided.
Print Assumptions leftover_V_still_mixedcone.
Print Assumptions leftover_VI_still_samecone.
Print Assumptions unnamed_ccw_still_unsupported.
Print Assumptions triangle_pair_regime_ccw_stop.
Print Assumptions triangle_pair_regime_ccw_stop_not_tjunction.
Print Assumptions leftover_vii_qed_or_qex.
Print Assumptions lens_fill_still_unsupported.
