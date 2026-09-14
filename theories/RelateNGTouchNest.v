(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchNest
   ----------------------------------------------------------------------------
   Leftover Ⅸ: name the leftover-Ⅷ same-side shared-edge nest.

   Accept as leftover-Ⅸ inhabitance. Reject as a touch_edge /
   contains / overlap remint or a soundness theorem. Constructor
   is “escaped every prior arm, then a shared edge plus a B
   vertex strictly interior to A,” not “this is contains /
   interiors meet.” `triangle_pair_regime_nest` is inhabitance,
   not soundness. `classify_triangle_pair`'s TPR_Nest arm is
   True — no denotation. There is no TPR_Nest ⇒ interiors meet.

   Compiled pair A = (0,0)(4,0)(0,4), B = (0,0)(4,0)(1,1). Both
   CCW. Shared full edge; thirds same side so `touch_edge_b`
   misses; B's third vertex strictly inside A. `contains_b`
   misses (B verts on A's boundary). `overlap_b` misses (no B
   vertex strictly exterior). Detector `nest_b` is both CCW plus
   some shared edge plus some B vertex strictly interior to A —
   not a remint of `touch_edge_b` / `contains_b` / `overlap_b` /
   `inside_b`. Constructor `TPR_Nest` stays on `im_unsupported`
   (load-bearing: do not emit `2FFFFFFF2` or `FF2F11212`). After
   leftover Ⅷ. False on leftover Ⅰ–Ⅷ regimes and the hard
   pairs (classifier order). Completeness stays false on an
   unnamed swap nest (not leftover `Ⅹ`). Relocating
   `triangle_pair_regime_ccw_stop` here does not move #522
   closer to QED — one more named bucket.
   `leftover_ix_qed_or_qex` is classified ∨ declined on the
   pair just classified. `classified_hard_pairs_still_nest` is
   misnamed: those pairs stay Disjoint / Overlap / TouchVertex /
   TouchEdge. `classify_triangle_pair` arm is `True` — leftover
   Ⅰ honesty, not CONTEXT Bar 1. Do not steal 522-j / 522-m /
   522-f / 522-i / leftover Ⅰ–Ⅷ. Do not remint `touch_edge_b`
   / `contains_b` / `overlap_b` / `inside_b`. Do not mint 522-n
   / leftover `Ⅹ`. Do not remint leftover `Ⅵ` / leftover `Ⅶ`
   / leftover `Ⅷ`. Do not remint aa_matrix_*.

   WITNESS topic: relate · claimId: Ⅸ · witness: Ⅸ-nest-cex
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

Lemma leftover_I_no_nest :
  nest_b 0 0 2 0 0 1 1 0 3 0 2 1 = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_II_no_nest :
  nest_b 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint (-2) 0))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 1 (-1)))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  rewrite !orb_false_r, andb_false_r.
  reflexivity.
Qed.

Lemma leftover_III_no_nest :
  nest_b 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1) = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (1/2) (-1) (3/2) (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_IV_no_nest :
  nest_b 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (5/4) (1/4) (3/4) (1/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_V_no_nest :
  nest_b 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-1) (-1) 3 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint (-1) (-1)))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 3 1))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  rewrite !orb_false_r, andb_false_r.
  reflexivity.
Qed.

Lemma leftover_VI_no_nest :
  nest_b 0 0 2 0 0 2 0 0 3 1 1 3 = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 3 1 1 3)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 3 1))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 1 3))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  rewrite !orb_false_r, andb_false_r.
  reflexivity.
Qed.

Lemma leftover_VII_no_nest :
  nest_b 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 3 0 0 3)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 2 (-1) 2 2 (-1) 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_VIII_no_nest :
  nest_b 1 1 2 1 1 2 0 0 4 0 0 4 = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 1 1 2 1 1 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_IX_nest_true :
  nest_b 0 0 4 0 0 4 0 0 4 0 1 1 = true.
Proof.
  exact nest_b_true.
Qed.

Lemma hard_disjoint_no_nest :
  nest_b 0 0 1 0 0 1 2 0 3 0 2 1 = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 2 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma hard_touchvertex_no_nest :
  nest_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 0 (-2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint (-2) 0))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 (-2)))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  rewrite !orb_false_r, andb_false_r.
  reflexivity.
Qed.

Lemma hard_touchedge_no_nest :
  nest_b 0 0 1 0 0 1 1 0 1 1 0 1 = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 1 1 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint 1 0))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint 1 1))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  destruct (Rlt_dec 0 (gtri 0 0 1 0 0 1 (mkPoint 0 1))) as [Hlt | _];
    [ exfalso; leftover_ix_gtri_contra Hlt | ].
  rewrite !orb_false_r, andb_false_r.
  reflexivity.
Qed.

Lemma hard_contains_no_nest :
  nest_b 0 0 1 0 0 1 (1/4) (1/4) (1/2) (1/4) (1/4) (1/2)
  = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 1 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl (1/4) (1/4) (1/2) (1/4) (1/4) (1/2))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma classified_hard_pairs_no_nest :
  nest_b 0 0 1 0 0 1 2 0 3 0 2 1 = false /\
  nest_b 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = false /\
  nest_b 0 0 1 0 0 1 1 0 1 1 0 1 = false /\
  nest_b 0 0 1 0 0 1 (1/4) (1/4) (1/2) (1/4) (1/4) (1/2)
  = false.
Proof.
  split; [exact hard_disjoint_no_nest|].
  split; [exact hard_touchvertex_no_nest|].
  split; [exact hard_touchedge_no_nest|].
  exact hard_contains_no_nest.
Qed.

(* WITNESS {"claimId":"Ⅸ","topic":"relate","lemma":"triangle_pair_regime_nest","title":"TPR_Nest inhabitance on the compiled leftover-Ⅸ nest pair (not a touch_edge/contains denotation)","file":"theories/RelateNGTouchNest.v","witness":"Ⅸ-nest-cex","board":"leftover-Ⅸ"} *)
Theorem triangle_pair_regime_nest :
  triangle_pair_regime 0 0 4 0 0 4 0 0 4 0 1 1 = TPR_Nest.
Proof.
  exact nest_pair_nest.
Qed.

Theorem triangle_pair_regime_nest_of :
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
    inside_b ax ay bx by_ cx cy dx dy ex ey fx fy = false ->
    nest_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_Nest.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy
         He Hc Ho Hs Hv Hp Ho1 Hob Hm Hsc Hl Hi Hn.
  unfold triangle_pair_regime.
  rewrite He, Hc, Ho, Hs, Hv, Hp, Ho1, Hob, Hm, Hsc, Hl, Hi, Hn.
  reflexivity.
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

Theorem leftover_VIII_still_inside :
  triangle_pair_regime 1 1 2 1 1 2 0 0 4 0 0 4 = TPR_Inside.
Proof.
  exact inside_pair_inside.
Qed.

(* Misnamed: leftover Ⅰ / #570 / #572 / #567 still Disjoint /
   Overlap / TouchVertex / TouchEdge. Not a TPR_Nest claim. *)
Theorem classified_hard_pairs_still_nest :
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
   unsupported pair (QEX). Discharged QEX — unnamed swap nest,
   not leftover `Ⅹ`. Leftover-Ⅸ inhabitance does not take the
   left. Not a 522-j remint. *)
(* WITNESS {"claimId":"Ⅸ","topic":"relate","lemma":"triangle_pair_regime_ccw_stop","title":"Epic #522 stop is completeness (QED) or a documented CCW unsupported pair (QEX); discharged QEX on an unnamed swap nest","file":"theories/RelateNGTouchNest.v","witness":"Ⅸ-nest-cex","board":"leftover-Ⅸ"} *)
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

(* Classified ∨ declined on the pair this letter just classified.
   One more named bucket. Does not move epic #522 closer to QED. *)
Theorem leftover_ix_qed_or_qex :
  triangle_pair_regime 0 0 4 0 0 4 0 0 4 0 1 1 = TPR_Nest
  \/
  triangle_pair_regime 0 0 4 0 0 4 0 0 4 0 1 1 = TPR_Unsupported.
Proof.
  left.
  exact triangle_pair_regime_nest.
Qed.

Theorem nest_fill_still_unsupported :
  triangle_pair_fill TPR_Nest = im_unsupported.
Proof.
  exact triangle_pair_fill_touch_nest_eq.
Qed.

Print Assumptions triangle_pair_regime_nest.
Print Assumptions leftover_I_no_nest.
Print Assumptions leftover_II_no_nest.
Print Assumptions leftover_III_no_nest.
Print Assumptions leftover_IV_no_nest.
Print Assumptions leftover_V_no_nest.
Print Assumptions leftover_VI_no_nest.
Print Assumptions leftover_VII_no_nest.
Print Assumptions leftover_VIII_no_nest.
Print Assumptions leftover_IX_nest_true.
Print Assumptions classified_hard_pairs_no_nest.
Print Assumptions leftover_I_still_partial.
Print Assumptions leftover_II_still_obtuse.
Print Assumptions leftover_III_still_onesided.
Print Assumptions leftover_IV_still_onesided.
Print Assumptions leftover_V_still_mixedcone.
Print Assumptions leftover_VI_still_samecone.
Print Assumptions leftover_VII_still_lens.
Print Assumptions leftover_VIII_still_inside.
Print Assumptions unnamed_ccw_still_unsupported.
Print Assumptions triangle_pair_regime_ccw_stop.
Print Assumptions triangle_pair_regime_ccw_stop_not_tjunction.
Print Assumptions leftover_ix_qed_or_qex.
Print Assumptions nest_fill_still_unsupported.
