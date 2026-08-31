(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchSwapNest
   ----------------------------------------------------------------------------
   Leftover Ⅹ / 522-n: same-side shared-edge swap nest.

   Map: docs/scout/map-swap-nest-cert.md. Compiled pair
   A = (0,0)(4,0)(1,1), B = (0,0)(4,0)(0,4) is the leftover-Ⅸ
   completeness residue. Both CCW. Shared full edge; thirds same
   side; A's third vertex strictly inside B. `nest_b` misses
   (B-in-A only). `inside_b` misses (A verts on B's boundary).
   `contains_b` / `overlap_b` miss. Detector `swap_nest_b` is
   both CCW plus some shared edge plus some A vertex strictly
   interior to B — not a remint of `nest_b` / `inside_b` /
   `contains_b` / `touch_edge_b`. Constructor `TPR_SwapNest`
   stays on `im_unsupported` (load-bearing: do not emit
   `2FFFFFFF2` or `FF2F11212`). After leftover Ⅸ.
   False on leftover Ⅰ–Ⅸ regimes and the hard pairs (classifier
   order). Completeness stays false on an unnamed identical
   CCW pair (not leftover `Ⅺ`). #577 Green is
   completeness (QED) or a documented cex (QEX).
   `triangle_pair_regime_ccw_stop` is that disjunction, discharged
   QEX. Leftover `Ⅹ` itself is QED (`leftover_x_qed_or_qex`).
   `classify_triangle_pair` arm is `True` — leftover Ⅰ honesty,
   not CONTEXT Bar 1. Nothing that mentions `TPR_SwapNest` may be
   proved through `classify_triangle_pair`. Do not steal 522-j /
   522-m / 522-f / 522-i / leftover Ⅰ–Ⅸ. Do not remint
   `nest_b` / `inside_b` / `contains_b` / `touch_edge_b`. Do not
   mint leftover `Ⅺ`. Do not remint aa_matrix_*.

   WITNESS topic: relate · claimId: 522-n · witness: 522-n-swap-cex
   macro: relate
   lane: proofs
   issue: leftover Ⅹ / 522-n / #522
   ADR-0004: this letter mints board claimId 522-n as leftover
   `Ⅹ` (owner override). JSON blob on the headline is the leftover
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

Lemma leftover_I_no_swapnest :
  swap_nest_b 0 0 2 0 0 1 1 0 3 0 2 1 = false.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 3 0 2 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_II_no_swapnest :
  swap_nest_b 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = false.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_III_no_swapnest :
  swap_nest_b 0 0 2 0 0 1 1 0 (1/2) (-1) (3/2) (-1) = false.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (1/2) (-1) (3/2) (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_IV_no_swapnest :
  swap_nest_b 0 0 2 0 0 1 1 0 (5/4) (1/4) (3/4) (1/4) = false.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 1 0 (5/4) (1/4) (3/4) (1/4))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_V_no_swapnest :
  swap_nest_b 0 0 2 0 0 2 0 0 (-1) (-1) 3 1 = false.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-1) (-1) 3 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_VI_no_swapnest :
  swap_nest_b 0 0 2 0 0 2 0 0 3 1 1 3 = false.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 3 1 1 3)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_VII_no_swapnest :
  swap_nest_b 0 0 3 0 0 3 2 (-1) 2 2 (-1) 2 = false.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 3 0 0 3)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 2 (-1) 2 2 (-1) 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_VIII_no_swapnest :
  swap_nest_b 1 1 2 1 1 2 0 0 4 0 0 4 = false.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 1 1 2 1 1 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_share_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma leftover_IX_no_swapnest :
  swap_nest_b 0 0 4 0 0 4 0 0 4 0 1 1 = false.
Proof.
  exact nest_ccw_swap_nest_false.
Qed.

Lemma leftover_X_swapnest_true :
  swap_nest_b 0 0 4 0 1 1 0 0 4 0 0 4 = true.
Proof.
  exact swap_nest_b_true.
Qed.

(* WITNESS {"claimId":"522-n","topic":"relate","lemma":"triangle_pair_regime_swapnest","title":"TPR_SwapNest reachable on the compiled leftover-Ⅹ / 522-n swap nest pair","file":"theories/RelateNGTouchSwapNest.v","witness":"522-n-swap-cex","board":"leftover-Ⅹ"} *)
Theorem triangle_pair_regime_swapnest :
  triangle_pair_regime 0 0 4 0 1 1 0 0 4 0 0 4 = TPR_SwapNest.
Proof.
  exact swap_pair_swapnest.
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

Theorem leftover_IX_still_nest :
  triangle_pair_regime 0 0 4 0 0 4 0 0 4 0 1 1 = TPR_Nest.
Proof.
  exact nest_pair_nest.
Qed.

Theorem unnamed_ccw_still_unsupported :
  triangle_pair_regime 0 0 4 0 0 4 0 0 4 0 0 4 = TPR_Unsupported.
Proof.
  exact unnamed_ccw_pair_unsupported.
Qed.

(* Epic #522 / #577 stop: completeness (QED) or a documented CCW
   unsupported pair (QEX). Discharged QEX — unnamed identical
   pair, not leftover `Ⅺ`. Leftover-Ⅹ classify does
   not take the left. Not a 522-j remint. *)
(* WITNESS {"claimId":"522-n","topic":"relate","lemma":"triangle_pair_regime_ccw_stop","title":"Epic #522 stop is completeness (QED) or a documented CCW unsupported pair (QEX); discharged QEX on an unnamed identical CCW pair","file":"theories/RelateNGTouchSwapNest.v","witness":"522-n-swap-cex","board":"leftover-Ⅹ"} *)
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

Theorem leftover_x_qed_or_qex :
  triangle_pair_regime 0 0 4 0 1 1 0 0 4 0 0 4 = TPR_SwapNest
  \/
  triangle_pair_regime 0 0 4 0 1 1 0 0 4 0 0 4 = TPR_Unsupported.
Proof.
  left.
  exact triangle_pair_regime_swapnest.
Qed.

Theorem swapnest_fill_still_unsupported :
  triangle_pair_fill TPR_SwapNest = im_unsupported.
Proof.
  exact triangle_pair_fill_touch_swapnest_eq.
Qed.

Print Assumptions triangle_pair_regime_swapnest.
Print Assumptions leftover_I_no_swapnest.
Print Assumptions leftover_II_no_swapnest.
Print Assumptions leftover_III_no_swapnest.
Print Assumptions leftover_IV_no_swapnest.
Print Assumptions leftover_V_no_swapnest.
Print Assumptions leftover_VI_no_swapnest.
Print Assumptions leftover_VII_no_swapnest.
Print Assumptions leftover_VIII_no_swapnest.
Print Assumptions leftover_IX_no_swapnest.
Print Assumptions leftover_X_swapnest_true.
Print Assumptions leftover_I_still_partial.
Print Assumptions leftover_II_still_obtuse.
Print Assumptions leftover_III_still_onesided.
Print Assumptions leftover_IV_still_onesided.
Print Assumptions leftover_V_still_mixedcone.
Print Assumptions leftover_VI_still_samecone.
Print Assumptions leftover_VII_still_lens.
Print Assumptions leftover_VIII_still_inside.
Print Assumptions leftover_IX_still_nest.
Print Assumptions unnamed_ccw_still_unsupported.
Print Assumptions triangle_pair_regime_ccw_stop.
Print Assumptions triangle_pair_regime_ccw_stop_not_tjunction.
Print Assumptions leftover_x_qed_or_qex.
Print Assumptions swapnest_fill_still_unsupported.
