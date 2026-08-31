(* ============================================================================
   NetTopologySuite.Proofs.RelateNGNestCex
   ----------------------------------------------------------------------------
   Leftover Ⅸ nest pair plus leftover Ⅹ / 522-n swap nest
   and the unnamed identical-pair completeness cex after leftover
   Ⅹ (not leftover `Ⅺ`). Split out of RelateNGUnnamedCex.v so
   that file stays under the 1234-line split gate. UnnamedCex
   re-exports this module.

   Nest pair: A = (0,0)(4,0)(0,4), B = (0,0)(4,0)(1,1). Shared
   edge, same-side thirds; B's third vertex strictly inside A.
   Classifies TPR_Nest.

   Swap pair: A = (0,0)(4,0)(1,1), B = (0,0)(4,0)(0,4). Classifies
   TPR_SwapNest (leftover Ⅹ / 522-n). `nest_b` is B-in-A only.

   Live cex: A = B = (0,0)(4,0)(0,4). Identical CCW pair. Do not
   mint leftover `Ⅺ`. Do not steal 522-j / 522-m.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

From Stdlib Require Import Reals Lra Bool.
From NTS.Proofs Require Import Real.
From NTS.Proofs Require Import DE9IM Distance Orientation RelateMatrixTriangle
  GeneralTriangleSeparation
  RelateNGCore RelateNGDisjoint RelateNGTouchVertex.
Local Open Scope R_scope.

(* Kill [edge_separates_b] by leftover-Ⅵ E6 style: [lra] the first
   [Rlt_dec] that is not actually [< 0]. [false_l] only sees q1. *)
Ltac leftover_vii_sep_false :=
  unfold edge_separates_b, opposite_sides_b, cross; cbn [px py];
  first
    [ destruct (Rlt_dec (_ * _) 0) as [Hbad | _];
        [ exfalso; lra | reflexivity ]
    | destruct (Rlt_dec (_ * _) 0) as [_ | _];
        [ destruct (Rlt_dec (_ * _) 0) as [Hbad | _];
            [ exfalso; lra | reflexivity ]
        | reflexivity ]
    | destruct (Rlt_dec (_ * _) 0) as [_ | _];
        [ destruct (Rlt_dec (_ * _) 0) as [_ | _];
            [ destruct (Rlt_dec (_ * _) 0) as [Hbad | _];
                [ exfalso; lra | reflexivity ]
            | reflexivity ]
        | reflexivity ] ].

(* -------------------------------------------------------------------------- *)
(* Leftover Ⅸ nest. A = (0,0)(4,0)(0,4), B = (0,0)(4,0)(1,1).               *)
(* Shared edge; thirds same side; B's third vertex strictly inside A.        *)
(* -------------------------------------------------------------------------- *)

Lemma nest_b_true :
  nest_b 0 0 4 0 0 4 0 0 4 0 1 1 = true.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  assert (E : shares_edge_b (mkPoint 0 0) (mkPoint 4 0)
                            (mkPoint 0 0) (mkPoint 4 0) = true).
  { unfold shares_edge_b, point_eqb; cbn [px py].
    repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
    reflexivity. }
  unfold some_edges_share_b.
  rewrite E; simpl.
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 0))) as [H0 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H0; cbn [px py] in H0; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 4 0))) as [H4 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H4; cbn [px py] in H4; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 1 1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gtri, gsA, gsB, gsC; cbn [px py]; lra ].
  reflexivity.
Qed.

Lemma nest_ccw_no_open_A :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false.
Proof.
  unfold some_vertex_on_open_edges, vertex_on_open_edges.
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 4 0) (mkPoint 0 4) (mkPoint 0 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 0 4) (mkPoint 0 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 0 0) (mkPoint 4 0) (mkPoint 4 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 4 0) (mkPoint 0 4) (mkPoint 4 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 4) (mkPoint 0 0) (mkPoint 4 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 4 0) (mkPoint 0 4) (mkPoint 1 1)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 4) (mkPoint 0 0) (mkPoint 1 1)
             ltac:(unfold cross; cbn [px py]; lra)).
  reflexivity.
Qed.

Lemma nest_ccw_no_open_B :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false.
Proof.
  unfold some_vertex_on_open_edges, vertex_on_open_edges.
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 4 0) (mkPoint 1 1) (mkPoint 0 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 1 1) (mkPoint 0 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 0 0) (mkPoint 4 0) (mkPoint 4 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 4 0) (mkPoint 1 1) (mkPoint 4 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 1 1) (mkPoint 0 0) (mkPoint 4 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 4 0) (mkPoint 1 1) (mkPoint 0 4)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 1 1) (mkPoint 0 0) (mkPoint 0 4)
             ltac:(unfold cross; cbn [px py]; lra)).
  reflexivity.
Qed.

Lemma nest_ccw_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false.
Proof.
  unfold some_edge_separates_b.
  assert (E1 : edge_separates_b (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false)
    by leftover_vii_sep_false.
  rewrite E1.
  assert (E2 : edge_separates_b (mkPoint 4 0) (mkPoint 0 4) (mkPoint 0 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false)
    by leftover_vii_sep_false.
  rewrite E2.
  assert (E3 : edge_separates_b (mkPoint 0 4) (mkPoint 0 0) (mkPoint 4 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false)
    by leftover_vii_sep_false.
  rewrite E3.
  assert (E4 : edge_separates_b (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E4.
  assert (E5 : edge_separates_b (mkPoint 4 0) (mkPoint 1 1) (mkPoint 0 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E5.
  assert (E6 : edge_separates_b (mkPoint 1 1) (mkPoint 0 0) (mkPoint 4 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E6.
  reflexivity.
Qed.

Lemma nest_ccw_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false.
Proof.
  unfold touch_partial_edge_b.
  rewrite nest_ccw_no_open_A, nest_ccw_no_open_B.
  reflexivity.
Qed.

Lemma nest_ccw_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false.
Proof.
  unfold touch_onesided_t_b.
  rewrite nest_ccw_no_open_A, nest_ccw_no_open_B.
  reflexivity.
Qed.

Lemma nest_ccw_touch_obtuse_false :
  touch_obtuse_vertex_b 0 0 4 0 0 4 0 0 4 0 1 1 = false.
Proof.
  unfold touch_obtuse_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma nest_ccw_mixed_cone_false :
  mixed_cone_vertex_b 0 0 4 0 0 4 0 0 4 0 1 1 = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma nest_ccw_same_cone_false :
  same_cone_vertex_b 0 0 4 0 0 4 0 0 4 0 1 1 = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma nest_ccw_lens_false :
  lens_edges_cross_b 0 0 4 0 0 4 0 0 4 0 1 1 = false.
Proof.
  unfold lens_edges_cross_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_proper_cross_b, segments_proper_cross_b,
         opposite_sides_b, cross.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma nest_ccw_inside_false :
  inside_b 0 0 4 0 0 4 0 0 4 0 1 1 = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma nest_pair_nest :
  triangle_pair_regime 0 0 4 0 0 4 0 0 4 0 1 1 = TPR_Nest.
Proof.
  unfold triangle_pair_regime, touch_edge_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold contains_b.
  assert (Hcb : gtri 0 0 4 0 0 4 (mkPoint 0 0) <= 0).
  { eapply Rle_trans; [ apply (gtri_le_gsA 0 0 4 0 0 4 (mkPoint 0 0)) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; lra | ].
  unfold overlap_b, some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 0))) as [H1 | _];
    [ exfalso; lra | ].
  assert (H20 : gtri 0 0 4 0 0 4 (mkPoint 4 0) <= 0).
  { eapply Rle_trans; [ apply (gtri_le_gsA 0 0 4 0 0 4 (mkPoint 4 0)) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 4 0))) as [H2 | _];
    [ exfalso; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 1 1))) as [_ | H3];
    [ | exfalso; apply H3; unfold gtri, gsA, gsB, gsC; cbn [px py]; lra ].
  unfold some_vertex_strict_neg, gtri_strict_neg_b.
  destruct (Rlt_dec (gtri 0 0 4 0 0 4 (mkPoint 0 0)) 0) as [Hn0 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hn0; cbn [px py] in Hn0; lra | ].
  destruct (Rlt_dec (gtri 0 0 4 0 0 4 (mkPoint 4 0)) 0) as [Hn4 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hn4; cbn [px py] in Hn4; lra | ].
  destruct (Rlt_dec (gtri 0 0 4 0 0 4 (mkPoint 1 1)) 0) as [Hn1 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hn1; cbn [px py] in Hn1; lra | ].
  rewrite !orb_false_r, andb_false_r.
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  rewrite nest_ccw_no_separator.
  unfold touch_vertex_b, exactly_one_shared_from_a, is_vertex_b, point_eqb.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  rewrite nest_ccw_no_partial_edge.
  rewrite nest_ccw_no_onesided.
  rewrite nest_ccw_touch_obtuse_false.
  rewrite nest_ccw_mixed_cone_false.
  rewrite nest_ccw_same_cone_false.
  rewrite nest_ccw_lens_false.
  rewrite nest_ccw_inside_false.
  rewrite nest_b_true.
  reflexivity.
Qed.

(* WITNESS {"claimId":"Ⅸ","topic":"relate","lemma":"nest_pair_nest","title":"Leftover Ⅸ nest classifies as TPR_Nest","file":"theories/RelateNGNestCex.v","witness":"Ⅸ-nest-cex","board":"leftover-Ⅸ"} *)

Lemma nest_ccw_swap_nest_false :
  swap_nest_b 0 0 4 0 0 4 0 0 4 0 1 1 = false.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 0 0))) as [H0 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H0; cbn [px py] in H0; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 4 0))) as [H4 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H4; cbn [px py] in H4; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 0 4))) as [H1 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H1; cbn [px py] in H1; lra | ].
  rewrite !orb_false_r, andb_false_r.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Leftover Ⅹ / 522-n swap nest. A = (0,0)(4,0)(1,1), B = (0,0)(4,0)(0,4).  *)
(* -------------------------------------------------------------------------- *)

Lemma swap_ccw_no_open_A :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false.
Proof.
  exact nest_ccw_no_open_B.
Qed.

Lemma swap_ccw_no_open_B :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false.
Proof.
  exact nest_ccw_no_open_A.
Qed.

Lemma swap_ccw_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false.
Proof.
  unfold some_edge_separates_b.
  assert (E1 : edge_separates_b (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E1.
  assert (E2 : edge_separates_b (mkPoint 4 0) (mkPoint 1 1) (mkPoint 0 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E2.
  assert (E3 : edge_separates_b (mkPoint 1 1) (mkPoint 0 0) (mkPoint 4 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E3.
  assert (E4 : edge_separates_b (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false)
    by leftover_vii_sep_false.
  rewrite E4.
  assert (E5 : edge_separates_b (mkPoint 4 0) (mkPoint 0 4) (mkPoint 0 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false)
    by leftover_vii_sep_false.
  rewrite E5.
  assert (E6 : edge_separates_b (mkPoint 0 4) (mkPoint 0 0) (mkPoint 4 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1) = false)
    by leftover_vii_sep_false.
  rewrite E6.
  reflexivity.
Qed.

Lemma swap_ccw_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false.
Proof.
  unfold touch_partial_edge_b.
  rewrite swap_ccw_no_open_A, swap_ccw_no_open_B.
  reflexivity.
Qed.

Lemma swap_ccw_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 1 1)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false.
Proof.
  unfold touch_onesided_t_b.
  rewrite swap_ccw_no_open_A, swap_ccw_no_open_B.
  reflexivity.
Qed.

Lemma swap_ccw_touch_obtuse_false :
  touch_obtuse_vertex_b 0 0 4 0 1 1 0 0 4 0 0 4 = false.
Proof.
  unfold touch_obtuse_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma swap_ccw_mixed_cone_false :
  mixed_cone_vertex_b 0 0 4 0 1 1 0 0 4 0 0 4 = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma swap_ccw_same_cone_false :
  same_cone_vertex_b 0 0 4 0 1 1 0 0 4 0 0 4 = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma swap_ccw_lens_false :
  lens_edges_cross_b 0 0 4 0 1 1 0 0 4 0 0 4 = false.
Proof.
  unfold lens_edges_cross_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_proper_cross_b, segments_proper_cross_b,
         opposite_sides_b, cross.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma swap_ccw_inside_false :
  inside_b 0 0 4 0 1 1 0 0 4 0 0 4 = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma swap_ccw_nest_false :
  nest_b 0 0 4 0 1 1 0 0 4 0 0 4 = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 0 0))) as [H0 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H0; cbn [px py] in H0; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 4 0))) as [H4 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H4; cbn [px py] in H4; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 0 4))) as [H1 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H1; cbn [px py] in H1; lra | ].
  rewrite !orb_false_r, andb_false_r.
  reflexivity.
Qed.

Lemma swap_nest_b_true :
  swap_nest_b 0 0 4 0 1 1 0 0 4 0 0 4 = true.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  assert (E : shares_edge_b (mkPoint 0 0) (mkPoint 4 0)
                            (mkPoint 0 0) (mkPoint 4 0) = true).
  { unfold shares_edge_b, point_eqb; cbn [px py].
    repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
    reflexivity. }
  unfold some_edges_share_b.
  rewrite E; simpl.
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 0))) as [H0 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H0; cbn [px py] in H0; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 4 0))) as [H4 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H4; cbn [px py] in H4; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 1 1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gtri, gsA, gsB, gsC; cbn [px py]; lra ].
  reflexivity.
Qed.

Lemma swap_pair_swapnest :
  triangle_pair_regime 0 0 4 0 1 1 0 0 4 0 0 4 = TPR_SwapNest.
Proof.
  unfold triangle_pair_regime, touch_edge_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold contains_b.
  assert (Hcb : gtri 0 0 4 0 1 1 (mkPoint 0 0) <= 0).
  { eapply Rle_trans; [ apply (gtri_le_gsA 0 0 4 0 1 1 (mkPoint 0 0)) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; lra | ].
  unfold overlap_b, some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 0 0))) as [H1 | _];
    [ exfalso; lra | ].
  assert (H20 : gtri 0 0 4 0 1 1 (mkPoint 4 0) <= 0).
  { eapply Rle_trans; [ apply (gtri_le_gsA 0 0 4 0 1 1 (mkPoint 4 0)) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 4 0))) as [H2 | _];
    [ exfalso; lra | ].
  assert (H1n : gtri 0 0 4 0 1 1 (mkPoint 0 4) < 0).
  { eapply Rle_lt_trans; [ apply (gtri_le_gsA 0 0 4 0 1 1 (mkPoint 0 4)) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 4 0 1 1 (mkPoint 0 4))) as [H3 | _];
    [ exfalso; lra | ].
  rewrite !orb_false_r, andb_false_r.
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  rewrite swap_ccw_no_separator.
  unfold touch_vertex_b, exactly_one_shared_from_a, is_vertex_b, point_eqb.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 1 1)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  rewrite swap_ccw_no_partial_edge.
  rewrite swap_ccw_no_onesided.
  rewrite swap_ccw_touch_obtuse_false.
  rewrite swap_ccw_mixed_cone_false.
  rewrite swap_ccw_same_cone_false.
  rewrite swap_ccw_lens_false.
  rewrite swap_ccw_inside_false.
  rewrite swap_ccw_nest_false.
  rewrite swap_nest_b_true.
  reflexivity.
Qed.

(* WITNESS {"claimId":"522-n","topic":"relate","lemma":"swap_pair_swapnest","title":"Leftover Ⅹ / 522-n swap nest classifies as TPR_SwapNest","file":"theories/RelateNGNestCex.v","witness":"522-n-swap-cex","board":"leftover-Ⅹ"} *)

(* -------------------------------------------------------------------------- *)
(* Unnamed identical-pair completeness cex after leftover Ⅹ.                 *)
(* Not leftover `Ⅺ`. A = B = (0,0)(4,0)(0,4).                                *)
(* -------------------------------------------------------------------------- *)

Lemma identical_ccw_no_open :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false.
Proof.
  unfold some_vertex_on_open_edges, vertex_on_open_edges.
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 4 0) (mkPoint 0 4) (mkPoint 0 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 0 4) (mkPoint 0 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 0 0) (mkPoint 4 0) (mkPoint 4 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 4 0) (mkPoint 0 4) (mkPoint 4 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 4) (mkPoint 0 0) (mkPoint 4 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 4 0) (mkPoint 0 4) (mkPoint 0 4)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 0 4) (mkPoint 0 0) (mkPoint 0 4)
             ltac:(cbn [px py]; lra)).
  reflexivity.
Qed.

Lemma identical_ccw_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false.
Proof.
  unfold some_edge_separates_b.
  assert (E1 : edge_separates_b (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E1.
  assert (E2 : edge_separates_b (mkPoint 4 0) (mkPoint 0 4) (mkPoint 0 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E2.
  assert (E3 : edge_separates_b (mkPoint 0 4) (mkPoint 0 0) (mkPoint 4 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E3.
  assert (E4 : edge_separates_b (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E4.
  assert (E5 : edge_separates_b (mkPoint 4 0) (mkPoint 0 4) (mkPoint 0 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E5.
  assert (E6 : edge_separates_b (mkPoint 0 4) (mkPoint 0 0) (mkPoint 4 0)
                 (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false)
    by leftover_vii_sep_false.
  rewrite E6.
  reflexivity.
Qed.

Lemma identical_ccw_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false.
Proof.
  unfold touch_partial_edge_b.
  rewrite identical_ccw_no_open, identical_ccw_no_open.
  reflexivity.
Qed.

Lemma identical_ccw_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4)
    (mkPoint 0 0) (mkPoint 4 0) (mkPoint 0 4) = false.
Proof.
  unfold touch_onesided_t_b.
  rewrite identical_ccw_no_open, identical_ccw_no_open.
  reflexivity.
Qed.

Lemma identical_ccw_touch_obtuse_false :
  touch_obtuse_vertex_b 0 0 4 0 0 4 0 0 4 0 0 4 = false.
Proof.
  unfold touch_obtuse_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma identical_ccw_mixed_cone_false :
  mixed_cone_vertex_b 0 0 4 0 0 4 0 0 4 0 0 4 = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma identical_ccw_same_cone_false :
  same_cone_vertex_b 0 0 4 0 0 4 0 0 4 0 0 4 = false.
Proof.
  unfold same_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma identical_ccw_lens_false :
  lens_edges_cross_b 0 0 4 0 0 4 0 0 4 0 0 4 = false.
Proof.
  unfold lens_edges_cross_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_edges_proper_cross_b, segments_proper_cross_b,
         opposite_sides_b, cross.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma identical_ccw_inside_false :
  inside_b 0 0 4 0 0 4 0 0 4 0 0 4 = false.
Proof.
  unfold inside_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in Hlt; cbn [px py] in Hlt; lra | ].
  reflexivity.
Qed.

Lemma identical_ccw_nest_false :
  nest_b 0 0 4 0 0 4 0 0 4 0 0 4 = false.
Proof.
  unfold nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 0))) as [H0 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H0; cbn [px py] in H0; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 4 0))) as [H4 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H4; cbn [px py] in H4; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 4))) as [H1 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H1; cbn [px py] in H1; lra | ].
  rewrite !orb_false_r, andb_false_r.
  reflexivity.
Qed.

Lemma identical_ccw_swap_nest_false :
  swap_nest_b 0 0 4 0 0 4 0 0 4 0 0 4 = false.
Proof.
  unfold swap_nest_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 0))) as [H0 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H0; cbn [px py] in H0; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 4 0))) as [H4 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H4; cbn [px py] in H4; lra | ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 4))) as [H1 | _];
    [ exfalso; unfold gtri, gsA, gsB, gsC in H1; cbn [px py] in H1; lra | ].
  rewrite !orb_false_r, andb_false_r.
  reflexivity.
Qed.

Lemma unnamed_ccw_pair_unsupported :
  triangle_pair_regime 0 0 4 0 0 4 0 0 4 0 0 4 = TPR_Unsupported.
Proof.
  unfold triangle_pair_regime, touch_edge_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold contains_b.
  assert (Hcb : gtri 0 0 4 0 0 4 (mkPoint 0 0) <= 0).
  { eapply Rle_trans; [ apply (gtri_le_gsA 0 0 4 0 0 4 (mkPoint 0 0)) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; lra | ].
  unfold overlap_b, some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 0))) as [H1 | _];
    [ exfalso; lra | ].
  assert (H20 : gtri 0 0 4 0 0 4 (mkPoint 4 0) <= 0).
  { eapply Rle_trans; [ apply (gtri_le_gsA 0 0 4 0 0 4 (mkPoint 4 0)) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 4 0))) as [H2 | _];
    [ exfalso; lra | ].
  assert (H1n : gtri 0 0 4 0 0 4 (mkPoint 0 4) <= 0).
  { eapply Rle_trans; [ apply (gtri_le_gsA 0 0 4 0 0 4 (mkPoint 0 4)) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 4 0 0 4 (mkPoint 0 4))) as [H3 | _];
    [ exfalso; lra | ].
  rewrite !orb_false_r, andb_false_r.
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  rewrite identical_ccw_no_separator.
  unfold touch_vertex_b, exactly_one_shared_from_a, is_vertex_b, point_eqb.
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 4 0 0 4)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  rewrite identical_ccw_no_partial_edge.
  rewrite identical_ccw_no_onesided.
  rewrite identical_ccw_touch_obtuse_false.
  rewrite identical_ccw_mixed_cone_false.
  rewrite identical_ccw_same_cone_false.
  rewrite identical_ccw_lens_false.
  rewrite identical_ccw_inside_false.
  rewrite identical_ccw_nest_false.
  rewrite identical_ccw_swap_nest_false.
  reflexivity.
Qed.
