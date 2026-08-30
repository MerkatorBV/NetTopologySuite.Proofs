(* ============================================================================
   NetTopologySuite.Proofs.RelateNGUnnamedCex
   ----------------------------------------------------------------------------
   Unnamed CCW completeness cex after leftover Ⅴ (not leftover `Ⅵ`).

   A = (0,0)(2,0)(0,2), B = (0,0)(3,1)(1,3). Shared origin. Both
   remaining B verts have side_dot > 0 vs nA = (2,2) — same cone,
   outside A. Lives here so RelateNGTouchVertexRegime.v stays under
   the 1234-line split gate and RelateNGComplete.v stays at the
   monolith floor. Do not mint leftover `Ⅵ`. Do not steal 522-j /
   522-m.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

From Stdlib Require Import Reals Lra Bool.
From NTS.Proofs Require Import DE9IM Distance Orientation RelateMatrixTriangle
  GeneralTriangleSeparation
  RelateNGCore RelateNGDisjoint RelateNGTouchVertex.
Local Open Scope R_scope.

Lemma unnamed_ccw_no_open_A :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = false.
Proof.
  unfold some_vertex_on_open_edges, vertex_on_open_edges.
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 2 0) (mkPoint 0 2) (mkPoint 0 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 0 2) (mkPoint 0 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 3 1)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 2 0) (mkPoint 0 2) (mkPoint 3 1)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 2) (mkPoint 0 0) (mkPoint 3 1)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 1 3)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 2 0) (mkPoint 0 2) (mkPoint 1 3)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 2) (mkPoint 0 0) (mkPoint 1 3)
             ltac:(unfold cross; cbn [px py]; lra)).
  reflexivity.
Qed.

Lemma unnamed_ccw_no_open_B :
  some_vertex_on_open_edges
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = false.
Proof.
  unfold some_vertex_on_open_edges, vertex_on_open_edges.
  rewrite (on_open_seg_b_false_of_nbetween_fst
             (mkPoint 0 0) (mkPoint 3 1) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 3 1) (mkPoint 1 3) (mkPoint 0 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_nbetween_snd
             (mkPoint 1 3) (mkPoint 0 0) (mkPoint 0 0)
             ltac:(cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint 3 1) (mkPoint 2 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 3 1) (mkPoint 1 3) (mkPoint 2 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 1 3) (mkPoint 0 0) (mkPoint 2 0)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 0 0) (mkPoint 3 1) (mkPoint 0 2)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 3 1) (mkPoint 1 3) (mkPoint 0 2)
             ltac:(unfold cross; cbn [px py]; lra)).
  rewrite (on_open_seg_b_false_of_ncross
             (mkPoint 1 3) (mkPoint 0 0) (mkPoint 0 2)
             ltac:(unfold cross; cbn [px py]; lra)).
  reflexivity.
Qed.

Lemma unnamed_ccw_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = false.
Proof.
  unfold some_edge_separates_b.
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
             (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 2 0) (mkPoint 0 2) (mkPoint 0 0)
             (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 0 2) (mkPoint 0 0) (mkPoint 2 0)
             (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  rewrite (edge_separates_b_false_l (mkPoint 3 1) (mkPoint 1 3) (mkPoint 0 0)
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  assert (E6 : edge_separates_b (mkPoint 1 3) (mkPoint 0 0) (mkPoint 3 1)
                 (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = false).
  { unfold edge_separates_b, opposite_sides_b, cross; cbn [px py].
    destruct (Rlt_dec (_ * _) 0) as [Hbad | _];
      [ exfalso; lra | reflexivity ]. }
  rewrite E6. reflexivity.
Qed.

Lemma unnamed_ccw_no_partial_edge :
  touch_partial_edge_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = false.
Proof.
  unfold touch_partial_edge_b.
  rewrite unnamed_ccw_no_open_A, unnamed_ccw_no_open_B.
  reflexivity.
Qed.

Lemma unnamed_ccw_no_onesided :
  touch_onesided_t_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = false.
Proof.
  unfold touch_onesided_t_b.
  rewrite unnamed_ccw_no_open_A, unnamed_ccw_no_open_B.
  reflexivity.
Qed.

Lemma unnamed_ccw_touch_obtuse_false :
  touch_obtuse_vertex_b 0 0 2 0 0 2 0 0 3 1 1 3 = false.
Proof.
  unfold touch_obtuse_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 3 1 1 3)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  unfold exactly_one_shared_from_a, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold touch_obtuse_from_v, others_fst, others_snd, is_vertex_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold closed_cone_separates_b, both_closed_pos_b, both_closed_neg_b,
         cone_separates_b, both_strict_pos_b, both_strict_neg_b,
         vec_sum_from, side_dot.
  cbn [px py].
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

Lemma unnamed_ccw_mixed_cone_false :
  mixed_cone_vertex_b 0 0 2 0 0 2 0 0 3 1 1 3 = false.
Proof.
  unfold mixed_cone_vertex_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 3 1 1 3)) as [_ | Hn];
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

Lemma unnamed_ccw_pair_unsupported :
  triangle_pair_regime 0 0 2 0 0 2 0 0 3 1 1 3 = TPR_Unsupported.
Proof.
  unfold triangle_pair_regime, touch_edge_b, shares_edge_b, point_eqb.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  unfold contains_b.
  assert (Hcb : gtri 0 0 2 0 0 2 (mkPoint 0 0) <= 0).
  { unfold gtri.
    assert (H : gsA 0 0 2 0 (mkPoint 0 0) = 0) by (unfold gsA; simpl; ring).
    rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ]. }
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [Hlt | _];
    [ exfalso; lra | ].
  unfold overlap_b, some_vertex_strict_pos, gtri_strict_pos_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 3 1 1 3)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [H1 | _];
    [ exfalso; lra | ].
  assert (H20 : gtri 0 0 2 0 0 2 (mkPoint 3 1) < 0).
  { eapply Rle_lt_trans; [ apply (gtri_le_gsB 0 0 2 0 0 2 (mkPoint 3 1)) | ].
    unfold gsB; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 3 1))) as [H2 | _];
    [ exfalso; lra | ].
  assert (H1n : gtri 0 0 2 0 0 2 (mkPoint 1 3) < 0).
  { eapply Rle_lt_trans; [ apply (gtri_le_gsB 0 0 2 0 0 2 (mkPoint 1 3)) | ].
    unfold gsB; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 1 3))) as [H3 | _];
    [ exfalso; lra | ].
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 3 1 1 3)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  rewrite unnamed_ccw_no_separator.
  unfold touch_vertex_b, exactly_one_shared_from_a, is_vertex_b, point_eqb.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 3 1 1 3)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  assert (HA2 : touch_vertex_from_v
            (mkPoint 2 0)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = false).
  { unfold touch_vertex_from_v.
    rewrite (is_vertex_b_false_of_none
               (mkPoint 2 0)
               (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)).
    - rewrite andb_false_r, andb_false_l. reflexivity.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_px; lra. }
  assert (HA3 : touch_vertex_from_v
            (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = false).
  { unfold touch_vertex_from_v.
    rewrite (is_vertex_b_false_of_none
               (mkPoint 0 2)
               (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3)).
    - rewrite andb_false_r, andb_false_l. reflexivity.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra. }
  assert (HA1 : touch_vertex_from_v
            (mkPoint 0 0)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint 3 1) (mkPoint 1 3) = false).
  { unfold touch_vertex_from_v, others_fst, others_snd, cone_separates_b,
           both_strict_pos_b, both_strict_neg_b, vec_sum_from, side_dot.
    rewrite (point_eqb_complete (mkPoint 0 0) (mkPoint 0 0) eq_refl).
    cbn [px py].
    repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
    reflexivity. }
  rewrite HA1, HA2, HA3.
  rewrite !orb_false_r, andb_false_r.
  rewrite unnamed_ccw_no_partial_edge.
  rewrite unnamed_ccw_no_onesided.
  rewrite unnamed_ccw_touch_obtuse_false.
  rewrite unnamed_ccw_mixed_cone_false.
  reflexivity.
Qed.
