(* ============================================================================
   NetTopologySuite.Proofs.RelateNGComplete
   ----------------------------------------------------------------------------
   Issue #577 / #522 claimId 522-j: leftover-decline finding.

   Ticket #577 asked either a completeness theorem (every nondegenerate
   CCW triangle pair answers a named regime) or a documented
   counterexample that becomes the next certificate's spec.  Completeness
   was FALSE on the compiled T-junction / partial-edge kiss
   `(0,0)(2,0)(0,1)` vs `(1,0)(3,0)(2,1)` (522-j). Leftover `Ⅰ`
   classifies that pair as `TPR_TouchPartialEdge`. Completeness is
   still FALSE: obtuse-at-v (leftover `ⅠⅠ`, 522-m) still emits
   `TPR_Unsupported`.  Do not invent the obtuse certificate here.

   Hard pairs that DO classify are cited, not re-proved.  Catalog
   ids, not the older witness-issue shorthand: disjoint is #571 /
   522-c (the #530 sentinel pair); overlap is #570 / 522-b (the
   #567 overlap pair); vertex-touch is #572 / 522-i; shared-edge
   touch is the existing `TPR_TouchEdge` pin, not a #522 subtask.

   Domain boundary: the three both-CCW certificates (`overlap_b`,
   `separated_b`, `touch_vertex_b`) are false when either orientation
   fails.  That is NOT "non-CCW ⇒ Unsupported" — `touch_edge_b` has no
   CCW guard, and `contains_b` guards only A.

   Five names are not a partition.  Leftover `Ⅰ` classifies the
   T-junction in `RelateNGTouchPartialEdge`.  Do not invent the
   obtuse-at-v certificate in this file.  Not an ADR-0004 remint.
   `522-j` is the existing #577 ticket id.  The filtered-completeness
   retry (`522-m`) lives below: excluding the T-junction 12-tuple,
   completeness is still FALSE (obtuse-at-v).

   WITNESS topic: relate · claimId: 522-j · witness: 522-j-sentinel-cex
   WITNESS topic: relate · claimId: 522-m · witness: 522-m-complete-filtered
   macro: relate
   lane: proofs
   issue: #577 / #522
   ADR-0004: not a remint. 522-j is the existing #577 ticket id.
   522-m is the filtered-completeness retry (unused letter; not 522-d..l).

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

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

(* 522-j recorded this pair as the decline cex. Leftover Ⅰ classifies
   it. Live completeness cex is obtuse (522-m). *)
Theorem triangle_pair_regime_incomplete_tjunction :
  0 < gdbl 0 0 2 0 0 1 /\
  0 < gdbl 1 0 3 0 2 1 /\
  triangle_pair_regime 0 0 2 0 0 1 1 0 3 0 2 1 = TPR_TouchPartialEdge.
Proof.
  split; [unfold gdbl; lra|].
  split; [unfold gdbl; lra|].
  exact tjunction_pair_touch_partial.
Qed.

(* -------------------------------------------------------------------------- *)
(* Hard-pair family that does classify.  Cite existing, do not re-prove.      *)
(* Catalog: disjoint #571 / 522-c on the #530 sentinel; overlap #570 /        *)
(* 522-b on the #567 pair; vertex-touch #572 / 522-i; shared-edge touch       *)
(* is the pre-#522 `TPR_TouchEdge` pin.                                       *)
(* -------------------------------------------------------------------------- *)

(* #571 / 522-c: the #530 sentinel `(0,0)(1,0)(0,1)` vs `(2,0)(3,0)(2,1)`. *)
Lemma classified_disjoint_pair :
  triangle_pair_regime 0 0 1 0 0 1 2 0 3 0 2 1 = TPR_Disjoint.
Proof.
  exact (triangle_pair_regime_disjoint 0 0 1 0 0 1 2 0 3 0 2 1
           dispatch_pair_separated_b).
Qed.

(* #570 / 522-b: the #567 overlap pair. *)
Lemma classified_overlap_pair :
  triangle_pair_regime 0 0 1 0 0 1 (1/4) (1/4) (5/4) (1/4) (1/4) (5/4)
    = TPR_Overlap.
Proof.
  exact (triangle_pair_regime_overlap 0 0 1 0 0 1
           (1/4) (1/4) (5/4) (1/4) (1/4) (5/4) overlap_ex_overlap_b).
Qed.

(* #572 / 522-i: ticket vertex-touch pair. *)
Lemma classified_touchvertex_pair :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 0 (-2) = TPR_TouchVertex.
Proof.
  exact (triangle_pair_regime_touchvertex 0 0 2 0 0 2
           0 0 (-2) 0 0 (-2) touchvertex_ex_touch_vertex_b).
Qed.

(* Pre-#522 shared-edge pin, not a #522 subtask. *)
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

(* -------------------------------------------------------------------------- *)
(* Filtered-hypothesis retry (#522 claimId 522-m).                            *)
(*                                                                            *)
(* The unrestricted CCW-completeness hypothesis is false (#577 / 522-j) on    *)
(* the T-junction 12-tuple.  Retry: exclude that tuple and ask again.         *)
(* Different tactic: do not retry SAT / trichotomy; exhibit a second          *)
(* leftover family.  Completeness is still FALSE.  The second pair is         *)
(* obtuse-at-v — A = (0,0)(2,0)(0,2), B = (0,0)(-2,0)(1,-1).  Both CCW,       *)
(* exactly one shared vertex, cone normal through v puts a remaining          *)
(* B-vertex on the line (side_dot = 0).  No certificate is invented.          *)
(* -------------------------------------------------------------------------- *)

Definition tjunction_pair_coords
    (ax ay bx by_ cx cy dx dy ex ey fx fy : R) : Prop :=
  ax = 0 /\ ay = 0 /\ bx = 2 /\ by_ = 0 /\ cx = 0 /\ cy = 1 /\
  dx = 1 /\ dy = 0 /\ ex = 3 /\ ey = 0 /\ fx = 2 /\ fy = 1.

Lemma obtuse_pair_both_ccw :
  0 < gdbl 0 0 2 0 0 2 /\ 0 < gdbl 0 0 (-2) 0 1 (-1).
Proof. unfold gdbl; split; lra. Qed.

Lemma obtuse_pair_not_tjunction :
  ~ tjunction_pair_coords 0 0 2 0 0 2 0 0 (-2) 0 1 (-1).
Proof.
  intros [Hax [Hay [Hbx [Hby [Hcx [Hcy _]]]]]].
  lra.
Qed.

Lemma both_strict_neg_b_false_snd : forall v n p q,
  ~ (side_dot v n q < 0) ->
  both_strict_neg_b v n p q = false.
Proof.
  intros v n p q Hn. unfold both_strict_neg_b.
  destruct (Rlt_dec (side_dot v n p) 0) as [_ | _];
    [| reflexivity ].
  destruct (Rlt_dec (side_dot v n q) 0) as [Hlt | _];
    [ contradiction | reflexivity ].
Qed.

Lemma both_strict_pos_b_false_snd : forall v n p q,
  ~ (0 < side_dot v n q) ->
  both_strict_pos_b v n p q = false.
Proof.
  intros v n p q Hn. unfold both_strict_pos_b.
  destruct (Rlt_dec 0 (side_dot v n p)) as [_ | _];
    [| reflexivity ].
  destruct (Rlt_dec 0 (side_dot v n q)) as [Hlt | _];
    [ contradiction | reflexivity ].
Qed.

Lemma obtuse_no_separator :
  some_edge_separates_b
    (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
    (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1)) = false.
Proof.
  unfold some_edge_separates_b.
  (* A bottom y=0: B's (0,0) is an endpoint. *)
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
             (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* A hypotenuse: B's (0,0) equals A's apex. *)
  rewrite (edge_separates_b_false_l (mkPoint 2 0) (mkPoint 0 2) (mkPoint 0 0)
             (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* A left x=0: B's (0,0) is an endpoint. *)
  rewrite (edge_separates_b_false_l (mkPoint 0 2) (mkPoint 0 0) (mkPoint 2 0)
             (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* B bottom y=0: A's (0,0) is an endpoint. *)
  rewrite (edge_separates_b_false_l (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* B sloped: A's (0,0) equals B's apex. *)
  rewrite (edge_separates_b_false_l (mkPoint (-2) 0) (mkPoint 1 (-1)) (mkPoint 0 0)
             (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)).
  2: { apply opposite_sides_b_false_of_nlt. unfold cross; cbn [px py]; lra. }
  (* B last: A's (0,0) is an endpoint (q1). *)
  assert (E6 : edge_separates_b (mkPoint 1 (-1)) (mkPoint 0 0) (mkPoint (-2) 0)
                 (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2) = false).
  { unfold edge_separates_b, opposite_sides_b, cross; cbn [px py].
    destruct (Rlt_dec (_ * _) 0) as [Hbad | _];
      [ exfalso; lra | reflexivity ]. }
  rewrite E6. reflexivity.
Qed.

Lemma obtuse_pair_unsupported :
  triangle_pair_regime 0 0 2 0 0 2 0 0 (-2) 0 1 (-1) = TPR_Unsupported.
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
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 0 0))) as [H1 | _];
    [ exfalso; lra | ].
  assert (H20 : gtri 0 0 2 0 0 2 (mkPoint (-2) 0) <= 0).
  { unfold gtri.
    assert (H : gsA 0 0 2 0 (mkPoint (-2) 0) = 0) by (unfold gsA; simpl; ring).
    rewrite H. eapply Rle_trans; [ apply Rmin_l_le | apply Rmin_l_le ]. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint (-2) 0))) as [H2 | _];
    [ exfalso; lra | ].
  assert (H1n : gtri 0 0 2 0 0 2 (mkPoint 1 (-1)) < 0).
  { eapply Rle_lt_trans; [ apply (gtri_le_gsA 0 0 2 0 0 2 (mkPoint 1 (-1))) | ].
    unfold gsA; cbn [px py]; lra. }
  destruct (Rlt_dec 0 (gtri 0 0 2 0 0 2 (mkPoint 1 (-1)))) as [H3 | _];
    [ exfalso; lra | ].
  unfold separated_b.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  rewrite obtuse_no_separator.
  unfold touch_vertex_b, exactly_one_shared_from_a, is_vertex_b, point_eqb.
  destruct (Rlt_dec 0 (gdbl 0 0 2 0 0 2)) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  destruct (Rlt_dec 0 (gdbl 0 0 (-2) 0 1 (-1))) as [_ | Hn];
    [ | exfalso; apply Hn; unfold gdbl; lra ].
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  assert (HA2 : touch_vertex_from_v
            (mkPoint 2 0)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1)) = false).
  { unfold touch_vertex_from_v.
    rewrite (is_vertex_b_false_of_none
               (mkPoint 2 0)
               (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))).
    - rewrite andb_false_r, andb_false_l. reflexivity.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_px; lra.
    - apply mkPoint_neq_px; lra. }
  assert (HA3 : touch_vertex_from_v
            (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1)) = false).
  { unfold touch_vertex_from_v.
    rewrite (is_vertex_b_false_of_none
               (mkPoint 0 2)
               (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1))).
    - rewrite andb_false_r, andb_false_l. reflexivity.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra.
    - apply mkPoint_neq_py; lra. }
  assert (HA1 : touch_vertex_from_v
            (mkPoint 0 0)
            (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
            (mkPoint 0 0) (mkPoint (-2) 0) (mkPoint 1 (-1)) = false).
  { unfold touch_vertex_from_v, others_fst, others_snd.
    rewrite (point_eqb_complete (mkPoint 0 0) (mkPoint 0 0) eq_refl).
    rewrite (cone_separates_b_false_of_arms
               (mkPoint 0 0) (mkPoint 2 0) (mkPoint 0 2)
               (mkPoint (-2) 0) (mkPoint 1 (-1))).
    - rewrite andb_false_r. reflexivity.
    - apply both_strict_neg_b_false_snd.
      unfold vec_sum_from, side_dot. cbn [px py]. lra.
    - apply both_strict_pos_b_false_snd.
      unfold vec_sum_from, side_dot. cbn [px py]. lra. }
  rewrite HA1, HA2, HA3.
  rewrite !orb_false_r, andb_false_r.
  unfold touch_partial_edge_b, some_vertex_on_open_edges,
         vertex_on_open_edges, on_open_seg_b, cross.
  cbn [px py].
  repeat (destruct (Req_dec_T _ _) as [?e | ?n]; try (exfalso; lra)).
  repeat (destruct (Rlt_dec _ _) as [?lt | ?nge]; try (exfalso; lra)).
  reflexivity.
Qed.

(* WITNESS {"claimId":"522-j","topic":"relate","lemma":"triangle_pair_regime_ccw_incomplete","title":"Classifier completeness is still false after leftover Ⅰ: obtuse-at-v emits TPR_Unsupported","file":"theories/RelateNGComplete.v","witness":"522-j-sentinel-cex","board":"#577"} *)
Theorem triangle_pair_regime_ccw_incomplete :
  exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
    0 < gdbl ax ay bx by_ cx cy /\
    0 < gdbl dx dy ex ey fx fy /\
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_Unsupported.
Proof.
  exists 0, 0, 2, 0, 0, 2, 0, 0, (-2), 0, 1, (-1).
  split; [unfold gdbl; lra|].
  split; [unfold gdbl; lra|].
  exact obtuse_pair_unsupported.
Qed.

(* WITNESS {"claimId":"522-m","topic":"relate","lemma":"triangle_pair_regime_ccw_incomplete_not_tjunction","title":"Filtered CCW-completeness is still false: obtuse-at-v declines after the T-junction cex is excluded","file":"theories/RelateNGComplete.v","witness":"522-m-complete-filtered","board":"#522"} *)
Theorem triangle_pair_regime_ccw_incomplete_not_tjunction :
  exists ax ay bx by_ cx cy dx dy ex ey fx fy : R,
    0 < gdbl ax ay bx by_ cx cy /\
    0 < gdbl dx dy ex ey fx fy /\
    ~ tjunction_pair_coords ax ay bx by_ cx cy dx dy ex ey fx fy /\
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
      = TPR_Unsupported.
Proof.
  exists 0, 0, 2, 0, 0, 2, 0, 0, (-2), 0, 1, (-1).
  split; [unfold gdbl; lra|].
  split; [unfold gdbl; lra|].
  split; [exact obtuse_pair_not_tjunction|].
  exact obtuse_pair_unsupported.
Qed.

Theorem ccw_complete_except_tjunction_false :
  ~ (forall ax ay bx by_ cx cy dx dy ex ey fx fy : R,
       0 < gdbl ax ay bx by_ cx cy ->
       0 < gdbl dx dy ex ey fx fy ->
       ~ tjunction_pair_coords ax ay bx by_ cx cy dx dy ex ey fx fy ->
       triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy
         <> TPR_Unsupported).
Proof.
  intros H.
  destruct triangle_pair_regime_ccw_incomplete_not_tjunction
    as [ax [ay [bx [by_ [cx [cy [dx [dy [ex [ey [fx [fy H12]]]]]]]]]]]].
  destruct H12 as [HA [HB [Hn Hreg]]].
  apply (H ax ay bx by_ cx cy dx dy ex ey fx fy HA HB Hn).
  exact Hreg.
Qed.

Print Assumptions triangle_pair_regime_incomplete_tjunction.
Print Assumptions triangle_pair_regime_ccw_incomplete.
Print Assumptions classified_hard_pairs.
Print Assumptions non_ccw_pair_no_overlap_disjoint_vertex.
Print Assumptions triangle_pair_regime_ccw_incomplete_not_tjunction.
Print Assumptions ccw_complete_except_tjunction_false.
