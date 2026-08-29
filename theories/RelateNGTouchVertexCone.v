(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchVertexCone
   ----------------------------------------------------------------------------
   Slice of #572 / 522-i. Boolean unpackers, affine side_dot, cone uniqueness,
   and `touch_vertex_b_triangles_touch`.  The original name
   RelateNGTouchVertex.v is the Require Export umbrella.

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
  RelateNGDisjoint.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Boolean unpackers.                                                         *)
(* -------------------------------------------------------------------------- *)

Lemma point_eqb_sound : forall p q, point_eqb p q = true -> p = q.
Proof.
  intros [px1 py1] [px2 py2] H.
  unfold point_eqb in H; cbn [px py] in H.
  destruct (Req_dec_T px1 px2) as [Hx | _]; [ | discriminate ].
  destruct (Req_dec_T py1 py2) as [Hy | _]; [ | discriminate ].
  subst; reflexivity.
Qed.

Lemma point_eqb_complete : forall p q, p = q -> point_eqb p q = true.
Proof.
  intros p q Heq. subst q. unfold point_eqb.
  destruct (Req_dec_T (px p) (px p)) as [_ | Hn];
    [ | exfalso; apply Hn; reflexivity ].
  destruct (Req_dec_T (py p) (py p)) as [_ | Hn];
    [ reflexivity | exfalso; apply Hn; reflexivity ].
Qed.

Lemma is_vertex_b_sound : forall v p q r,
  is_vertex_b v p q r = true -> is_vertex_of v p q r.
Proof.
  intros v p q r H.
  unfold is_vertex_b in H.
  apply orb_true_iff in H as [H | H3];
    [ apply orb_true_iff in H as [H1 | H2];
      [ left; apply point_eqb_sound; exact H1
      | right; left; apply point_eqb_sound; exact H2 ]
    | right; right; apply point_eqb_sound; exact H3 ].
Qed.

Lemma both_strict_pos_b_elim : forall v n p q,
  both_strict_pos_b v n p q = true ->
  0 < side_dot v n p /\ 0 < side_dot v n q.
Proof.
  intros v n p q H.
  unfold both_strict_pos_b in H.
  apply andb_true_iff in H as [Hp Hq].
  split.
  - destruct (Rlt_dec 0 (side_dot v n p)) as [Hlt | _];
      [ exact Hlt | discriminate ].
  - destruct (Rlt_dec 0 (side_dot v n q)) as [Hlt | _];
      [ exact Hlt | discriminate ].
Qed.

Lemma both_strict_neg_b_elim : forall v n p q,
  both_strict_neg_b v n p q = true ->
  side_dot v n p < 0 /\ side_dot v n q < 0.
Proof.
  intros v n p q H.
  unfold both_strict_neg_b in H.
  apply andb_true_iff in H as [Hp Hq].
  split.
  - destruct (Rlt_dec (side_dot v n p) 0) as [Hlt | _];
      [ exact Hlt | discriminate ].
  - destruct (Rlt_dec (side_dot v n q) 0) as [Hlt | _];
      [ exact Hlt | discriminate ].
Qed.

Lemma cone_separates_b_elim : forall v a1 a2 b1 b2,
  cone_separates_b v a1 a2 b1 b2 = true ->
  (0 < side_dot v (vec_sum_from v a1 a2) a1 /\
   0 < side_dot v (vec_sum_from v a1 a2) a2 /\
   side_dot v (vec_sum_from v a1 a2) b1 < 0 /\
   side_dot v (vec_sum_from v a1 a2) b2 < 0) \/
  (0 < side_dot v (vec_sum_from v b1 b2) b1 /\
   0 < side_dot v (vec_sum_from v b1 b2) b2 /\
   side_dot v (vec_sum_from v b1 b2) a1 < 0 /\
   side_dot v (vec_sum_from v b1 b2) a2 < 0).
Proof.
  intros v a1 a2 b1 b2 H.
  unfold cone_separates_b in H.
  apply orb_true_iff in H as [HA | HB].
  - apply andb_true_iff in HA as [Hp Hn].
    apply both_strict_pos_b_elim in Hp.
    apply both_strict_neg_b_elim in Hn.
    left. tauto.
  - apply andb_true_iff in HB as [Hp Hn].
    apply both_strict_pos_b_elim in Hp.
    apply both_strict_neg_b_elim in Hn.
    right. tauto.
Qed.

Lemma touch_vertex_from_v_elim : forall v a1 a2 a3 b1 b2 b3,
  touch_vertex_from_v v a1 a2 a3 b1 b2 b3 = true ->
  is_vertex_of v a1 a2 a3 /\
  is_vertex_of v b1 b2 b3 /\
  cone_separates_b v
    (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
    (others_fst v b1 b2 b3) (others_snd v b1 b2 b3) = true.
Proof.
  intros v a1 a2 a3 b1 b2 b3 H.
  unfold touch_vertex_from_v in H.
  apply andb_true_iff in H as [H Hc].
  apply andb_true_iff in H as [HA HB].
  repeat split;
    [ apply is_vertex_b_sound; exact HA
    | apply is_vertex_b_sound; exact HB
    | exact Hc ].
Qed.

Lemma touch_vertex_b_unpack :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    0 < gdbl ax ay bx by_ cx cy /\
    0 < gdbl dx dy ex ey fx fy /\
    exactly_one_shared_from_a
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = true /\
    (touch_vertex_from_v (mkPoint ax ay)
       (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
       (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = true \/
     touch_vertex_from_v (mkPoint bx by_)
       (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
       (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = true \/
     touch_vertex_from_v (mkPoint cx cy)
       (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
       (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) = true).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy H.
  unfold touch_vertex_b in H.
  destruct (Rlt_dec 0 (gdbl ax ay bx by_ cx cy)) as [HA | _];
    [ | discriminate ].
  destruct (Rlt_dec 0 (gdbl dx dy ex ey fx fy)) as [HB | _];
    [ | discriminate ].
  apply andb_true_iff in H as [Hex Hfrom].
  repeat split; [ exact HA | exact HB | exact Hex | ].
  apply orb_true_iff in Hfrom as [Hfrom | H3];
    [ apply orb_true_iff in Hfrom as [H1 | H2];
      [ left; exact H1
      | right; left; exact H2 ]
    | right; right; exact H3 ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Affine side function.                                                      *)
(* -------------------------------------------------------------------------- *)

Lemma side_dot_at_v : forall v n, side_dot v n v = 0.
Proof. intros [] []; unfold side_dot; simpl; ring. Qed.

Lemma side_dot_affine :
  forall v n a1 a2 a3 pt,
    side_dot v n pt
      * gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) =
      gsB (px a2) (py a2) (px a3) (py a3) pt * side_dot v n a1
    + gsC (px a1) (py a1) (px a3) (py a3) pt * side_dot v n a2
    + gsA (px a1) (py a1) (px a2) (py a2) pt * side_dot v n a3.
Proof. intros [] [] [] [] [] []; unfold side_dot, gsA, gsB, gsC, gdbl; simpl; ring. Qed.

Lemma bary_x :
  forall a1 a2 a3 pt,
    px pt * gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) =
      gsB (px a2) (py a2) (px a3) (py a3) pt * px a1
    + gsC (px a1) (py a1) (px a3) (py a3) pt * px a2
    + gsA (px a1) (py a1) (px a2) (py a2) pt * px a3.
Proof. intros [] [] [] []; unfold gsA, gsB, gsC, gdbl; simpl; ring. Qed.

Lemma bary_y :
  forall a1 a2 a3 pt,
    py pt * gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) =
      gsB (px a2) (py a2) (px a3) (py a3) pt * py a1
    + gsC (px a1) (py a1) (px a3) (py a3) pt * py a2
    + gsA (px a1) (py a1) (px a2) (py a2) pt * py a3.
Proof. intros [] [] [] []; unfold gsA, gsB, gsC, gdbl; simpl; ring. Qed.

Lemma mkPoint_congr : forall x1 y1 x2 y2,
  x1 = x2 -> y1 = y2 -> mkPoint x1 y1 = mkPoint x2 y2.
Proof. intros; subst; reflexivity. Qed.

Lemma pt_eq_a1_of_slacks :
  forall a1 a2 a3 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    gsA (px a1) (py a1) (px a2) (py a2) pt = 0 ->
    gsC (px a1) (py a1) (px a3) (py a3) pt = 0 ->
    gsB (px a2) (py a2) (px a3) (py a3) pt
      = gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    pt = a1.
Proof.
  intros a1 a2 a3 pt Hd HA HC HB.
  pose proof (bary_x a1 a2 a3 pt) as Hx.
  pose proof (bary_y a1 a2 a3 pt) as Hy.
  rewrite HA, HC, HB in Hx, Hy.
  destruct a1, a2, a3, pt; simpl in *;
    apply mkPoint_congr; nra.
Qed.

Lemma mkPoint_eta : forall p, mkPoint (px p) (py p) = p.
Proof. intros []; reflexivity. Qed.

Lemma pt_eq_a1 :
  forall a1 a2 a3 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    gsA (px a1) (py a1) (px a2) (py a2) pt = 0 ->
    gsC (px a1) (py a1) (px a3) (py a3) pt = 0 ->
    pt = a1.
Proof.
  intros a1 a2 a3 pt Hd HA HC.
  pose proof (slack_sum_free (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt)
    as Hs.
  rewrite HA, HC in Hs.
  apply (pt_eq_a1_of_slacks a1 a2 a3 pt Hd HA HC).
  lra.
Qed.

Lemma pt_eq_a2 :
  forall a1 a2 a3 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    gsA (px a1) (py a1) (px a2) (py a2) pt = 0 ->
    gsB (px a2) (py a2) (px a3) (py a3) pt = 0 ->
    pt = a2.
Proof.
  intros a1 a2 a3 pt Hd HA HB.
  pose proof (slack_sum_free (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt)
    as Hs.
  pose proof (bary_x a1 a2 a3 pt) as Hx.
  pose proof (bary_y a1 a2 a3 pt) as Hy.
  rewrite HA, HB in Hs, Hx, Hy.
  destruct a1, a2, a3, pt; simpl in *;
    apply mkPoint_congr; nra.
Qed.

Lemma pt_eq_a3 :
  forall a1 a2 a3 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    gsB (px a2) (py a2) (px a3) (py a3) pt = 0 ->
    gsC (px a1) (py a1) (px a3) (py a3) pt = 0 ->
    pt = a3.
Proof.
  intros a1 a2 a3 pt Hd HB HC.
  pose proof (slack_sum_free (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt)
    as Hs.
  pose proof (bary_x a1 a2 a3 pt) as Hx.
  pose proof (bary_y a1 a2 a3 pt) as Hy.
  rewrite HB, HC in Hs, Hx, Hy.
  destruct a1, a2, a3, pt; simpl in *;
    apply mkPoint_congr; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Side signs on a closed triangle.                                           *)
(* -------------------------------------------------------------------------- *)

Lemma others_cover : forall v p q r,
  (others_fst v p q r = q /\ others_snd v p q r = r /\ v = p) \/
  (others_fst v p q r = p /\ others_snd v p q r = r /\ v = q) \/
  (others_fst v p q r = p /\ others_snd v p q r = q /\
   point_eqb v p = false /\ point_eqb v q = false).
Proof.
  intros v p q r.
  unfold others_fst, others_snd.
  destruct (point_eqb v p) eqn:Ep.
  - apply point_eqb_sound in Ep. subst v. left. tauto.
  - destruct (point_eqb v q) eqn:Eq.
    + apply point_eqb_sound in Eq. subst v. right. left. tauto.
    + right. right. tauto.
Qed.

Lemma side_combo_pos :
  forall v n a1 a2 a3 pt s1 s2 s3,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    0 <= gtri (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt ->
    side_dot v n a1 = s1 ->
    side_dot v n a2 = s2 ->
    side_dot v n a3 = s3 ->
    0 <= s1 -> 0 <= s2 -> 0 <= s3 ->
    0 <= side_dot v n pt.
Proof.
  intros v n a1 a2 a3 pt s1 s2 s3 Hd Hg E1 E2 E3 Hs1 Hs2 Hs3.
  apply gtri_nonneg_iff in Hg.
  destruct Hg as [HA [HB HC]].
  pose proof (side_dot_affine v n a1 a2 a3 pt) as Haff.
  rewrite E1, E2, E3 in Haff.
  nra.
Qed.

Lemma side_combo_neg :
  forall v n a1 a2 a3 pt s1 s2 s3,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    0 <= gtri (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt ->
    side_dot v n a1 = s1 ->
    side_dot v n a2 = s2 ->
    side_dot v n a3 = s3 ->
    s1 <= 0 -> s2 <= 0 -> s3 <= 0 ->
    side_dot v n pt <= 0.
Proof.
  intros v n a1 a2 a3 pt s1 s2 s3 Hd Hg E1 E2 E3 Hs1 Hs2 Hs3.
  apply gtri_nonneg_iff in Hg.
  destruct Hg as [HA [HB HC]].
  pose proof (side_dot_affine v n a1 a2 a3 pt) as Haff.
  rewrite E1, E2, E3 in Haff.
  nra.
Qed.

Lemma side_zero_kills_pos_weights :
  forall v n a1 a2 a3 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    0 <= gtri (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt ->
    side_dot v n pt = 0 ->
    0 <= side_dot v n a1 ->
    0 <= side_dot v n a2 ->
    0 <= side_dot v n a3 ->
    (0 < side_dot v n a1 -> gsB (px a2) (py a2) (px a3) (py a3) pt = 0) /\
    (0 < side_dot v n a2 -> gsC (px a1) (py a1) (px a3) (py a3) pt = 0) /\
    (0 < side_dot v n a3 -> gsA (px a1) (py a1) (px a2) (py a2) pt = 0).
Proof.
  intros v n a1 a2 a3 pt Hd Hg Hz Hs1 Hs2 Hs3.
  apply gtri_nonneg_iff in Hg.
  destruct Hg as [HA [HB HC]].
  pose proof (side_dot_affine v n a1 a2 a3 pt) as Haff.
  rewrite Hz in Haff.
  repeat split; intros Hpos; nra.
Qed.

Lemma side_zero_kills_neg_weights :
  forall v n a1 a2 a3 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    0 <= gtri (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) pt ->
    side_dot v n pt = 0 ->
    side_dot v n a1 <= 0 ->
    side_dot v n a2 <= 0 ->
    side_dot v n a3 <= 0 ->
    (side_dot v n a1 < 0 -> gsB (px a2) (py a2) (px a3) (py a3) pt = 0) /\
    (side_dot v n a2 < 0 -> gsC (px a1) (py a1) (px a3) (py a3) pt = 0) /\
    (side_dot v n a3 < 0 -> gsA (px a1) (py a1) (px a2) (py a2) pt = 0).
Proof.
  intros v n a1 a2 a3 pt Hd Hg Hz Hs1 Hs2 Hs3.
  apply gtri_nonneg_iff in Hg.
  destruct Hg as [HA [HB HC]].
  pose proof (side_dot_affine v n a1 a2 a3 pt) as Haff.
  rewrite Hz in Haff.
  repeat split; intros Hneg; nra.
Qed.

Lemma assign_sides_owner :
  forall v n a1 a2 a3 r1 r2,
    is_vertex_of v a1 a2 a3 ->
    r1 = others_fst v a1 a2 a3 ->
    r2 = others_snd v a1 a2 a3 ->
    0 < side_dot v n r1 ->
    0 < side_dot v n r2 ->
    0 <= side_dot v n a1 /\ 0 <= side_dot v n a2 /\ 0 <= side_dot v n a3.
Proof.
  intros v n a1 a2 a3 r1 r2 Hv Er1 Er2 Hp1 Hp2.
  pose proof (others_cover v a1 a2 a3) as Hc.
  rewrite <- Er1, <- Er2 in Hc.
  destruct Hc as [Hc | [Hc | Hc]].
  - destruct Hc as (E1 & E2 & Ev).
    rewrite Ev, E1, E2 in *.
    rewrite (side_dot_at_v a1 n).
    split; [ apply Rle_refl | split; apply Rlt_le; assumption ].
  - destruct Hc as (E1 & E2 & Ev).
    rewrite Ev, E1, E2 in *.
    rewrite (side_dot_at_v a2 n).
    split; [ apply Rlt_le; assumption | split; [ apply Rle_refl | apply Rlt_le; assumption ] ].
  - destruct Hc as (E1 & E2 & Ep & Eq).
    destruct Hv as [Ev | [Ev | Ev]].
    + rewrite Ev in Ep. rewrite point_eqb_complete in Ep; [ discriminate | reflexivity ].
    + rewrite Ev in Eq. rewrite point_eqb_complete in Eq; [ discriminate | reflexivity ].
    + rewrite Ev, E1, E2 in *.
      rewrite (side_dot_at_v a3 n).
      split; [ apply Rlt_le; assumption | split; [ apply Rlt_le; assumption | apply Rle_refl ] ].
Qed.

Lemma assign_sides_other :
  forall v n a1 a2 a3 r1 r2,
    is_vertex_of v a1 a2 a3 ->
    r1 = others_fst v a1 a2 a3 ->
    r2 = others_snd v a1 a2 a3 ->
    side_dot v n r1 < 0 ->
    side_dot v n r2 < 0 ->
    side_dot v n a1 <= 0 /\ side_dot v n a2 <= 0 /\ side_dot v n a3 <= 0.
Proof.
  intros v n a1 a2 a3 r1 r2 Hv Er1 Er2 Hn1 Hn2.
  pose proof (others_cover v a1 a2 a3) as Hc.
  rewrite <- Er1, <- Er2 in Hc.
  destruct Hc as [Hc | [Hc | Hc]].
  - destruct Hc as (E1 & E2 & Ev).
    rewrite Ev, E1, E2 in *.
    rewrite (side_dot_at_v a1 n).
    split; [ apply Rle_refl | split; apply Rlt_le; assumption ].
  - destruct Hc as (E1 & E2 & Ev).
    rewrite Ev, E1, E2 in *.
    rewrite (side_dot_at_v a2 n).
    split; [ apply Rlt_le; assumption | split; [ apply Rle_refl | apply Rlt_le; assumption ] ].
  - destruct Hc as (E1 & E2 & Ep & Eq).
    destruct Hv as [Ev | [Ev | Ev]].
    + rewrite Ev in Ep. rewrite point_eqb_complete in Ep; [ discriminate | reflexivity ].
    + rewrite Ev in Eq. rewrite point_eqb_complete in Eq; [ discriminate | reflexivity ].
    + rewrite Ev, E1, E2 in *.
      rewrite (side_dot_at_v a3 n).
      split; [ apply Rlt_le; assumption | split; [ apply Rlt_le; assumption | apply Rle_refl ] ].
Qed.

Lemma cone_pos_meet_is_v :
  forall v n a1 a2 a3 r1 r2 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    is_vertex_of v a1 a2 a3 ->
    r1 = others_fst v a1 a2 a3 ->
    r2 = others_snd v a1 a2 a3 ->
    0 < side_dot v n r1 ->
    0 < side_dot v n r2 ->
    in_tri_closure a1 a2 a3 pt ->
    side_dot v n pt = 0 ->
    pt = v.
Proof.
  intros v n a1 a2 a3 r1 r2 pt Hd Hv Er1 Er2 Hp1 Hp2 Hcl Hz.
  unfold in_tri_closure in Hcl.
  pose proof (assign_sides_owner v n a1 a2 a3 r1 r2 Hv Er1 Er2 Hp1 Hp2)
    as (Os1 & Os2 & Os3).
  pose proof (side_zero_kills_pos_weights v n a1 a2 a3 pt Hd Hcl Hz Os1 Os2 Os3)
    as (K1 & K2 & K3).
  pose proof (others_cover v a1 a2 a3) as Hc.
  rewrite <- Er1, <- Er2 in Hc.
  destruct Hc as [Hc | [Hc | Hc]].
  - destruct Hc as (E1 & E2 & Ev).
    rewrite Ev, E1, E2 in *.
    apply (pt_eq_a1 a1 a2 a3 pt Hd);
      [ apply K3; exact Hp2 | apply K2; exact Hp1 ].
  - destruct Hc as (E1 & E2 & Ev).
    rewrite Ev, E1, E2 in *.
    apply (pt_eq_a2 a1 a2 a3 pt Hd);
      [ apply K3; exact Hp2 | apply K1; exact Hp1 ].
  - destruct Hc as (E1 & E2 & Ep & Eq).
    destruct Hv as [Ev | [Ev | Ev]].
    + rewrite Ev in Ep. rewrite point_eqb_complete in Ep; [ discriminate | reflexivity ].
    + rewrite Ev in Eq. rewrite point_eqb_complete in Eq; [ discriminate | reflexivity ].
    + rewrite Ev, E1, E2 in *.
      apply (pt_eq_a3 a1 a2 a3 pt Hd);
        [ apply K1; exact Hp1 | apply K2; exact Hp2 ].
Qed.

Lemma cone_neg_meet_is_v :
  forall v n a1 a2 a3 r1 r2 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    is_vertex_of v a1 a2 a3 ->
    r1 = others_fst v a1 a2 a3 ->
    r2 = others_snd v a1 a2 a3 ->
    side_dot v n r1 < 0 ->
    side_dot v n r2 < 0 ->
    in_tri_closure a1 a2 a3 pt ->
    side_dot v n pt = 0 ->
    pt = v.
Proof.
  intros v n a1 a2 a3 r1 r2 pt Hd Hv Er1 Er2 Hn1 Hn2 Hcl Hz.
  unfold in_tri_closure in Hcl.
  pose proof (assign_sides_other v n a1 a2 a3 r1 r2 Hv Er1 Er2 Hn1 Hn2)
    as (Ns1 & Ns2 & Ns3).
  pose proof (side_zero_kills_neg_weights v n a1 a2 a3 pt Hd Hcl Hz Ns1 Ns2 Ns3)
    as (K1 & K2 & K3).
  pose proof (others_cover v a1 a2 a3) as Hc.
  rewrite <- Er1, <- Er2 in Hc.
  destruct Hc as [Hc | [Hc | Hc]].
  - destruct Hc as (E1 & E2 & Ev).
    rewrite Ev, E1, E2 in *.
    apply (pt_eq_a1 a1 a2 a3 pt Hd);
      [ apply K3; exact Hn2 | apply K2; exact Hn1 ].
  - destruct Hc as (E1 & E2 & Ev).
    rewrite Ev, E1, E2 in *.
    apply (pt_eq_a2 a1 a2 a3 pt Hd);
      [ apply K3; exact Hn2 | apply K1; exact Hn1 ].
  - destruct Hc as (E1 & E2 & Ep & Eq).
    destruct Hv as [Ev | [Ev | Ev]].
    + rewrite Ev in Ep. rewrite point_eqb_complete in Ep; [ discriminate | reflexivity ].
    + rewrite Ev in Eq. rewrite point_eqb_complete in Eq; [ discriminate | reflexivity ].
    + rewrite Ev, E1, E2 in *.
      apply (pt_eq_a3 a1 a2 a3 pt Hd);
        [ apply K1; exact Hn1 | apply K2; exact Hn2 ].
Qed.

Lemma cone_line_unique :
  forall v n a1 a2 a3 b1 b2 b3 ra1 ra2 rb1 rb2 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    0 < gdbl (px b1) (py b1) (px b2) (py b2) (px b3) (py b3) ->
    is_vertex_of v a1 a2 a3 ->
    is_vertex_of v b1 b2 b3 ->
    ra1 = others_fst v a1 a2 a3 ->
    ra2 = others_snd v a1 a2 a3 ->
    rb1 = others_fst v b1 b2 b3 ->
    rb2 = others_snd v b1 b2 b3 ->
    0 < side_dot v n ra1 ->
    0 < side_dot v n ra2 ->
    side_dot v n rb1 < 0 ->
    side_dot v n rb2 < 0 ->
    in_tri_closure a1 a2 a3 pt ->
    in_tri_closure b1 b2 b3 pt ->
    pt = v.
Proof.
  intros v n a1 a2 a3 b1 b2 b3 ra1 ra2 rb1 rb2 pt
         HdA HdB HvA HvB Ea1 Ea2 Eb1 Eb2 Hp1 Hp2 Hn1 Hn2 HA HB.
  pose proof (assign_sides_owner v n a1 a2 a3 ra1 ra2 HvA Ea1 Ea2 Hp1 Hp2)
    as (Os1 & Os2 & Os3).
  pose proof (assign_sides_other v n b1 b2 b3 rb1 rb2 HvB Eb1 Eb2 Hn1 Hn2)
    as (Ns1 & Ns2 & Ns3).
  unfold in_tri_closure in HA, HB.
  assert (Hpos : 0 <= side_dot v n pt)
    by (apply (side_combo_pos v n a1 a2 a3 pt
                 (side_dot v n a1) (side_dot v n a2) (side_dot v n a3)
                 HdA HA eq_refl eq_refl eq_refl Os1 Os2 Os3)).
  assert (Hneg : side_dot v n pt <= 0)
    by (apply (side_combo_neg v n b1 b2 b3 pt
                 (side_dot v n b1) (side_dot v n b2) (side_dot v n b3)
                 HdB HB eq_refl eq_refl eq_refl Ns1 Ns2 Ns3)).
  assert (Hz : side_dot v n pt = 0) by lra.
  exact (cone_pos_meet_is_v v n a1 a2 a3 ra1 ra2 pt HdA HvA Ea1 Ea2 Hp1 Hp2 HA Hz).
Qed.

(* -------------------------------------------------------------------------- *)
(* Certificate ⇒ geometry.                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma cone_separates_unique :
  forall v a1 a2 a3 b1 b2 b3 pt,
    0 < gdbl (px a1) (py a1) (px a2) (py a2) (px a3) (py a3) ->
    0 < gdbl (px b1) (py b1) (px b2) (py b2) (px b3) (py b3) ->
    is_vertex_of v a1 a2 a3 ->
    is_vertex_of v b1 b2 b3 ->
    cone_separates_b v
      (others_fst v a1 a2 a3) (others_snd v a1 a2 a3)
      (others_fst v b1 b2 b3) (others_snd v b1 b2 b3) = true ->
    in_tri_closure a1 a2 a3 pt ->
    in_tri_closure b1 b2 b3 pt ->
    pt = v.
Proof.
  intros v a1 a2 a3 b1 b2 b3 pt HdA HdB HvA HvB Hc HA HB.
  apply cone_separates_b_elim in Hc.
  set (ra1 := others_fst v a1 a2 a3).
  set (ra2 := others_snd v a1 a2 a3).
  set (rb1 := others_fst v b1 b2 b3).
  set (rb2 := others_snd v b1 b2 b3).
  destruct Hc as [HA_side | HB_side].
  - destruct HA_side as (P1 & P2 & N1 & N2).
    exact (cone_line_unique v (vec_sum_from v ra1 ra2)
             a1 a2 a3 b1 b2 b3 ra1 ra2 rb1 rb2 pt
             HdA HdB HvA HvB eq_refl eq_refl eq_refl eq_refl
             P1 P2 N1 N2 HA HB).
  - destruct HB_side as (P1 & P2 & N1 & N2).
    exact (cone_line_unique v (vec_sum_from v rb1 rb2)
             b1 b2 b3 a1 a2 a3 rb1 rb2 ra1 ra2 pt
             HdB HdA HvB HvA eq_refl eq_refl eq_refl eq_refl
             P1 P2 N1 N2 HB HA).
Qed.

Theorem touch_vertex_b_triangles_touch :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    touch_vertex_b ax ay bx by_ cx cy dx dy ex ey fx fy = true ->
    triangles_touch_at_vertex
      (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
      (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htv.
  pose proof (touch_vertex_b_unpack _ _ _ _ _ _ _ _ _ _ _ _ Htv)
    as (HccwA & HccwB & _ & Hfrom).
  unfold triangles_touch_at_vertex, tri_ccw.
  split; [ exact HccwA | split; [ exact HccwB | ] ].
  pose (A1 := mkPoint ax ay).
  pose (A2 := mkPoint bx by_).
  pose (A3 := mkPoint cx cy).
  pose (B1 := mkPoint dx dy).
  pose (B2 := mkPoint ex ey).
  pose (B3 := mkPoint fx fy).
  assert (HdA : 0 < gdbl (px A1) (py A1) (px A2) (py A2) (px A3) (py A3))
    by (unfold A1, A2, A3; exact HccwA).
  assert (HdB : 0 < gdbl (px B1) (py B1) (px B2) (py B2) (px B3) (py B3))
    by (unfold B1, B2, B3; exact HccwB).
  destruct Hfrom as [Hv | [Hv | Hv]];
    apply touch_vertex_from_v_elim in Hv;
    destruct Hv as (HvA & HvB & Hc).
  - exists A1. split; [ exact HvA | split; [ exact HvB | ] ].
    intros pt HA HB.
    apply (cone_separates_unique _ A1 A2 A3 B1 B2 B3 pt HdA HdB HvA HvB Hc HA HB).
  - exists A2. split; [ exact HvA | split; [ exact HvB | ] ].
    intros pt HA HB.
    apply (cone_separates_unique _ A1 A2 A3 B1 B2 B3 pt HdA HdB HvA HvB Hc HA HB).
  - exists A3. split; [ exact HvA | split; [ exact HvB | ] ].
    intros pt HA HB.
    apply (cone_separates_unique _ A1 A2 A3 B1 B2 B3 pt HdA HdB HvA HvB Hc HA HB).
Qed.

Print Assumptions touch_vertex_b_triangles_touch.
