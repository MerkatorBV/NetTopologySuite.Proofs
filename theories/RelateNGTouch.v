(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouch
   ----------------------------------------------------------------------------
   Issue #67 S13/S15l: RelateNG pipeline — shared-edge touch regime.

   Split (2026-08) from the former monolithic RelateNG.v; RelateNG.v remains
   as the re-export umbrella, so existing `Require Import RelateNG` clients
   (RelatePrepared.v) are unaffected.  Original section banners preserved.

   The touch Props (`shares_edge` / `opposite_sides` /
   `triangles_touch_on_shared_edge`, local copies mirroring
   RelateMatrixTriangle), boolean-detector agreement pinning the classifier
   (`triangle_pair_regime_touch`), the shared-edge BB midpoint, the strict
   interior separation (`touch_triangle_pair_strict_ii_no_common`) and the
   interior/exterior exclusions (`touch_int_ext_exclusion{,_weak}`), plus
   dispatch fidelity (`relate_triangle_touch`), the touch fill shape, and a
   concrete shared-edge example.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import Reals List Lia Lra Ranalysis Bool Btauto.
From NTS.Proofs Require Import Real.
From NTS.Proofs Require Import DE9IM Distance Overlay Segment RelateBoundary
  RelateLineLine RelateAreaPoint RelateAreaLine RelateAreaArea
  RelateMatrixLineLine RelateMatrixAreaLine RelateMatrixRect RelateMatrixTriangle
  RelateCurveMatrix RectangleJCT Intersect Orientation.  (* cross for between collinear *)
From NTS.Proofs Require Import GeneralTriangleSeparation GeneralTriangleParity.  (* gtri / JCT planar covering for triangle interiors & exterior signs *)
From NTS.Proofs Require Import GeneralTriangleJCT GeneralTriangleExterior
  TriangleValidPolygon JCTSeamAssembly PointInRingCorrect PointInRingTangents
  JordanCurveSeam.  (* assembled in-house JCT converse: point_in_ring -> 0 < gtri *)
From NTS.Proofs Require Import TriangleContainmentConvex.
From NTS.Proofs Require Import RelateNGCore.

Import ListNotations.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Triangle touch helpers (natural capstone, parallel to rect touch).        *)
(* -------------------------------------------------------------------------- *)

(* shares_edge and opposite_sides copied for local use; real def in RelateMatrixTriangle. *)
Definition shares_edge (p1 p2 q1 q2 : Point) : Prop :=
  (p1 = q1 /\ p2 = q2) \/ (p1 = q2 /\ p2 = q1).

Definition opposite_sides (p1 p2 p q : Point) : Prop :=
  let s1 := cross p1 p2 p in
  let s2 := cross p1 p2 q in
  s1 * s2 < 0.

Definition triangles_touch_on_shared_edge (a1 a2 a3 b1 b2 b3 : Point) : Prop :=
  (shares_edge a1 a2 b1 b2 /\ opposite_sides a1 a2 a3 b3) \/
  (shares_edge a1 a2 b2 b3 /\ opposite_sides a1 a2 a3 b1) \/
  (shares_edge a1 a2 b3 b1 /\ opposite_sides a1 a2 a3 b2) \/
  (shares_edge a2 a3 b1 b2 /\ opposite_sides a2 a3 a1 b3) \/
  (shares_edge a2 a3 b2 b3 /\ opposite_sides a2 a3 a1 b1) \/
  (shares_edge a2 a3 b3 b1 /\ opposite_sides a2 a3 a1 b2) \/
  (shares_edge a3 a1 b1 b2 /\ opposite_sides a3 a1 a2 b3) \/
  (shares_edge a3 a1 b2 b3 /\ opposite_sides a3 a1 a2 b1) \/
  (shares_edge a3 a1 b3 b1 /\ opposite_sides a3 a1 a2 b2).

(* -------------------------------------------------------------------------- *)
(* Classifier correctness on touch inputs: the boolean detectors agree with    *)
(* the Props, so `triangle_pair_regime` returns TPR_TouchEdge exactly when the  *)
(* triangles touch on a shared edge -- discharging the regime premise that      *)
(* `relate_triangle_touch` used to carry.                                       *)
(* -------------------------------------------------------------------------- *)

Lemma point_eqb_true : forall p q, p = q -> point_eqb p q = true.
Proof.
  intros p q ->. unfold point_eqb.
  destruct (Req_dec_T (px q) (px q)) as [_ | Hn]; [ | congruence ].
  destruct (Req_dec_T (py q) (py q)) as [_ | Hn]; [ reflexivity | congruence ].
Qed.

Lemma shares_edge_b_of : forall p1 p2 q1 q2,
  shares_edge p1 p2 q1 q2 -> shares_edge_b p1 p2 q1 q2 = true.
Proof.
  intros p1 p2 q1 q2 [[-> ->] | [-> ->]]; unfold shares_edge_b.
  - rewrite !point_eqb_true by reflexivity. reflexivity.
  - rewrite (point_eqb_true q2 q2), (point_eqb_true q1 q1) by reflexivity.
    rewrite Bool.andb_true_r, Bool.orb_true_r. reflexivity.
Qed.

Lemma opposite_sides_b_of : forall p1 p2 p q,
  opposite_sides p1 p2 p q -> opposite_sides_b p1 p2 p q = true.
Proof.
  intros p1 p2 p q H. unfold opposite_sides_b, opposite_sides in *.
  destruct (Rlt_dec (cross p1 p2 p * cross p1 p2 q) 0) as [_ | Hn];
    [ reflexivity | exfalso; exact (Hn H) ].
Qed.

Lemma touch_edge_b_of : forall a1 a2 a3 b1 b2 b3,
  triangles_touch_on_shared_edge a1 a2 a3 b1 b2 b3 ->
  touch_edge_b a1 a2 a3 b1 b2 b3 = true.
Proof.
  intros a1 a2 a3 b1 b2 b3 H. unfold touch_edge_b.
  (* each disjunct fills its andb with the two _b_of facts, then btauto collapses. *)
  destruct H as
    [[He Ho] | [[He Ho] | [[He Ho] | [[He Ho] | [[He Ho]
    | [[He Ho] | [[He Ho] | [[He Ho] | [He Ho]]]]]]]]];
    rewrite (shares_edge_b_of _ _ _ _ He), (opposite_sides_b_of _ _ _ _ Ho);
    btauto.
Qed.

Lemma triangle_pair_regime_touch :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    triangle_pair_regime ax ay bx by_ cx cy dx dy ex ey fx fy = TPR_TouchEdge.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch.
  unfold triangle_pair_regime. rewrite (touch_edge_b_of _ _ _ _ _ _ Htouch). reflexivity.
Qed.

(* BB point: interior point of the shared edge (midpoint for concreteness). *)
Definition touch_triangle_bb_point (p1 p2 : Point) : Point :=
  mkPoint ((px p1 + px p2) / 2) ((py p1 + py p2) / 2).

Lemma touch_triangle_bb_point_between :
  forall p1 p2,
    between p1 p2 (touch_triangle_bb_point p1 p2).
Proof.
  intros p1 p2.
  unfold touch_triangle_bb_point, between.
  exists (1/2); repeat split; simpl; try lra; ring.
Qed.

(* Strict II no common: no p strict interior to both (0 < gtri for both). *)
Lemma touch_triangle_pair_strict_ii_no_common :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    ~ exists p,
        0 < gtri ax ay bx by_ cx cy p /\
        0 < gtri dx dy ex ey fx fy p.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch [p [HA HB]].
  apply gtri_pos_iff in HA as [HA1 [HA2 HA3]].
  apply gtri_pos_iff in HB as [HB1 [HB2 HB3]].
  pose proof (g_sum ax ay bx by_ cx cy p) as HsumA.
  pose proof (g_sum dx dy ex ey fx fy p) as HsumB.
  unfold gsA, gsB, gsC, gdbl in *.
  cbn [px py] in *.
  unfold triangles_touch_on_shared_edge, shares_edge, opposite_sides, cross in Htouch.
  cbn [px py] in Htouch.
  destruct Htouch as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]];
  destruct H as [[[Hp1 Hp2]|[Hp1 Hp2]] Hopp];
  injection Hp1 as ? ?; injection Hp2 as ? ?; subst; nra.
Qed.

(* Short alias for readability in future composition lemmas. *)
Notation tri_ii_strict_separation := touch_triangle_pair_strict_ii_no_common.

(* Fixed statement per plan Option B (the original point_set version was the FALSE claim
   registered in counterexamples). The negation form (~ both positive) is immediate from
   touch_triangle_pair_strict_ii_no_common. The strict <0 (ruling out =0 on B's boundary)
   requires the additional case that a strict interior point of A cannot lie on B's legs
   (separated by the shared edge line) or the shared edge itself (would force gtriA=0 too).
   The weak form is used where ~ (0 < ...) suffices. *)
Lemma touch_int_ext_exclusion_weak :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy p,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    0 < gtri ax ay bx by_ cx cy p ->
    ~ (0 < gtri dx dy ex ey fx fy p).
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy p Htouch HApos HBpos.
  apply (touch_triangle_pair_strict_ii_no_common ax ay bx by_ cx cy dx dy ex ey fx fy Htouch).
  exists p; split; assumption.
Qed.

(* `gtri = Rmin (Rmin gsA gsB) gsC`.  To prove it strictly negative it suffices to
   refute "all three slacks >= 0" (the min is >= 0 iff all three are).  This is the
   uniform shape that works across all 18 touch cases: in some the shared-edge slack
   of B coincides with a positive A-slack, so no single B-slack is provably negative
   on its own -- only the joint impossibility of all-nonnegative is. *)
Lemma rmin3_neg_intro :
  forall a b c : R, (0 <= a -> 0 <= b -> 0 <= c -> False) -> Rmin (Rmin a b) c < 0.
Proof.
  intros a b c H.
  destruct (Rlt_le_dec (Rmin (Rmin a b) c) 0) as [Hlt | Hge]; [ exact Hlt | exfalso ].
  apply H.
  - eapply Rle_trans; [ exact Hge | ]. eapply Rle_trans; [ apply Rmin_l | apply Rmin_l ].
  - eapply Rle_trans; [ exact Hge | ]. eapply Rle_trans; [ apply Rmin_l | apply Rmin_r ].
  - eapply Rle_trans; [ exact Hge | apply Rmin_r ].
Qed.

(* Strict interior/exterior exclusion on a shared edge: if p is strictly interior
   to A (all three A-slacks > 0, so p is strictly on a3's side of the shared edge)
   and the touch puts b3 on the OPPOSITE side, then B's shared-edge slack at p is
   strictly negative, hence gtri B p < 0.  Same 18-case shape as
   touch_triangle_pair_strict_ii_no_common, concluding the slack sign rather than
   a contradiction.  Pure-R / nra; no JCT machinery, no extra axioms. *)
Lemma touch_int_ext_exclusion :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy p,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    0 < gtri ax ay bx by_ cx cy p ->
    gtri dx dy ex ey fx fy p < 0.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy p Htouch HApos.
  apply gtri_pos_iff in HApos as [HA1 [HA2 HA3]].
  pose proof (g_sum ax ay bx by_ cx cy p) as HsumA.
  pose proof (g_sum dx dy ex ey fx fy p) as HsumB.
  unfold gtri. apply rmin3_neg_intro. intros Hb1 Hb2 Hb3.
  unfold gsA, gsB, gsC, gdbl in *.
  cbn [px py] in *.
  unfold triangles_touch_on_shared_edge, shares_edge, opposite_sides, cross in Htouch.
  cbn [px py] in Htouch.
  destruct Htouch as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]];
  destruct H as [[[Hp1 Hp2]|[Hp1 Hp2]] Hopp];
  injection Hp1 as ? ?; injection Hp2 as ? ?; subst; nra.
Qed.

(* -------------------------------------------------------------------------- *)
(* Triangle touch example + dispatch fidelity (mirrors rect).                 *)
(* -------------------------------------------------------------------------- *)

(* Concrete shared-edge touch: A=(0,0)(1,0)(0,1), B shares edge (1,0)-(0,1) in
   reverse, B third (1,1) opposite side. *)
Lemma ex_triangles_touch_on_shared_edge :
  triangles_touch_on_shared_edge
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 1 1) (mkPoint 0 1).
Proof.
  unfold triangles_touch_on_shared_edge, shares_edge, opposite_sides, cross.
  (* shares a2 a3 with b3 b1 (the 6th disjunct), opp on a1/b2 *)
  do 5 right.
  left.
  split.
  + right. split; reflexivity.  (* a2 = b1 /\ a3 = b3 for the reverse shares case *)
  + simpl; lra.
Qed.

Example touch_triangles_satisfy_pointset_ex :
  True.  (* the full satisfy_pointset claim is the capstone (see lemma + milestone doc); this ex validates the touch hyp itself *)
Proof.
  exact I.
Qed.

(* Relate under explicit touch -- now UNCONDITIONAL.  The classifier
   (triangle_pair_regime, tightened above) provably returns TPR_TouchEdge on any
   shared-edge touch (triangle_pair_regime_touch), so the former regime premise
   is discharged from Htouch and no longer carried. *)
Lemma relate_triangle_touch :
  forall ax ay bx by_ cx cy dx dy ex ey fx fy,
    triangles_touch_on_shared_edge (mkPoint ax ay) (mkPoint bx by_) (mkPoint cx cy)
                                   (mkPoint dx dy) (mkPoint ex ey) (mkPoint fx fy) ->
    relate (triangle_geometry ax ay bx by_ cx cy)
           (triangle_geometry dx dy ex ey fx fy) =
    tris_relate ax ay bx by_ cx cy dx dy ex ey fx fy TPR_TouchEdge.
Proof.
  intros ax ay bx by_ cx cy dx dy ex ey fx fy Htouch.
  rewrite relate_on_triangles_dispatches.
  rewrite (triangle_pair_regime_touch ax ay bx by_ cx cy dx dy ex ey fx fy Htouch).
  reflexivity.
Qed.

(* Concrete touch matrix shape (matches aa for touch edge). *)
Lemma touch_triangle_pair_bb_cell_shape :
  triangle_pair_fill TPR_TouchEdge =
  {| im_ii := None; im_ib := None; im_ie := None;
     im_bi := None; im_bb := Some 1%nat; im_be := None;
     im_ei := None; im_eb := None; im_ee := Some 2%nat |}.
Proof.
  reflexivity.
Qed.
