(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeDisjointCert
   ----------------------------------------------------------------------------
   A one-sign-test exact DISJOINTNESS certificate for integer segment pairs.

   RelateEdgeNodeDecide.v made the positive side of the lineal DE-9IM runnable:
   `dual_proper_cutb = true` decides that two integer segments properly cross
   and populates the II point-cell.  That test returning FALSE, however, proves
   nothing about emptiness -- collinear overlap and endpoint contact are also
   `false`, yet both share points.  The negative side needs its own certificate.

   This module supplies it.  The cheapest sound witness of disjointness is a
   single determinant-product sign:

       cut_product > 0   <->   A and B lie STRICTLY on the same side of line C-D

   and a segment whose endpoints are strictly on one side of a line never meets
   that line, hence never meets any segment lying on it.  The geometric content
   is convexity: `cross C D (.)` is affine along A-B, so its value at any point
   of the segment is a convex combination of two same-sign endpoint values, and
   therefore never zero -- while every point of C-D has `cross C D (.) = 0`.

   Landing:
     - `cross_between_convex` / `same_side_no_share` -- the R-side geometry;
     - `same_side_cutb` + `same_side_cut_no_share` -- the integer certificate;
     - `decide_line_no_ib_meet` -- HEADLINE: one integer sign test discharges
       ALL FOUR meet cells (II, IB, BI, BB) as empty, i.e. the pair realises
       `ll_matrix_disjoint`.  Disjointness is the highest-frequency relate query
       and this is the cheapest exact filter for it;
     - `same_side_excludes_dual_proper` -- coherence: the disjointness
       certificate and the II-cell classifier can never both fire.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith Lia Bool Reals Lra.
From NTS.Proofs Require Import Distance Orientation Segment
  RelateLineLine RelateNodingLineLine
  RelateIntDetBound RelateEdgeInterParam
  RelateEdgeMultiNode RelateEdgeDualCross RelateEdgeNodeDecide.

Local Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* §1  R-side geometry: strictly-same-side endpoints cannot meet the line.    *)
(* -------------------------------------------------------------------------- *)

(* `cross C D (.)` is affine along A-B: at a point of the segment it is the
   convex combination of its two endpoint values. *)
Lemma cross_between_convex :
  forall C D A B Q,
    between A B Q ->
    exists t : R, (0 <= t <= 1)%R /\
      (cross C D Q = (1 - t) * cross C D A + t * cross C D B)%R.
Proof.
  intros C D A B Q [t [Ht0 [Ht1 [Hx Hy]]]].
  exists t. split; [ lra | ].
  unfold cross. rewrite Hx, Hy. ring.
Qed.

(* A convex combination of two strictly positive values is strictly positive. *)
Lemma convex_comb_pos :
  forall t a b,
    (0 <= t)%R -> (t <= 1)%R -> (0 < a)%R -> (0 < b)%R ->
    (0 < (1 - t) * a + t * b)%R.
Proof.
  intros t a b Ht0 Ht1 Ha Hb.
  destruct (Rlt_le_dec t 1) as [H | H].
  - assert (H1 : (0 < (1 - t) * a)%R) by (apply Rmult_lt_0_compat; lra).
    assert (H2 : (0 <= t * b)%R) by (apply Rmult_le_pos; lra).
    lra.
  - assert (Ht : t = 1%R) by lra.
    rewrite Ht. replace ((1 - 1) * a + 1 * b)%R with b by ring. exact Hb.
Qed.

(* ... and of two strictly negative values is strictly negative. *)
Lemma convex_comb_neg :
  forall t a b,
    (0 <= t)%R -> (t <= 1)%R -> (a < 0)%R -> (b < 0)%R ->
    ((1 - t) * a + t * b < 0)%R.
Proof.
  intros t a b Ht0 Ht1 Ha Hb.
  assert (H := convex_comb_pos t (- a) (- b) Ht0 Ht1 ltac:(lra) ltac:(lra)).
  replace ((1 - t) * - a + t * - b)%R with (- ((1 - t) * a + t * b))%R in H
    by ring.
  lra.
Qed.

(* Sign transfer across a positive product. *)
Lemma pos_mult_pos_right :
  forall a b, (0 < a)%R -> (0 < a * b)%R -> (0 < b)%R.
Proof.
  intros a b Ha Hab.
  apply (Rmult_lt_reg_l a); [ exact Ha | ].
  rewrite Rmult_0_r. exact Hab.
Qed.

Lemma neg_mult_pos_right :
  forall a b, (a < 0)%R -> (0 < a * b)%R -> (b < 0)%R.
Proof.
  intros a b Ha Hab.
  assert (H : (0 < - b)%R).
  { apply (pos_mult_pos_right (- a)); [ lra | ].
    replace (- a * - b)%R with (a * b)%R by ring. exact Hab. }
  lra.
Qed.

(* If A and B are strictly on the same side of line C-D (positive product of
   their orientation determinants), the segments share no point at all. *)
Lemma same_side_no_share :
  forall A B C D,
    (0 < cross C D A * cross C D B)%R ->
    ~ segments_share A B C D.
Proof.
  intros A B C D Hpos [p [Hab Hcd]].
  (* p lies on segment C-D, hence on line C-D. *)
  assert (H0 : (cross C D p = 0)%R)
    by (apply (between_implies_on_line C D p); exact Hcd).
  (* p lies on segment A-B, hence its cross is a convex combination. *)
  destruct (cross_between_convex C D A B p Hab) as [t [[Ht0 Ht1] Heq]].
  rewrite H0 in Heq.
  destruct (Rlt_le_dec 0 (cross C D A)) as [Hpa | Hna].
  - assert (Hpb := pos_mult_pos_right _ _ Hpa Hpos).
    assert (H := convex_comb_pos t _ _ Ht0 Ht1 Hpa Hpb). lra.
  - assert (Hna' : (cross C D A < 0)%R).
    { destruct (Rle_lt_or_eq_dec (cross C D A) 0 Hna) as [H | H];
        [ exact H | ].
      exfalso. rewrite H, Rmult_0_l in Hpos. lra. }
    assert (Hnb := neg_mult_pos_right _ _ Hna' Hpos).
    assert (H := convex_comb_neg t _ _ Ht0 Ht1 Hna' Hnb). lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The integer certificate.                                               *)
(* -------------------------------------------------------------------------- *)

Definition same_side_cutb (ax ay bx by_ : Z) (c : ZCut) : bool :=
  Z.ltb 0 (cut_product ax ay bx by_ c).

Lemma same_side_cutb_iff :
  forall ax ay bx by_ c,
    same_side_cutb ax ay bx by_ c = true <-> 0 < cut_product ax ay bx by_ c.
Proof.
  intros. unfold same_side_cutb. apply Z.ltb_lt.
Qed.

(* The integer product IS the product of the two real orientation determinants. *)
Lemma cut_product_is_cross_product :
  forall ax ay bx by_ c,
    (cross (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)) (ptZ ax ay)
     * cross (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)) (ptZ bx by_))%R
    = IZR (cut_product ax ay bx by_ c).
Proof.
  intros. unfold cut_product.
  rewrite !cross_ptZ_is_idet, <- mult_IZR. reflexivity.
Qed.

Theorem same_side_cut_no_share :
  forall ax ay bx by_ c,
    same_side_cutb ax ay bx by_ c = true ->
    ~ segments_share (ptZ ax ay) (ptZ bx by_)
        (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)).
Proof.
  intros ax ay bx by_ c Hb.
  apply same_side_no_share.
  rewrite cut_product_is_cross_product.
  assert (Hz : 0 < cut_product ax ay bx by_ c)
    by (apply same_side_cutb_iff; exact Hb).
  assert (H : (IZR 0 < IZR (cut_product ax ay bx by_ c))%R)
    by (apply IZR_lt; exact Hz).
  change (IZR 0) with 0%R in H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  HEADLINE: one sign test empties all four meet cells.                   *)
(* -------------------------------------------------------------------------- *)

Theorem decide_line_no_ib_meet :
  forall ax ay bx by_ c,
    same_side_cutb ax ay bx by_ c = true ->
    line_no_ib_meet (ptZ ax ay) (ptZ bx by_)
      (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)) ll_matrix_disjoint.
Proof.
  intros ax ay bx by_ c Hb.
  apply segments_no_share_line_no_ib_meet.
  apply same_side_cut_no_share. exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Coherence: the two certificates are mutually exclusive.                *)
(* -------------------------------------------------------------------------- *)

Theorem same_side_excludes_dual_proper :
  forall ax ay bx by_ c,
    same_side_cutb ax ay bx by_ c = true ->
    dual_proper_cutb ax ay bx by_ c = false.
Proof.
  intros ax ay bx by_ c Hb.
  assert (Hz : 0 < cut_product ax ay bx by_ c)
    by (apply same_side_cutb_iff; exact Hb).
  unfold dual_proper_cutb.
  assert (Hf : Z.ltb (cut_product ax ay bx by_ c) 0 = false)
    by (apply Z.ltb_ge; lia).
  rewrite Hf. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions same_side_no_share.
Print Assumptions same_side_cut_no_share.
Print Assumptions decide_line_no_ib_meet.
Print Assumptions same_side_excludes_dual_proper.
