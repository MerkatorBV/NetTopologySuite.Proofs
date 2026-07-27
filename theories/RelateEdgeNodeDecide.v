(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeNodeDecide
   ----------------------------------------------------------------------------
   A COMPUTABLE exact classifier for the lineal DE-9IM interior/interior cell.

   RelateEdgeNodeStratum.v closed the last link of the exact-noding chain: a
   dual-proper integer cut populates the lineal DE-9IM II point-cell.  But that
   chain ended in a `Prop` (`dual_proper_cut`), not in something a consumer can
   RUN.  Every predicate along it is, however, a strict inequality between
   products of integer orientation determinants -- so the whole chain is
   decidable by integer sign tests, with no rounding anywhere.

   This module supplies the decision layer and ties off the arithmetic:

     - `dual_proper_cutb` -- the boolean test (two `Z.ltb`s on `cut_product`
       and `host_product`), with `dual_proper_cutb_iff` /
       `dual_proper_cutb_false_iff` and the sumbool `dual_proper_cut_dec`;
     - `decide_line_ii_point_cell` -- HEADLINE: the boolean returning `true` is
       enough to conclude the DE-9IM II point-cell, so the classifier is an
       exact, zero-rounding, RUNNABLE DE-9IM decision for integer segments;
     - `cut_host_products_fit_int128` -- the decision arithmetic itself fits
       signed 128-bit over the paper's `cmax` coordinate window: each product
       is a product of two determinants, hence bounded by `cmax^4 <= 2^127-1`,
       the same bound that governs the position comparator
       (RelateEdgePosOrder).

   Together with the ordering bricks, the whole lineal pipeline -- decide the
   crossing, locate the node, order the nodes, populate the matrix cell -- is
   exact integer arithmetic inside int128.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith Lia Bool Reals.
From NTS.Proofs Require Import Distance Orientation Segment
  RelateLineLine RelateNodingLineLine
  RelateIntDetBound RelateEdgePosOrder RelateEdgeInterParam
  RelateEdgeMultiNode RelateEdgeDualCross RelateEdgeNodeStratum.

Local Open Scope Z_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The boolean test.                                                      *)
(*                                                                            *)
(* `dual_proper_cut` is `cut_product < 0 /\ host_product < 0` -- two strict    *)
(* integer inequalities, so one `andb` of two `Z.ltb`s decides it exactly.     *)
(* -------------------------------------------------------------------------- *)

Definition dual_proper_cutb (ax ay bx by_ : Z) (c : ZCut) : bool :=
  andb (Z.ltb (cut_product ax ay bx by_ c) 0)
       (Z.ltb (host_product ax ay bx by_ c) 0).

Lemma dual_proper_cutb_iff :
  forall ax ay bx by_ c,
    dual_proper_cutb ax ay bx by_ c = true <-> dual_proper_cut ax ay bx by_ c.
Proof.
  intros ax ay bx by_ c.
  unfold dual_proper_cutb, dual_proper_cut, proper_cut.
  rewrite andb_true_iff, !Z.ltb_lt. reflexivity.
Qed.

Lemma dual_proper_cutb_false_iff :
  forall ax ay bx by_ c,
    dual_proper_cutb ax ay bx by_ c = false <-> ~ dual_proper_cut ax ay bx by_ c.
Proof.
  intros ax ay bx by_ c. split.
  - intros Hf Hp. apply dual_proper_cutb_iff in Hp. congruence.
  - intros Hn. destruct (dual_proper_cutb ax ay bx by_ c) eqn:E.
    + exfalso. apply Hn, dual_proper_cutb_iff. exact E.
    + reflexivity.
Qed.

(* The predicate is decidable (sumbool form, for callers that want a proof). *)
Lemma dual_proper_cut_dec :
  forall ax ay bx by_ c,
    {dual_proper_cut ax ay bx by_ c} + {~ dual_proper_cut ax ay bx by_ c}.
Proof.
  intros ax ay bx by_ c.
  destruct (dual_proper_cutb ax ay bx by_ c) eqn:E.
  - left. apply dual_proper_cutb_iff. exact E.
  - right. apply dual_proper_cutb_false_iff. exact E.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  HEADLINE: a runnable, exact DE-9IM II-cell classifier.                 *)
(* -------------------------------------------------------------------------- *)

Theorem decide_line_ii_point_cell :
  forall ax ay bx by_ c,
    dual_proper_cutb ax ay bx by_ c = true ->
    line_ii_point_cell (ptZ ax ay) (ptZ bx by_)
      (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)) ll_matrix_point_ii.
Proof.
  intros ax ay bx by_ c Hb.
  apply dual_proper_cut_line_ii_point_cell.
  apply dual_proper_cutb_iff. exact Hb.
Qed.

(* The node itself is available under the same boolean guard: it is interior
   (LSInt) on both segments. *)
Corollary decide_node_LSInt_both :
  forall ax ay bx by_ c,
    dual_proper_cutb ax ay bx by_ c = true ->
    seg_in_stratum LSInt (ptZ ax ay) (ptZ bx by_)
      (inter_ptZ ax ay bx by_ (c0x c) (c0y c) (c1x c) (c1y c)) /\
    seg_in_stratum LSInt (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c))
      (inter_ptZ ax ay bx by_ (c0x c) (c0y c) (c1x c) (c1y c)).
Proof.
  intros ax ay bx by_ c Hb.
  apply dual_proper_cut_LSInt_both.
  apply dual_proper_cutb_iff. exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  The decision arithmetic fits int128 over the cmax window.              *)
(*                                                                            *)
(* Each of `cut_product` / `host_product` is a product of two orientation      *)
(* determinants, so over the paper's coordinate window it is bounded by        *)
(* cmax^4 -- the same int128 budget that governs the position comparator.      *)
(* -------------------------------------------------------------------------- *)

Theorem cut_host_products_fit_int128 :
  forall ax ay bx by_ c,
    0 <= ax <= cmax -> 0 <= ay <= cmax ->
    0 <= bx <= cmax -> 0 <= by_ <= cmax ->
    0 <= c0x c <= cmax -> 0 <= c0y c <= cmax ->
    0 <= c1x c <= cmax -> 0 <= c1y c <= cmax ->
    Z.abs (cut_product ax ay bx by_ c) <= int128_max /\
    Z.abs (host_product ax ay bx by_ c) <= int128_max.
Proof.
  intros ax ay bx by_ c Hax Hay Hbx Hby Hc0x Hc0y Hc1x Hc1y.
  pose proof cmax_4th_le_int128 as H4.
  assert (Hnn : 0 <= cmax * cmax) by (unfold cmax; lia).
  split.
  - unfold cut_product. rewrite Z.abs_mul.
    pose proof (idet_abs_le_cmax_sq (c0x c) (c0y c) (c1x c) (c1y c) ax ay
                  Hc0x Hc0y Hc1x Hc1y Hax Hay) as H1.
    pose proof (idet_abs_le_cmax_sq (c0x c) (c0y c) (c1x c) (c1y c) bx by_
                  Hc0x Hc0y Hc1x Hc1y Hbx Hby) as H2.
    pose proof (Z.abs_nonneg (idet (c0x c) (c0y c) (c1x c) (c1y c) ax ay)).
    pose proof (Z.abs_nonneg (idet (c0x c) (c0y c) (c1x c) (c1y c) bx by_)).
    nia.
  - unfold host_product. rewrite Z.abs_mul.
    pose proof (idet_abs_le_cmax_sq ax ay bx by_ (c0x c) (c0y c)
                  Hax Hay Hbx Hby Hc0x Hc0y) as H1.
    pose proof (idet_abs_le_cmax_sq ax ay bx by_ (c1x c) (c1y c)
                  Hax Hay Hbx Hby Hc1x Hc1y) as H2.
    pose proof (Z.abs_nonneg (idet ax ay bx by_ (c0x c) (c0y c))).
    pose proof (Z.abs_nonneg (idet ax ay bx by_ (c1x c) (c1y c))).
    nia.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dual_proper_cutb_iff.
Print Assumptions dual_proper_cut_dec.
Print Assumptions decide_line_ii_point_cell.
Print Assumptions cut_host_products_fit_int128.
