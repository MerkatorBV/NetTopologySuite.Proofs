(* ============================================================================
   NetTopologySuite.Proofs.RelateEdgeNodeStratum
   ----------------------------------------------------------------------------
   Wiring the exact integer-coordinate noding node into the lineal DE-9IM
   point-set classification.

   The exact-noding stack (RelateEdgePosOrder -> ... -> RelateEdgeDualCross /
   RelateEdgeSetNoding) produces, from an integer-coordinate proper cut, an
   intersection node `inter_ptZ` and proves it is `between_strict` on BOTH
   crossing segments (`dual_proper_node_on_both_segments`).  Separately,
   RelateNodingLineLine.v carries the lineal DE-9IM point-set spec, where a
   segment's interior stratum is exactly `between_strict`
   (`seg_in_stratum LSInt := between_strict`) and endpoints are the boundary
   stratum -- a CLEAN classification for line segments (no half-open-ring
   pathology; that pathology is specific to AREA operands and is deferred to
   #68, the full 9-cell `geom_de9im_pointset` capstone).

   Those two worlds were not connected: the existing II-cell theorem
   (`segments_proper_cross_line_ii_cell`) is stated for the REAL-analytic
   proper-cross notion, not for the integer cut the noding pipeline emits.
   This module supplies the bridge:

     - `dual_proper_cut_LSInt_both`: the integer node sits in the LSInt
       (interior) stratum of BOTH edges;
     - `dual_proper_cut_int_int_share`: hence the two segments share an
       interior-interior point;
     - `dual_proper_cut_line_ii_point_cell`: hence an exact integer proper cut
       POPULATES the lineal DE-9IM interior/interior point-cell
       (`line_ii_point_cell ... ll_matrix_point_ii`).

   So the exact-noding pipeline is now attached to the DE-9IM matrix on the
   lineal side, with zero rounding and without touching the deferred area seam.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From Stdlib Require Import ZArith Reals Lra List Lia.
From NTS.Proofs Require Import Distance Orientation Segment
  RelateLineLine RelateNodingLineLine
  RelateEdgeInterParam RelateEdgeMultiNode RelateEdgeDualCross.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  The integer node lands in the interior (LSInt) stratum of both edges.  *)
(* -------------------------------------------------------------------------- *)

Theorem dual_proper_cut_LSInt_both :
  forall ax ay bx by_ c,
    dual_proper_cut ax ay bx by_ c ->
    seg_in_stratum LSInt (ptZ ax ay) (ptZ bx by_)
      (inter_ptZ ax ay bx by_ (c0x c) (c0y c) (c1x c) (c1y c)) /\
    seg_in_stratum LSInt (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c))
      (inter_ptZ ax ay bx by_ (c0x c) (c0y c) (c1x c) (c1y c)).
Proof.
  intros ax ay bx by_ c Hcut.
  destruct (dual_proper_node_on_both_segments ax ay bx by_ c Hcut)
    as [HAB HCD].
  unfold seg_in_stratum. split; [ exact HAB | exact HCD ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Interior-interior share and the DE-9IM II point-cell.                  *)
(* -------------------------------------------------------------------------- *)

Corollary dual_proper_cut_int_int_share :
  forall ax ay bx by_ c,
    dual_proper_cut ax ay bx by_ c ->
    segments_share (ptZ ax ay) (ptZ bx by_)
      (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)).
Proof.
  intros ax ay bx by_ c Hcut.
  destruct (dual_proper_cut_LSInt_both ax ay bx by_ c Hcut) as [HAB HCD].
  eapply int_int_share; [ exact HAB | exact HCD ].
Qed.

(* HEADLINE: an exact integer proper cut populates the lineal DE-9IM II
   point-cell -- the exact-noding pipeline attached to the DE-9IM matrix. *)
Theorem dual_proper_cut_line_ii_point_cell :
  forall ax ay bx by_ c,
    dual_proper_cut ax ay bx by_ c ->
    line_ii_point_cell (ptZ ax ay) (ptZ bx by_)
      (ptZ (c0x c) (c0y c)) (ptZ (c1x c) (c1y c)) ll_matrix_point_ii.
Proof.
  intros ax ay bx by_ c Hcut.
  destruct (dual_proper_cut_LSInt_both ax ay bx by_ c Hcut) as [HAB HCD].
  unfold line_ii_point_cell, ll_matrix_point_ii. simpl.
  eapply line_cell_ok_dim0; [ exact HAB | exact HCD ].
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions dual_proper_cut_LSInt_both.
Print Assumptions dual_proper_cut_int_int_share.
Print Assumptions dual_proper_cut_line_ii_point_cell.
