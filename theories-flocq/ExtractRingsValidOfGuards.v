(* ============================================================================
   NetTopologySuite.Proofs.Flocq.ExtractRingsValidOfGuards

   [H-bridge / Euler campaign, issue #67 track] `extract_rings_valid`
   (OverlayBridge.v Section 8) closes the DCEL ring-assembly obligation for
   RelateNG / overlay under two raw NAMED hypotheses: `euler_characteristic`
   on the result edge set, and on every one-edge-removed sub-arrangement.
   `theories/EulerUnconditional.v` (rung E-3b) has since proved
   `euler_characteristic_holds`: the planar Euler identity follows OUTRIGHT
   from five geometric/noding guards a snap-rounded overlay arrangement
   already maintains (`NoDup`, `no_twin_dup`, `fan_ok`,
   `pairwise_no_proper_cross_twin_aware`, `no_horizontal_darts`,
   `no_foreign_vertex_twin_aware`).

   This file threads that unconditional result into `extract_rings_valid`:
   `extract_rings_valid_of_guards` replaces BOTH `euler_characteristic`
   premises by the same guards, stated once for the top-level result edge
   set.  The two Euler obligations are discharged by:
     - the top-level one: `euler_characteristic_holds` applied directly;
     - the per-removed-edge one: the guards are hereditary under `E_minus`
       (`NoDup_filter`, `no_twin_dup_E_minus`, `fan_ok_E_minus`, and the
       three `_incl` lemmas from `EulerUnconditional.v` transported along
       `darts_of_incl _ _ (E_minus_incl _ e)`) -- exactly the same
       bookkeeping `EulerUnconditional.euler_characteristic_holds`'s own
       induction step already performs one edge at a time.

   No new geometric content: this is a pure composition of two already-Qed
   theorems.  Euler-free from the caller's point of view -- the only
   premises are the five standing guards plus the pre-existing structural
   obligations (`well_noded_darts`, `no_spurs`, `edge_2_connected`) that
   `extract_rings_valid` already required.

   No `Admitted` / `Axiom` / `Parameter`.  Same Category C Flocq lineage as
   `OverlayBridge.v` (transitive `Classical_Prop.classic` via
   `HobbyTheorem_b64`'s `snap_round_segments`), already listed in
   docs/audit-exceptions.txt for that file's consumers.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals List Arith Lia Bool Wf_nat.
From NTS.Proofs Require Import Distance Overlay Dart DartNextSpec
                               EdgeConnectivity EulerCoreInduction
                               ArrangementEMinus FaceTwinAware
                               HBridgeCoreSlice EulerUnconditional
                               VertexGeneralPosition NoShortFaces ExtractFaces.
From NTS.Proofs.Flocq Require Import OverlayBridge.

Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* The guards-only headline.                                                   *)
(* -------------------------------------------------------------------------- *)

Theorem extract_rings_valid_of_guards :
  forall (op : BooleanOp) (A B : Geometry),
    well_noded_darts (result_edges op (noded_labeled_graph A B)) ->
    no_spurs (result_darts op (noded_labeled_graph A B)) ->
    edge_2_connected (result_edges op (noded_labeled_graph A B)) ->
    NoDup (result_edges op (noded_labeled_graph A B)) ->
    no_twin_dup (result_edges op (noded_labeled_graph A B)) ->
    (forall v : Point,
       fan_ok (outgoing v (darts_of (result_edges op (noded_labeled_graph A B))))) ->
    pairwise_no_proper_cross_twin_aware
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    no_horizontal_darts (darts_of (result_edges op (noded_labeled_graph A B))) ->
    no_foreign_vertex_twin_aware
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    forall poly,
      In poly (extract_faces op (noded_labeled_graph A B)) ->
      valid_polygon poly.
Proof.
  intros op A B Hwn Hns H2ec Hnd Hntd Hfan Hpw Hnh Hnfv.
  apply extract_rings_valid.
  - exact Hwn.
  - exact Hns.
  - exact H2ec.
  - apply euler_characteristic_holds; assumption.
  - intros e Hin.
    assert (HdinclEd :
              incl (darts_of (E_minus (result_edges op (noded_labeled_graph A B)) e))
                   (darts_of (result_edges op (noded_labeled_graph A B)))).
    { apply darts_of_incl. apply E_minus_incl. }
    apply euler_characteristic_holds.
    + unfold E_minus. apply NoDup_filter. exact Hnd.
    + apply no_twin_dup_E_minus. exact Hntd.
    + intro v. apply fan_ok_E_minus. exact Hfan.
    + exact (pairwise_no_proper_cross_twin_aware_incl _ _ HdinclEd Hpw).
    + exact (no_horizontal_darts_incl _ _ HdinclEd Hnh).
    + exact (no_foreign_vertex_twin_aware_incl _ _ HdinclEd Hnfv).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions extract_rings_valid_of_guards.
