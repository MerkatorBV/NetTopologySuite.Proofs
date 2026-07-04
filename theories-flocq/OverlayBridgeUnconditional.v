(* ==========================================================================
   OverlayBridgeUnconditional.v

   [H-bridge / Euler campaign, rung E-4] RING EXTRACTION WITHOUT THE
   EULER HYPOTHESES: `extract_rings_valid`'s two `euler_characteristic`
   clauses existed solely to feed `H_bridge_premise_from_euler`; with
   the premise now a THEOREM of the geometric/noding guards
   (`WalkResidualDischarge.H_bridge_premise_holds`, E-2c), the headline
   restates with the guards in their place -- every hypothesis is now a
   combinatorial or geometric invariant of the snap-rounded overlay
   arrangement itself, none is a global topological identity.

   In one sentence: `extract_rings_valid_of_guards` is the Euler-free
   strengthening of the banked theorem, obtained after discharging
   `euler_characteristic` via the guard set (E-3b, PR #361).

   The banked `extract_rings_valid` is untouched; this is a corollary
   at its exact use shape.  MIGRATION NOTE: new call sites should
   prefer this `_of_guards` variant -- it is strictly stronger (no
   topological hypotheses) and its guards are the invariants the
   snap-rounding pipeline already maintains.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List.
From NTS.Proofs Require Import Distance Overlay OverlayGraph EdgeConnectivity
                               Dart DartNextSpec ExtractFaces EdgeFaceBridge
                               NoShortFaces FaceTwinAware VertexGeneralPosition
                               FaceOrbitSep HBridgeCoreSlice WalkPremiseBridge
                               WalkResidualDischarge.
From NTS.Proofs.Flocq Require Import OverlayBridge.

Import ListNotations.

Theorem extract_rings_valid_of_guards :
  forall (op : BooleanOp) (A B : Geometry),
    well_noded_darts (result_edges op (noded_labeled_graph A B)) ->
    no_spurs (result_darts op (noded_labeled_graph A B)) ->
    edge_2_connected (result_edges op (noded_labeled_graph A B)) ->
    pairwise_no_proper_cross_twin_aware
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    no_horizontal_darts
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    no_foreign_vertex_twin_aware
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    forall poly,
      In poly (extract_faces op (noded_labeled_graph A B)) ->
      valid_polygon poly.
Proof.
  intros op A B Hwn Hns H2ec Hpw Hnh Hnfv poly Hin.
  assert (Hfan : forall v : Point,
            fan_ok (outgoing v
                      (darts_of (result_edges op (noded_labeled_graph A B)))))
    by (intro v; apply well_noded_fan_ok; exact Hwn).
  assert (Hbr : H_bridge_premise (result_edges op (noded_labeled_graph A B)))
    by (apply H_bridge_premise_holds; assumption).
  exact (extract_faces_valid_sep op (noded_labeled_graph A B) Hwn Hns
           (H_bridge_well_noded (result_edges op (noded_labeled_graph A B))
              Hbr Hwn Hns H2ec) poly Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Euler-hypothesis-free ring extraction; allowlist only.        *)
(* -------------------------------------------------------------------------- *)

Print Assumptions extract_rings_valid_of_guards.
