(* ==========================================================================
   OverlayBridgeUnconditionalHoles.v

   [H-bridge / Euler campaign, rung E-4 companion] RING EXTRACTION WITH
   HOLES, WITHOUT THE EULER HYPOTHESES.

   `OverlayBridgeUnconditional.extract_rings_valid_of_guards` restated the
   hole-free `extract_rings_valid` (theories-flocq/OverlayBridge.v §8) with
   its two `euler_characteristic` clauses discharged by the geometric/noding
   guard set (`WalkResidualDischarge.H_bridge_premise_holds`, E-2c). This
   file is the WITH-HOLES companion: `OverlayBridge.extract_rings_valid_holes`
   (itself explicitly commented there as the "With-holes companion" to the
   hole-free headline) threads the identical two Euler clauses unchanged,
   alongside the oracle well-formedness + `hole_inside_outer` nesting
   clauses. Swapping in the guard-derived `H_bridge_premise_holds` exactly as
   the hole-free rung did yields the same strengthening here: every
   hypothesis of the with-holes headline is now a combinatorial or geometric
   invariant of the snap-rounded overlay arrangement itself (or, for
   `hole_inside_outer`, the pre-existing single named JCT/nesting residual)
   -- none is a global topological identity.

   `hole_inside_outer` is left untouched as a named hypothesis: it is the
   point-set nesting bridge (the same JCT-shaped seam ExtractRingsShell.v /
   valid_polygon_noded_shell isolate at the ring-algebra layer), not a piece
   of the Euler/genus-0 argument this rung retires. No new topology is
   introduced here; this is a pure re-derivation at the guard-only premise.

   The banked `extract_rings_valid_holes` is untouched; this is a corollary
   at its exact use shape. MIGRATION NOTE: new with-holes call sites should
   prefer this `_of_guards` variant for the same reason as the hole-free one
   -- it is strictly stronger (no topological hypotheses beyond the named
   nesting residual) and its guards are the invariants the snap-rounding
   pipeline already maintains.

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
                               WalkResidualDischarge RingExtract FaceChain
                               FacePolygonHoles ExtractFacesHoles.
From NTS.Proofs.Flocq Require Import OverlayBridge.

Import ListNotations.

Theorem extract_rings_valid_holes_of_guards :
  forall (hassign : Dart -> list Dart) (op : BooleanOp) (A B : Geometry),
    well_noded_darts (result_edges op (noded_labeled_graph A B)) ->
    no_spurs (result_darts op (noded_labeled_graph A B)) ->
    edge_2_connected (result_edges op (noded_labeled_graph A B)) ->
    pairwise_no_proper_cross_twin_aware
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    no_horizontal_darts
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    no_foreign_vertex_twin_aware
      (darts_of (result_edges op (noded_labeled_graph A B))) ->
    (forall d, In d (result_darts op (noded_labeled_graph A B)) ->
       forall h, In h (hassign d) ->
         In h (result_darts op (noded_labeled_graph A B))) ->
    (forall d, In d (result_darts op (noded_labeled_graph A B)) ->
       forall h, In h (hassign d) ->
       hole_inside_outer
         (ring_of_chain (face_chain (result_darts op (noded_labeled_graph A B)) d
                           (face_period (result_darts op (noded_labeled_graph A B)) d)))
         (hole_ring_of (result_darts op (noded_labeled_graph A B))
            (h, face_period (result_darts op (noded_labeled_graph A B)) h))) ->
    forall poly,
      In poly (extract_faces_holes hassign op (noded_labeled_graph A B)) ->
      valid_polygon poly.
Proof.
  intros hassign op A B Hwn Hns H2ec Hpw Hnh Hnfv Hwf Hinside poly Hin.
  assert (Hfan : forall v : Point,
            fan_ok (outgoing v
                      (darts_of (result_edges op (noded_labeled_graph A B)))))
    by (intro v; apply well_noded_fan_ok; exact Hwn).
  assert (Hbr : H_bridge_premise (result_edges op (noded_labeled_graph A B)))
    by (apply H_bridge_premise_holds; assumption).
  exact (extract_faces_holes_valid_sep hassign op (noded_labeled_graph A B) Hwn Hns
           (H_bridge_well_noded (result_edges op (noded_labeled_graph A B))
              Hbr Hwn Hns H2ec)
           Hwf Hinside poly Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit.  Euler-hypothesis-free with-holes ring extraction; allowlist   *)
(* only.                                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions extract_rings_valid_holes_of_guards.
