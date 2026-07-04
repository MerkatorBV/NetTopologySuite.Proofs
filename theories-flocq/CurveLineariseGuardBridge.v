(* ============================================================================
   NetTopologySuite.Proofs.Flocq.CurveLineariseGuardBridge
   ----------------------------------------------------------------------------
   Issue #64 V-CP / CP_VALID: the EULER-FREE guard entry point for plugging
   linearised curve geometries into the overlay extraction machinery.

   theories/CurveLinearise.v already closes the purely-structural half of this
   ("every outer ring and hole of `to_geometry cg n` is closed for a valid
   `cg`") and explicitly flags the remainder as future work: "the structural
   prerequisite for plugging linearised curves into the `extract_rings_valid`
   / overlay machinery."  Separately, the H-bridge/Euler campaign's rung E-4
   (`theories-flocq/OverlayBridgeUnconditional.v`) now supplies exactly the
   GUARD-based (Euler-free) closure `extract_rings_valid_of_guards`: given
   `well_noded_darts`, `no_spurs`, `edge_2_connected`,
   `pairwise_no_proper_cross_twin_aware`, `no_horizontal_darts`, and
   `no_foreign_vertex_twin_aware` on a noded/labelled result graph -- NO
   `euler_characteristic` premise anywhere -- every extracted face is
   `valid_polygon`.  Per that file's own migration note, new call sites
   should prefer this `_of_guards` variant over the older
   `extract_rings_valid` / `extract_rings_valid_sep`.

   This file supplies exactly the missing wiring: instantiate
   `extract_rings_valid_of_guards` at the curve call site,
   `noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB)`, so a
   boolean overlay op run on two linearised `CurveGeometry` inputs extracts
   only `valid_polygon` faces whenever the six guard hypotheses hold on the
   result graph.

   This is a direct instantiation of the existing, already-Qed
   `extract_rings_valid_of_guards` -- it does not redefine, rename, or
   re-derive it, and adds no new axioms (its `Print Assumptions` footprint is
   exactly that theorem's).  No `euler_characteristic` / `H_bridge_premise`
   anywhere in THIS file: strictly Euler-free, guards only.

   Defined here:
     `to_geometry_result_valid_of_guards` -- guard-only validity of every
       extracted face of a boolean op over two linearised curve geometries
       (direct corollary of `OverlayBridgeUnconditional.extract_rings_valid_of_guards`).
     `to_geometry_result_valid_geometry_of_guards` -- the `valid_geometry`
       packaging of the above.

   DEFERRED (honest scope, unchanged by this file): discharging the six guard
   hypotheses themselves for a concrete curve-noding pipeline is untouched
   here; this file only closes the "linearised curve -> guard-based validity"
   wiring gap, not the guards' own provenance.  A with-holes companion needs
   an `extract_rings_valid_holes_of_guards` counterpart that does not yet
   exist (the older, still-Qed `extract_rings_valid_holes_sep` -- Euler-free
   via a single `twins_in_different_faces` guard rather than this file's
   six-guard set -- is the nearest existing analogue; see the shared-lemma
   request in the accompanying PR/issue note).

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import List.
From NTS.Proofs        Require Import Overlay CurveGeometry ExtractFaces Dart
                                       VertexGeneralPosition NoShortFaces
                                       EdgeConnectivity FaceTwinAware
                                       HBridgeCoreSlice.
From NTS.Proofs.Flocq  Require Import OverlayBridge OverlayBridgeUnconditional.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* §1  Guard-only (Euler-free) validity for a boolean op over two linearised   *)
(*     curve geometries.                                                      *)
(* -------------------------------------------------------------------------- *)

Theorem to_geometry_result_valid_of_guards :
  forall (cgA cgB : CurveGeometry) (nA nB : nat) (op : BooleanOp),
    well_noded_darts
      (result_edges op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB))) ->
    no_spurs
      (result_darts op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB))) ->
    edge_2_connected
      (result_edges op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB))) ->
    pairwise_no_proper_cross_twin_aware
      (darts_of (result_edges op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB)))) ->
    no_horizontal_darts
      (darts_of (result_edges op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB)))) ->
    no_foreign_vertex_twin_aware
      (darts_of (result_edges op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB)))) ->
    forall poly,
      In poly (extract_faces op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB))) ->
      valid_polygon poly.
Proof.
  intros cgA cgB nA nB op Hwn Hns H2ec Hpw Hnh Hnfv poly Hin.
  exact (extract_rings_valid_of_guards op (to_geometry cgA nA) (to_geometry cgB nB)
           Hwn Hns H2ec Hpw Hnh Hnfv poly Hin).
Qed.

Corollary to_geometry_result_valid_geometry_of_guards :
  forall (cgA cgB : CurveGeometry) (nA nB : nat) (op : BooleanOp),
    well_noded_darts
      (result_edges op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB))) ->
    no_spurs
      (result_darts op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB))) ->
    edge_2_connected
      (result_edges op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB))) ->
    pairwise_no_proper_cross_twin_aware
      (darts_of (result_edges op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB)))) ->
    no_horizontal_darts
      (darts_of (result_edges op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB)))) ->
    no_foreign_vertex_twin_aware
      (darts_of (result_edges op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB)))) ->
    valid_geometry
      (extract_faces op (noded_labeled_graph (to_geometry cgA nA) (to_geometry cgB nB))).
Proof.
  intros cgA cgB nA nB op Hwn Hns H2ec Hpw Hnh Hnfv.
  unfold valid_geometry. intros poly Hin.
  apply (to_geometry_result_valid_of_guards cgA cgB nA nB op Hwn Hns H2ec Hpw Hnh Hnfv poly Hin).
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Audit footprint -- must match `extract_rings_valid_of_guards` exactly  *)
(*     (no new axioms introduced by this file).                              *)
(* -------------------------------------------------------------------------- *)

Print Assumptions to_geometry_result_valid_of_guards.
Print Assumptions to_geometry_result_valid_geometry_of_guards.
