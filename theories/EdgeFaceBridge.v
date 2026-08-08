(* ==========================================================================
   NetTopologySuite.Proofs.EdgeFaceBridge
   ----------------------------------------------------------------------------
   extract_rings_valid R5, H_bridge rung: link graph cut edges to rotation-system
   face orbits — re-export umbrella.

   Target (forward implication only):

     edge_2_connected E -> twins_in_different_faces (darts_of E)

   Equivalently (contrapositive core): if a proper dart d shares an `fstep`
   orbit with its twin, the undirected edge is a cut edge (`same_face_twin_is_cut`
   in the Capstone — the planar same-face⇒bridge seam is the named premise
   `H_bridge_premise`, discharged in HBridgeEuler.v).

   The former monolith was split (2026-08) into four layered modules; this
   file re-exports them all, so existing `Require Import EdgeFaceBridge`
   clients are unaffected.  Original §-numbers are preserved inside the
   split files (docs/extract-faces-bridge.md §19, verified-claims row).

   Layer map:

     - EdgeFaceBridgeIncidence.v   §1–§2   dart↔edge incidence + face-walk linkage
     - EdgeFaceBridgeTwinPath.v    §3      twin step / first_twin / E_minus prefix loop
     - EdgeFaceBridgeBarrier.v     §3b-ii–iii  singleton-fan + carrier exclusivity / not_adj
     - EdgeFaceBridgeCapstone.v    §3b-v, §4, §4b  H_bridge_premise + packaging + converse

   Layers consumed (via the split modules):
     - EdgeConnectivity.v   (reachable / is_cut_edge / edge_2_connected)
     - FaceOrbitSep.v       (same_face / twins_in_different_faces)
     - FaceChain.v          (dart_walk / face_chain)
     - ExtractFaces.v       (face_period)
     - VertexGeneralPosition.v (well_noded_darts -> fan_ok)

   No `Admitted` / `Axiom` / `Parameter` in this stack; `Print Assumptions`
   lives next to the theorems in each split file.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude / Grok
   ========================================================================== *)

From NTS.Proofs Require Export
  EdgeFaceBridgeIncidence
  EdgeFaceBridgeTwinPath
  EdgeFaceBridgeBarrier
  EdgeFaceBridgeCapstone.
