(* ==========================================================================
   BaseToTipHeadline.v

   [H-bridge attack, C-3e step C] The ALONG-DART HEADLINE: base/tip corner
   sample -> corridor ride -> straddle target at height `my`, composed by
   transitivity.  The straddle pair `(edge_x_at d my ± ef, my)` is reached
   as a west/east corridor point once `ef` sits below the corridor
   half-threshold (`corridor_absorbs_ef` / `corridor_ef_inherits_clearance`).

   Also packages `corridor_safe_for_ef*` discharge, the ring-dart / foreign
   face_transport_premise apply hooks, and a concrete descending-dart
   sample exercise.

   The algebraic bypass (`HandoffConnector.handoff_base_bridge_*`) reuses
   the corner connector's own sample as the corridor endpoint at the bridge
   height; the handoff chord (`handoff_base_to_corridor_west_convex`) is
   the general alternative when heights differ.

   No `Admitted` / `Axiom` / `Parameter`; allowlist axioms only.


   SPLIT (2026-08-16): the C-3e step-C layers now live in five modules --
   BaseToTipDelta (bridge deltas/heights + ef-matched corner deltas;
   gains its own PA footer per the no-footer audit rule),
   BaseToTipAlongDart (the west/east along-dart headlines),
   BaseToTipCorridorSafe (_clear packaging + corner samples +
   corridor_safe_for_ef* discharge), BaseToTipTransportHooks (the
   face_transport_premise apply hooks + connected straddle headlines),
   BaseToTipSample (the concrete descending-dart exercise).  This file
   is the Require Export umbrella: every name is re-exported, so
   importers are unaffected.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From NTS.Proofs Require Export BaseToTipDelta.
From NTS.Proofs Require Export BaseToTipAlongDart.
From NTS.Proofs Require Export BaseToTipCorridorSafe.
From NTS.Proofs Require Export BaseToTipTransportHooks.
From NTS.Proofs Require Export BaseToTipSample.
