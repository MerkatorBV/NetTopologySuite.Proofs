(* ============================================================================
   NetTopologySuite.Proofs.JctSeamPack
   ----------------------------------------------------------------------------
   Require-Export facade for the co-required JCT seam clique (support ≥ 12).
   One import instead of the pack.

   Members: JordanRingKit · ConvexOffringSeam · JCTParityTransport ·
   JCTHalfOpenParity · JCTGenericStability · JCTLevelJump · JCTTrappedHalf.

   Full-pack importers (all 7) plus the near-clique theorem module
   JCTSeamAssembly (≥6 of 7) Require this facade.  RelateNG and Overlay-only
   leaves stay off it so the JCT cone does not leak sideways.

   Not JctSeamPack7 — one pack, this member set (highest savings).  Competing
   7-sets that swap JCTSeamAssembly / JCTEscapeDescent / JCTEastApproach /
   JCTCorridor stay as importers, not a second facade.

   Layer law (ADR-0001): overlay → topology.  JordanRingKit already
   Require-Exports Overlay before Jordan; this file Require-Exports the kit
   first, then the JCT seam modules in their existing dep order.  Real chain
   stays the rocq makefile / `_CoqProject.full`.

   topic: core
   claimId: none
   witness: none
   issue: #69

   No lemmas.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From NTS.Proofs Require Export
  JordanRingKit
  ConvexOffringSeam
  JCTParityTransport
  JCTHalfOpenParity
  JCTGenericStability
  JCTLevelJump
  JCTTrappedHalf.
