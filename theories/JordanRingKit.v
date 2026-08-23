(* ============================================================================
   NetTopologySuite.Proofs.JordanRingKit
   ----------------------------------------------------------------------------
   Require-Export facade for the co-required PIP + overlay + Jordan seam
   clique (support ≥ 12).  One import instead of the pack.

   Members: Distance · Overlay · PointInRingCorrect · PointInRingTangents ·
   JordanCurveSeam · JCT · JCT_OnEdgeCounterexample.

   Full-pack importers (all 7) plus near-clique theorem modules (≥6 of 7,
   or ≥5 already on JCT) Require this facade.  RelateNG and Overlay-only
   leaves stay off it so the JCT cone does not leak sideways.

   Layer law (ADR-0001): overlay → topology.  This file Require-Exports
   Overlay before Jordan; Overlay.v itself is unchanged (no Overlay↔Jordan
   cycle).  Real chain stays the rocq makefile / `_CoqProject.full`.

   No lemmas.  No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From NTS.Proofs Require Export
  Distance
  Overlay
  PointInRingCorrect
  PointInRingTangents
  JordanCurveSeam
  JCT
  JCT_OnEdgeCounterexample.
