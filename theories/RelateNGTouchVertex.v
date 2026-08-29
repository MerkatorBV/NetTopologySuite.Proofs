(* ============================================================================
   NetTopologySuite.Proofs.RelateNGTouchVertex
   ----------------------------------------------------------------------------
   Issue #572 / #522 claimId 522-i: TPR_TouchVertex reachable at relate
   bar level 1.

   `touch_vertex_b` (RelateNGCore) is a sound-but-partial certificate:
   both triangles CCW, exactly one A-vertex is a B-vertex, and a line
   through that vertex — normal = the sum of one triangle's remaining
   legs — puts those remaining vertices strictly on the positive side
   and the other triangle's remaining vertices strictly on the negative
   side.  The side function is affine, so the closed regions meet only
   at the shared vertex.

   Earlier classifier branches are derived false (not assumed).  Obtuse-
   at-v pairs and partial-edge kisses still decline — completeness of
   leftover declines is #577.

   Frozen anchors stay untouched: `touch_int_ext_exclusion` and the
   II-guard maximality refutation.  `triangles_touch_on_shared_edge`
   is not referenced.

   The affine-side / barycentric-lift *pattern* is shared with the
   disjoint certificate; the helpers are not.  Disjoint uses `cross` /
   `opposite_sides_b` on an existing edge.  Vertex-touch uses `side_dot`
   against a constructed normal through `v` — the line need not be an
   edge.

   SPLIT: RelateNGTouchVertexCone.v holds the unpackers, affine cone
   uniqueness, and `touch_vertex_b_triangles_touch`.
   RelateNGTouchVertexRegime.v holds the earlier-branch exclusions,
   headlines, and ticket pins.  This file is the Require Export
   umbrella: every name is re-exported, so importers are unaffected.

   WITNESS topic: relate · claimId: 522-i · witness: 522-i-touchvertex-bar1
   macro: relate
   lane: proofs
   issue: #572 / #522
   ADR-0004: not a remint. 522-i is the existing #572 ticket id.

   No `Admitted`, no `Axiom`, no `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Cursor Agent
   ========================================================================== *)

(* WITNESS {"claimId":"522-i","topic":"relate","lemma":"triangle_pair_regime_touchvertex","title":"TPR_TouchVertex reachable at relate bar 1 via a line-through-vertex certificate","file":"theories/RelateNGTouchVertex.v","witness":"522-i-touchvertex-bar1","board":"#572"} *)

From NTS.Proofs Require Export RelateNGTouchVertexCone.
From NTS.Proofs Require Export RelateNGTouchVertexRegime.
