(* ============================================================================
   NetTopologySuite.Proofs.RelateNG
   ----------------------------------------------------------------------------
   Issue #67 S13: full RelateNG pipeline integration — re-export umbrella.

   The former 1 750-line monolith was split (2026-08) into layered
   modules; this file re-exports them all, so existing
   `Require Import RelateNG` clients (RelatePrepared.v) are unaffected.
   The original section banners are preserved inside the split files, and
   the meso-audit B6 untangle (rect and triangle lanes were interleaved:
   `rect_pair_regime` sat inside the triangle block) is executed by the
   Core layout.  Layer map:

     - RelateNGCore.v        strata + rect/triangle regime classifiers +
         the top-level `relate` dispatch (`rect_geometry_bounds`,
         `rect_pair_regime`, `rects_relate`; `triangle_geometry`,
         `triangle_pair_regime`, `tris_relate`; `relate` + fidelity
         lemmas and the line fallback).
     - RelateNGContains.v    TPR_Contains regime correctness
         (`triangle_pair_regime_contains`; whole-boundary containment
         `contains_b_ring_inside` / `contains_b_ring_strictly_inside`
         via TriangleContainmentConvex).
     - RelateNGOverlap.v     TPR_Overlap regime at bar 1 (#570 / 522-b)
         (`triangle_pair_regime_overlap`; soundness
         `overlap_b_partial_overlap` via a centroid nudge).
     - RelateNGDisjoint.v    TPR_Disjoint regime at bar 1 (#571 / 522-c)
         (`triangle_pair_regime_disjoint`; soundness
         `separated_b_triangles_separated` via a supporting edge).
     - RelateNGTouchVertex.v TPR_TouchVertex regime at bar 1 (#572 / 522-i)
         (`triangle_pair_regime_touchvertex`; soundness
         `touch_vertex_b_triangles_touch` via a line through the
         shared vertex).
     - RelateNGTouch.v       shared-edge touch regime
         (`triangles_touch_on_shared_edge` + detector agreement
         `triangle_pair_regime_touch`; strict interior separation
         `touch_triangle_pair_strict_ii_no_common`;
         `touch_int_ext_exclusion{,_weak}`; `relate_triangle_touch`).
     - RelateNGTouchRED.v    RED refutation: the parity SInt sets of two
         CCW shared-edge triangles overlap at the vertex-grazing
         p = (-1,1), so guard-free II separation is FALSE
         (`touch_triangle_ii_separation_not_unconditional`).
     - RelateNGTouchCells.v  DE-9IM cells for the touch regime: EE/II/BB
         cells, the JCT seam lift
         (`point_set_characterises_geometric_interior`), the guarded II
         cell via the seam, the unconditional geometric-interior
         separation, and the capstones
         (`touch_triangles_regime_cells_ii_bb_ee`).
     - RelateNGRect.v        rect regime cells + dispatch fidelity
         (touch pins, `relate_on_rects_dispatches`, overlap fill facts,
         `touch_rect_pair_{ee,ii}_cell`, BB point constructor, examples).

   Provides (unchanged public surface): the top-level relate computation and
   matrix assembly, integrating the MOD2 boundary policy (RelateBoundary),
   the area-line / area-area regime cases + general strata, dim assignment
   with Jordan soundness hooks, and the prepared cache wrapper (delegates to
   RelatePrepared).

   No `Admitted`, no `Axiom`, no `Parameter`.  Per-theorem audit footprints
   (`Print Assumptions`) live in the split files, next to their theorems.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Claude
   ========================================================================== *)

From NTS.Proofs Require Export
  RelateNGCore
  RelateNGContains
  RelateNGOverlap
  RelateNGDisjoint
  RelateNGTouchVertex
  RelateNGTouch
  RelateNGTouchRED
  RelateNGTouchCells
  RelateNGRect.
