(* C-3e open design note (post-PR#339)
   Target for face_transport_premise: (edge_x_at d my - ef, my) and +ef.
   Question: corridor.safe_offset guarantees δ < threshold, but ef comes from
   straddle_side_core with no explicit relation yet.
   Proposed closure: prove ∃ ε₀ > 0, ∀ ef < ε₀, corridor argument still holds
   (standard "sufficiently small" + triangle-inequality chaining). *)
(* ## C-3e-4 (along-dart headline) – IN PROGRESS
   - [x] internal corner bridge via CornerCorridorBridge (PR#339)
   - [ ] connect to exact (edge_x_at … ±ef, my) targets ← you are here
   - Proposed: Lemma `corridor_safe_for_ef` + `corridor_absorbs_ef` bypass application *)