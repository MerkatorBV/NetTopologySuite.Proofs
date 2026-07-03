(* C-3e open design note (post-PR#339)
   Both tracks currently connect only d's own two corner samples via corridor.
   Target for face_transport_premise: (edge_x_at d my - ef, my) and +ef.
   Question: corridor.safe_offset guarantees δ < threshold, but ef comes from
   straddle_side_core with no explicit relation yet.
   Proposed closure: prove ∃ ε₀ > 0, ∀ ef < ε₀, corridor argument still holds
   (standard "sufficiently small" + triangle-inequality chaining). *)