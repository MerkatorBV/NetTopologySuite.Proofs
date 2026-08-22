# Retire #65 — buffer and offset curves

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** —

## Question

#65 (Urgent) asks for parallel-curve correctness, joins, endcaps, topology,
`CurvePolygon` emission and oracle modes. The audit reads **MOSTLY**: eight of ten
asks satisfied, and the body's round-2 item 1 has landed since. Does it close, and
where does its residue go?

Satisfied (verify then cite): with-holes extraction now reduces to the *same*
single `face_twin_free` residual as the hole-free case
(`theories/ExtractHolesWellNoded.v`), and that residual is itself Qed via
`theories/FaceOrbitSep.v:154 face_twin_free_of_sep` — the chain is called
"discharged end-to-end" in `docs/face-twin-free-closure-plan.md` §1. Miter and
flat-cap assembly wired (`BufferAssembly.v : assemble_open_miter_chain`,
`BufferEndcap.v : flat_cap_ring_closed`). Curve ladder rungs 1–14, P1, P3,
`CurveBufferArea.v` green; the clothoid chain gives a simple-closed-curve
certificate under clearance > 2·|d|. Oracles `BUFFER_REGION`, `ARC_OFFSET_XY`,
`ARC_BUFFER_SIMPLE`, `ARC_OFFSET_FILTERED` all present. Honest negatives intact
(`BufferDepth*Counterexample.v`, `inner_offset_past_center_not_at_distance`,
`tangent_continuity_insufficient_for_offset`).

Residue to place:

1. Per-hypothesis disposition of `BufferCorrectness.v : buffer_correct_conditional`'s
   two named hypotheses (`H_valid`, `H_bridge`, lines 106-150) against the
   guard-only spine.
2. Round-join **assembly**: `CurveRoundJoin.v` proves `round_join_arc_valid` and
   `_connects`, but nothing wires them into `BufferAssembly`; plus the multi-edge
   two-sided open-chain walk.
3. Self-intersecting offset cleanup for non-convex inputs.
4. P2 Minkowski point-set semantics — **parked by decision**. Decide whether it
   becomes a documented non-goal rather than an issue, since filing it would
   re-open something deliberately closed.
