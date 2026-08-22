# Retire #64 — arc primitives

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** —

## Question

#64 (Immediate) asks for arc length, sweep, point-on-arc, in-circle, arc-line and
arc-arc intersection, plus oracle modes. The audit reads it **MOSTLY** satisfied:
three of the body's four round-2 items have closed since the body was written.
Does it close, and where does its residue go?

Satisfied (verify then cite): D-PT distance clamps fully closed
(`fallback_ends_lower`, `arc_dot_max_at_endpoint`); span discharge unconditional
for all sweeps including reflex (`theories/ArcSpanAtan2.v`); the arc-arc quartic —
the body's own "deepest open work" — closed in `theories/ArcArcQuartic.v`
(`arc_arc_intersects_of_atan2_radical_span:316`). Asks 1/2/4b/5a green via
`ArcLength.v`, `Atan2.v`/`AngleBetween.v`, `InCircle_b64_exact.v`,
`ArcLineIntersect_b64_exact.v` (`verified-claims.md:480-483`). New micro-claims
64-b/c/d/e exist and are not in the body at all.

Residue to place, per the closure bar — subtask, new epic, or documented non-goal:

1. **V-CP true-region (Jordan) soundness** — `CurvePolygonValid.v` has only the
   inscribed-chord floor, and #376's survey says the triangle-only toolkit cannot
   discharge it: genuinely new ray-vs-arc crossing geometry is needed. Flagged
   high-risk; this one plausibly deserves its own epic rather than a subtask.
2. `ArcOverlay.v : arc_overlay_correct_chord_approx` — two bridge hypotheses.
3. The permanent interface caveat for float modes `ARC_DISTANCE`,
   `POINT_IN_CURVE_RING`, `RING_ORIENTATION` (transcendental sweep clamp) — a
   documented convention, not closable work. Decide where it is written down so
   it stops reading as residue.
