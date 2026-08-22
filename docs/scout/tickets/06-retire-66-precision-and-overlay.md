# Retire #66 — precision models, snap rounding, OverlayNG

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** —

## Question

#66 (Urgent) asks for precision models, snap-rounding and OverlayNG/relate
soundness. The audit reads **MOSTLY**: six of eight asks satisfied and holding.
Does it close, and where does its residue go?

Satisfied (verify then cite): C1 grid-exactness
(`PassesThrough_b64_grid_exact.v`, now five layered modules plus umbrella),
snap-rounding idempotence (`SnapRounding_b64.v`), boolean overlay semantics
(`Overlay.v`, `OverlayGraph.v`), Euler hypotheses discharged
(`OverlayBridgeUnconditional.v : extract_rings_valid_of_guards`,
`_holes_of_guards`), `RingArea979.v` plus `HOLE_PRECISION_AUDIT` /
`HOLES_SURVIVE_PRECISION`, and `CURVE_SNAP_DECISION` /
`CURVE_SNAP_INVARIANTS_EXACT` in the oracle.

Note the interesting one: the body's remaining item 3 (guard-discharge audit)
**is delivered**, as `docs/guard-discharge-audit.md`, and it is an honest
*negative* — none of the five guards are free corollaries of snap-rounding, guard
4 is refuted outright by
`theories-flocq/SnapRoundingGuardAudit.v : snap_can_introduce_horizontal_dart`.
A delivered negative still satisfies the ask; say so explicitly in the closure
comment so it is not mistaken for unfinished work.

Residue to place:

1. **C1 width extension to 2²⁵** (`PassesThrough_b64_grid_exact.v:69-75`,
   `audit-rgr-comparison.md` P6) — needs exact integer-determinant comparison;
   survived a 1.7M-trial sweep but is UNPROVEN (`verified-claims.md:265`).
2. Unconditional OverlayNG headline (`OverlayCorrectness.v`, three named
   hypotheses).
3. The guard bridge from the noder's `fully_intersected` to
   `noded_general_position`, plus guards 2 and 5 (uninvestigated).
4. C2 off-grid completeness — **parked by decision**; would be stale as an issue.
5. Arc Hobby analog — a research gap with no published true statement to aim at.

Items 4 and 5 are the reason this ticket is a grilling and not a task: filing them
as issues would misrepresent a decision and a genuine unknown as backlog.
