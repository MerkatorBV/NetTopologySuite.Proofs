# Write the module-split gate: policy and ratchet guard

**Type:** task · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** —

## Question

The split criterion decided for this effort exists nowhere in the repo: there is
no size policy, no threshold, and no CI size check (`make ci-guards` runs five
guards — admitted, README axioms, deferred registry, claims, oracle handrolled —
none measures size). Write it down and enforce it.

Deliverables:

1. **Policy**, in `docs/macro-meso-micro.md` beside the meso scale it belongs to:
   a module over **1234 lines** whose `(transitive dependents + 1) × lines`
   reaches **3210** must be split, via the established umbrella pattern (original
   name kept as a `Require Export` umbrella, byte-identical declaration set,
   `Print Assumptions` footers carried verbatim).
2. **Guard**, wired into `make ci-guards`: computes the metric over `theories/`
   and `theories-flocq/`, compares against a **shrink-only allowlist** carrying
   headroom so a comment-sized edit to a listed module does not fail the build.
   Fails when an unlisted module crosses the gate, or a listed one grows past its
   headroom. The allowlist may never gain an entry.
3. **The seed protocol**: one split per session, drawn from the queue by the day's
   seed (e.g. `20260822`), recorded the way
   `docs/geos-open-issues-triage-2026-08.md` records its sample seed.

Open question for the ticket: what headroom figure? A fixed pad (+50 lines) is
predictable; a percentage (+5%) scales with the monolith. Pick one and say why in
the policy text.

Reference computation (2026-08-22): gated = `Orient_b64_exact.v` 1270×72,
`HotPixel_b64.v` 2604×32, `Route2.v` 2293×9; exempt near-miss =
`ArcLineIntersect_b64_exact.v` 1516×2 = 3032.
