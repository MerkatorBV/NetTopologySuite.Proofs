# Open the module-split queue epic

**Type:** task · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** [Write the module-split gate](02-module-split-gate-policy-and-guard.md)

## Question

The split campaign stalled after a seven-monolith burst in August 2026 (#464,
#465, #472, #475, plus the earlier `EdgeFaceBridge` / `RelateNodingLineLine` /
`CornerCorridorBridge` work), and its remainder is tracked nowhere — only rows
B2/B3/B5 of `docs/audit-meso-sample-2026-08.md` survive, and no issue enumerates
the twelve files now over 800 lines. Open the clearly-stated new epic that carries
it, so the chore has a home outside this map.

The epic should state:

- The gate from the policy ticket, verbatim, as its entry criterion.
- The current queue with metrics, and the exempt near-miss, so nobody re-argues
  membership.
- The seeded one-per-session cadence.
- That high fan-in is **not** a blocker: the umbrella re-export pattern makes
  importers unable to notice a split, which is precisely why `HotPixel_b64.v`
  being marked "split BLOCKED — 21 reverse deps incl. the oracle extraction path"
  in `docs/audit-meso-sample-2026-08.md` is worth revisiting rather than encoding.
- The two split children that regrew past 800 lines
  (`Intersect_b64_exact_forward_error.v` 1002, `RelateNodingLineLineCollection.v`
  781) as evidence that the ratchet guard is the real deliverable — they drifted
  because nothing watched.

Decide in the ticket whether B2/B3/B5 fold into this epic or stay in the audit
doc's queue.
