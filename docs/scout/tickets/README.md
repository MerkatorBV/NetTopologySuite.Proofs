# Tickets — Retire the epic block #64–#69

One ticket per session. A ticket is **takeable** when every ticket blocking it is
closed and nobody has claimed it; claim by adding `**Claimed:** <name>` under the
title before doing any work. Resolve by appending a `## Resolution` section,
moving the file to `closed/`, and adding a one-line pointer to the map's
*Decisions so far*.

Order of work: top-down from #64, with the freebie first.

| # | Ticket | Type | Blocked by |
|---|---|---|---|
| 01 | ~~[Close #482 — Shewchuk half-ulp counterexample retip](closed/01-close-shewchuk-counterexample-subtask.md)~~ **closed** | task | — |
| 02 | ~~[Write the module-split gate: policy and ratchet guard](closed/02-module-split-gate-policy-and-guard.md)~~ **closed** | task | — |
| 03 | ~~[Open the module-split queue epic](closed/03-open-module-split-queue-epic.md)~~ **closed** → #506 | task | 02 |
| 04 | ~~[Retire #64 — arc primitives](closed/04-retire-64-arc-primitives.md)~~ **closed** → #508 #509 #510 #511 | grilling | — |
| 05 | [Retire #65 — buffer and offset curves](05-retire-65-buffer-and-offset.md) | grilling | — |
| 06 | [Retire #66 — precision models, snap rounding, OverlayNG](06-retire-66-precision-and-overlay.md) | grilling | — |
| 07 | [Retire #67 — RelateNG matrix and boundary handling](07-retire-67-relateng.md) | grilling | — |
| 08 | [Retire #68 — Delaunay triangulation and Voronoi diagrams](08-retire-68-delaunay-voronoi.md) | grilling | — |
| 09 | [End #69's umbrella role and re-parent the standing epics](09-end-69-umbrella.md) | grilling | 04, 05, 06, 07, 08 |
| 10 | [Resync surviving issue bodies to corpus state](10-resync-surviving-bodies.md) | task | **#506 queue empty**, 09 |

```
01 ══════════════════════════════════════ closed 2026-08-22 (#482)

02 ═══ 03 ═══ #506 ───────────────┐  gate live in CI; epic open
              (queue must empty)  ├── 10
04 ═══════════════════════╗       │  #64 closed → #508 #509 #510 #511
05 ┐                      ║       │
06 ├── 09 ────────────────╝───────┘
07 │
08 ┘
```

**Frontier:** 05, 06, 07, 08 — four takeable, one per session. One epic of the
block is retired; #69's hinge waits on the remaining four.
