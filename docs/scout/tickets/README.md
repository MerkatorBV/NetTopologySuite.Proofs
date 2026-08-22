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
| 05 | ~~[Retire #65 — buffer and offset curves](closed/05-retire-65-buffer-and-offset.md)~~ **closed** → #515 #513 #514, ADR-0002 | grilling | — |
| 06 | ~~[Retire #66 — precision models, snap rounding, OverlayNG](closed/06-retire-66-precision-and-overlay.md)~~ **closed** → #517 #518 #519 #520, ADR-0002 amended | grilling | — |
| 07 | [Retire #67 — RelateNG matrix and boundary handling](07-retire-67-relateng.md) | grilling | — |
| 08 | [Retire #68 — Delaunay triangulation and Voronoi diagrams](08-retire-68-delaunay-voronoi.md) | grilling | — |
| 09 | [End #69's umbrella role and re-parent the standing epics](09-end-69-umbrella.md) | grilling | 04, 05, 06, 07, 08 |
| 10 | [Resync surviving issue bodies to corpus state](10-resync-surviving-bodies.md) | task | **#506 queue empty**, 09 |

```
01 ══════════════════════════════════════ closed 2026-08-22 (#482)

02 ═══ 03 ═══ #506 ───────────────┐  gate live in CI; epic open
              (queue must empty)  ├── 10
04 ═══════════════════════╗       │  #64 closed → #508 #509 #510 #511
05 ═══════════════════════╣       │  #65 closed → #515 (hero shot), #513 #514
06 ═══════════════════════╣       │  #66 closed → #517 #518 #519 #520
07 ┐                      ║       │
08 ├── 09 ────────────────╝───────┘
```

**Frontier:** 07, 08 — two takeable, one per session. Three epics retired;
#69's hinge waits on #67 and #68.
