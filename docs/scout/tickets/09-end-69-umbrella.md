# End #69's umbrella role and re-parent the standing epics

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** [#64](04-retire-64-arc-primitives.md) · [#65](05-retire-65-buffer-and-offset.md) · [#66](06-retire-66-precision-and-overlay.md) · [#67](07-retire-67-relateng.md) · [#68](08-retire-68-delaunay-voronoi.md)

## Question

#69 (Expectant) is a tracking issue whose own body says "Tracking issue only…
Keep open as the epic tracker". Once #64–#68 are retired, what does it track — and
how does it end?

Its `69-a` ask is itself green (`theories/OracleCurveChecklist.v : w1_w5_coverage_table_complete`,
`eval/Claim69a.v`, `verified-claims.md:1042`), so the question is purely about the
umbrella role.

Decide:

1. **Do #423/#424/#425 need a replacement umbrella?** They currently carry
   `Umbrella: #69` in prose. Options: a fresh umbrella issue, a GitHub project
   board, `TRIAGE_NTS_JTS_ISSUES.md` alone (it already holds the wire map), or
   nothing — each stands alone as a clearly-stated epic.
2. **What happens to the successor epics** this map creates (the module-split
   queue, #68's Voronoi phase, #64's V-CP Jordan work if it becomes an epic)? Do
   they inherit an umbrella or stand alone too?
3. **The stale body.** #69's status table is the most-read stale artifact in the
   tracker: it claims the deferred registry has "1 live entry (ArcPointDistance
   fallback)" when the registry is now empty, says "424+ cited theorems" when
   `docs/verified-claims.md` carries 700 rows, and its child map predates D-PT
   closure, the quartic, 68-a/68-b, and the extended epics entirely. If #69
   closes, this evaporates; if it survives in any form, the resync ticket owns it.

This ticket is the map's hinge: the destination is only reached if #69 itself
closes.
