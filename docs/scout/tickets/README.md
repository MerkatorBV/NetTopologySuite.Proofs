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
| 07 | ~~[Retire #67 — RelateNG matrix and boundary handling](closed/07-retire-67-relateng.md)~~ **closed: decided not to close #67** → ADR-0003, #522, #523 | grilling | — |
| 11 | [Retire #67 — second pass](11-retire-67-second-pass.md) | grilling | ADR-0003 unconsumed, **#523**, **#503** — precondition 1 largely met by #530; #523 children `523-a`/`523-b`/`523-c` landed, still open, not accepted |
| 12 | ~~[Grill #523 — `CURVE_RELATE_MATRIX` alphabet](closed/12-grill-523-curve-relate-alphabet.md)~~ **closed: decided not to resolve ticket 523** → [`map-523.md`](../map-523.md) | grilling | — |
| 13 | ~~[Spec #523 — `CURVE_RELATE_MATRIX` alphabet](closed/13-spec-523-curve-relate-alphabet.md)~~ **closed: spec written; ticket 523 stays open** → [`spec-523.md`](../spec-523.md) | task | 12 |
| 14 | ~~[Cut #523 spec into takeable tickets](closed/14-to-tickets-523.md)~~ **closed: tickets written; ticket 523 stays open** → `523-a` / `523-b` / `523-c` | task | 13 |
| 15 | ~~[`523-a` — E/B refuse](closed/15-523-a-eb-refuse.md)~~ **closed** → [#603](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/603) | task | 14 |
| 16 | ~~[`523-b` — consumers accept `?` as a matrix cell](closed/16-523-b-cell-unknown.md)~~ **closed** → [#604](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/604) | task | 14 |
| 17 | ~~[`523-c` — driver prints `?` where it did not compute](closed/17-523-c-driver-alphabet.md)~~ **closed** → [#605](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/605) | task | 16 / #604 |
| 08 | ~~[Retire #68 — Delaunay triangulation and Voronoi diagrams](closed/08-retire-68-delaunay-voronoi.md)~~ **closed** → #525 (global tier), #526 | grilling | — |
| 09 | [End #69's umbrella role and re-parent the standing epics](09-end-69-umbrella.md) | grilling | 11 (04–08 all closed) |
| 10 | [Resync surviving issue bodies to corpus state](10-resync-surviving-bodies.md) | task | **#506 queue empty**, 09 |

```
01 ══════════════════════════════════════ closed 2026-08-22 (#482)

02 ═══ 03 ═══ #506 ───────────────┐  gate live in CI; epic open
              (queue must empty)  ├── 10
04 ═══════════════════════╗       │  #64 closed → #508 #509 #510 #511
05 ═══════════════════════╣       │  #65 closed → #515 (hero shot), #513 #514
06 ═══════════════════════╣       │  #66 closed → #517 #518 #519 #520
07 ═══ 11 ────────────────╣       │  #67 still open (reopened after an
       (ADR-0003, #523,   ║       │  accidental keyword closure) → ADR-0003,
        #503)             ║       │  #522 wrap-up on main; #523 children
                                  │  523-a / 523-b / 523-c landed (15–17
                                  │  closed). Ticket 523 still open,
                                  │  not accepted
08 ═══════════ 09 ────────╝───────┘  #68 closed → #525 (global tier), #526
```

**Related living maps.** The #522 children (bar 1 → bar 2) have their own
frontier: [`docs/scout/map-522.md`](../map-522.md). Wrap-up leftovers:
[`docs/scout/map-522-leftovers.md`](../map-522-leftovers.md).
`/wayfinder 522 leftovers` refreshes the leftovers chart. Leftover `Ⅰ` is the mutual vertex-in-open-edge sliver. Leftover `Ⅱ` is
the obtuse-at-v certificate ([`map-obtuse-cert.md`](../map-obtuse-cert.md); ticket [27](closed/27-leftover-ii-obtuse.md) closed — `RelateNGTouchObtuse.v : triangle_pair_regime_obtuse`; fill token). Leftover `Ⅲ` is the exterior-side one-sided T (`Ⅲ∨Ⅳ` xor, two compiled witnesses, one constructor / one fill token / one `True` arm). Leftover `Ⅳ` is the interior-side stem ([`map-interior-side-cert.md`](../map-interior-side-cert.md); grill [`map-interior-side-grill.md`](../map-interior-side-grill.md); ticket [26](closed/26-leftover-iv-compile-or-empty.md) closed — `RelateNGComplete.v : interior_side_pair_inhabits`; not CONTEXT Bar 1). Leftover `Ⅴ` is mixed-cone ([`map-mixed-cone-cert.md`](../map-mixed-cone-cert.md); ticket [28](closed/28-leftover-v-mixed-cone.md) closed — `RelateNGTouchMixedCone.v : triangle_pair_regime_mixedcone`; fill token). Leftover `Ⅵ` is same-cone ([`map-same-cone-cert.md`](../map-same-cone-cert.md); ticket [29](closed/29-leftover-vi-same-cone.md) closed — `RelateNGTouchSameCone.v : triangle_pair_regime_samecone`; fill token). Leftover `Ⅶ` is the lens ([`map-lens-cert.md`](../map-lens-cert.md); ticket [30](closed/30-leftover-vii-lens.md) closed — `RelateNGTouchLens.v : triangle_pair_regime_lens`; fill token; #522 stop QED ∨ QEX on `triangle_pair_regime_ccw_stop`). Sibling #523 alphabet grill:
[`docs/scout/map-523.md`](../map-523.md). Takeable spec:
[`docs/scout/spec-523.md`](../spec-523.md). Alphabet letter landed:
[`15`](closed/15-523-a-eb-refuse.md) `523-a`, [`16`](closed/16-523-b-cell-unknown.md)
`523-b`, [`17`](closed/17-523-c-driver-alphabet.md) `523-c`. Ticket 11 still
waits on ADR-0003 / #523 / #503; it does not own leftover grab order and
does not receive a closed `522-*` letter. Landing the children does not
accept ticket 523.

**Frontier.** Alphabet children 15–17 are closed. Ticket 11 still waits.

| Ticket | Waiting on |
|---|---|
| 15 · `523-a` / #603 E/B refuse | closed |
| 16 · `523-b` / #604 consumer `?` cell | closed |
| 17 · `523-c` / #605 driver alphabet | closed |
| 11 · second pass at #67 | ADR-0003 consumed by the capstone work · ticket 523 (`523-a`…`523-c` landed; still open, not accepted) · #503's four defects. Precondition 1 largely met by #530. |
| 09 · end #69's umbrella | ticket 11 |
| 10 · resync surviving bodies | #506's split queue emptying · ticket 09 |

The next useful session is not another #523 letter. Owner resolve-or-accept
is the gate for ticket 11 precondition 3. Leftover `Ⅰ` / `Ⅱ` / `Ⅲ` / `Ⅳ`
are compiled. Leftover `Ⅴ` is compiled. Leftover `Ⅵ` is compiled.
Leftover `Ⅶ` is compiled. Completeness is an unnamed inside pair
(not leftover `Ⅷ`).

Three epics retired on evidence, one deliberately not: **an epic closes only when
its closure comment would be true.**
