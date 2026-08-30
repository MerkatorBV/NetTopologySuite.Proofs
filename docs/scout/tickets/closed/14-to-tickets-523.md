# Cut #523 spec into takeable tickets

**Type:** task · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** [Spec #523](13-spec-523-curve-relate-alphabet.md) · **Closed:** 2026-08-30 (tickets written; ticket 523 stays open)

Living spec: [`docs/scout/spec-523.md`](../../spec-523.md).

## Question

Turn [`spec-523.md`](../../spec-523.md) slices A–C into claimable
tickets so `/implement` does not re-spec. Do not implement. Do not
accept ticket 523. Do not mint leftover `ⅠⅠⅠ`. Do not steal closed
`522-*` letters.

## Resolution

**Closed 2026-08-30 with the tickets written.** Ticket 523 stays open
and is not accepted. Ticket 11 precondition 3 is still “resolved or
explicitly accepted.”

Minted claimIds (children of ticket 523, not leftover numerals, not
`522-n`):

| claimId | Scout | Slice | Gate |
|---|---|---|---|
| `523-a` | [15](../15-523-a-eb-refuse.md) | E/B `failwith` | — |
| `523-b` | [16](../16-523-b-cell-unknown.md) | consumers learn `?` as a matrix cell | — |
| `523-c` | [17](../17-523-c-driver-alphabet.md) | driver emits `?` | 16 |

No GitHub child issue numbers. The scout tickets plus these claimIds
are the takeable surface. `/implement 523-a` or `/implement 523-b`
can start now.
