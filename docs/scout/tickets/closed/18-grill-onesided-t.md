# Grill leftover `ⅠⅠⅠ` — one-sided / non-collinear vertex-in-open-edge T

**Type:** grilling · **Map:** [#522 leftovers](../../map-522-leftovers.md)
**Blocked by:** — · **Closed:** 2026-08-30 (grill written; leftover `ⅠⅠⅠ` stays open)
**claimId:** `ⅠⅠⅠ` · **GitHub:** none · **witness:** none

Living record: [`docs/scout/map-onesided-t-grill.md`](../../map-onesided-t-grill.md).
Research chart: [`docs/scout/map-onesided-t-cert.md`](../../map-onesided-t-cert.md) (#614).
Spec (later, ticket 19): [`docs/scout/spec-onesided-t.md`](../../spec-onesided-t.md).

## Question

Does leftover `ⅠⅠⅠ` hold against the tree and against CONTEXT? Name
what holds. Park what does not. Do not invent a 12-tuple. Do not
invent a detector. Do not restage #609 / #611 / #614.

## Resolution

**Closed 2026-08-30 with the grill written.** Leftover `ⅠⅠⅠ` stays
open. CONTEXT Bar 1 is not applicable (no pair, no matrix).

Satisfied (verify then cite):

- No compiled onesided coords in `RelateNGComplete.v`.
- Decline cexes are leftover `Ⅰ`
  (`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`)
  and leftover `ⅠⅠ`
  (`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).
- Wired detectors miss
  (`RelateNGCore.v : triangle_pair_regime`).
- #609's `touch_partial_edge_b` is mutual. This family is one-sided.
- Completeness stays false
  (`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`).
- Inhabited-or-empty is still open (research park, ADR-0002).

Do **not** implement a cex or a detector here. Do **not** mint
`522-n`. Do **not** mint `ⅠⅠⅠⅠ`. Do **not** steal leftover `Ⅰ`
/ `ⅠⅠ`.
