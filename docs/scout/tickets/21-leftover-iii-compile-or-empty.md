# Leftover `ⅠⅠⅠ` — compile a cex or prove emptiness

**Type:** task · **Map:** [#522 leftovers](../map-522-leftovers.md)
**Blocked by:** — · **Spec:** [`spec-onesided-t.md`](../spec-onesided-t.md) slice A
**claimId:** `ⅠⅠⅠ` · **GitHub:** none · **witness:** none

> Umbrella: leftover `ⅠⅠⅠ`. Does not retire epic 522. Not leftover
> `Ⅰ`. Not leftover `ⅠⅠ`. Not a `522-*` letter.

## Question

Leftover `ⅠⅠⅠ` is a named family with **no** compiled 12-tuple.
Either inhabit it among both-CCW triangles or prove it empty.
Do not invent the tuple in a comment.

Family filter (all must hold; this list is not a pair):

1. Both triangles are CCW.
2. A vertex of one sits in the open interior of an edge of the other.
3. The contact is not mutual (leftover `Ⅰ`'s `touch_partial_edge_b`
   on #609 stays false).
4. The triangles share no vertex.
5. The shared set is a point (BB dimension 0).
6. The tuple is not a `classified_hard_pairs` row, not leftover `Ⅰ`,
   not leftover `ⅠⅠ`, not the RelatePrepared CW 12-tuple.

Grill cites (`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`;
`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`;
`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete_not_tjunction`).

## Acceptance

Exactly one of:

1. A named 12-tuple in `RelateNGComplete.v` that satisfies the filter,
   with a finding that the classifier emits `TPR_Unsupported` (or
   leftover `Ⅰ`'s constructor if #609 has landed and the boolean is
   still false). Both-CCW proofs sit next to the coords. **or**
2. A theorem that no both-CCW pair inhabits the filter.

The letter does **not** emit `FFFFFFFFF`. It does **not** move the
decline golden unless the golden pair itself classifies. Completeness
stays false (`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`)
unless emptiness plus leftover `Ⅰ` / `ⅠⅠ` landing leave no other
cex.

If emptiness is proved, ticket 22 is cancelled.

## Non-goals

Do not invent a prose 12-tuple and treat it as compiled. Do not
implement ticket 22 here unless the same letter claims it and slice A
produced a cex. Do not widen `touch_partial_edge_b` /
`cone_separates_b` / `shares_edge_b`. Do not remint `aa_matrix_*`.
Do not mint `522-n`. Do not mint `ⅠⅠⅠⅠ`. Do not steal leftover
`Ⅰ` / `ⅠⅠ` / `522-j` / `522-m` / `522-f` / `522-i`. Do not pile
onto #609, #611, #614, or a `508-*` branch. Do not comment on a
GitHub issue unless the user says `comment`.
