# Leftover `Ⅳ` — compile a residue cex or prove emptiness

**Type:** task · **Map:** [#522 leftovers](../map-522-leftovers.md)
**Blocked by:** — · **Spec:** [`spec-interior-side.md`](../spec-interior-side.md) slice A
**claimId:** `Ⅳ` · **GitHub:** none · **witness:** none

> Umbrella: leftover `Ⅳ`. Does not retire epic 522. Not leftover
> `Ⅰ`. Not leftover `Ⅱ`. Not leftover `Ⅲ`. Not a `522-*` letter.

## Question

Leftover `Ⅳ` is a named family with **no** compiled 12-tuple. The
xor (`RelateNGCore.v : touch_onesided_t_b`) is already a `Ⅲ∨Ⅳ`
configuration class with one exterior-side witness (leftover `Ⅲ`,
#628). `overlap_b` may steal same-side stems (those are leftover
`522-b`). This letter compiles a residue witness or proves the
residue empty. Do not invent the tuple in a comment and treat it as
compiled. Do not remint the xor. Do not invent a detector.

Family filter (all must hold; this list is not a pair):

1. Both triangles are CCW.
2. A vertex of one sits in the open interior of an edge of the other.
3. The contact is not mutual (`touch_partial_edge_b` stays false).
4. The triangles share no vertex.
5. Remaining vertices of the stemmed triangle sit on the same side
   of the supporting line as the other interior (leftover `Ⅲ`
   opposite-side / `onesided_t_ii_empty` stays out).
6. `overlap_b` is false (`RelateNGCore.v : overlap_b`).
7. The tuple is not a `classified_hard_pairs` row, not leftover `Ⅰ`,
   not leftover `Ⅱ`, not leftover `Ⅲ`, not the RelatePrepared CW
   12-tuple.

Grill cites (`RelateNGComplete.v : onesided_t_pair_inhabits`;
`RelateNGComplete.v : onesided_t_ii_empty`;
`RelateNGCore.v : touch_onesided_t_b`;
`RelateNGCore.v : overlap_b`;
`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`).

## Acceptance

Exactly one of:

1. A named 12-tuple in `RelateNGComplete.v` that satisfies the
   filter, with a finding that the classifier emits
   `TPR_TouchOnesided`. Both-CCW proofs sit next to the coords.
   Record that the pair is interior-side. **or**
2. A theorem that no both-CCW pair inhabits the filter (every
   same-side one-sided T is already `overlap_b` / `contains_b` /
   leftover `Ⅰ`).

Typically II is nonempty. Prove II empty before calling the pair
BB dim 0 Touches. There is no `onesided_t_bb_dim0`. Fill stays
`im_unsupported`. The letter does **not** emit `FFFFFFFFF` /
`FFFF1FFF2` / `FF2F11212`. It does **not** move the decline golden
unless the golden pair itself classifies. Completeness stays false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`). Do
**not** remint leftover `Ⅰ` or leftover `Ⅲ` fills. Do **not**
remint `touch_onesided_t_b`.

A side-distinguishing boolean is a later leftover, and only if
asked. Next unused is `Ⅴ`.

## Non-goals

Do not invent a prose 12-tuple and treat it as compiled. Do not
write a detector. Do not remint `touch_onesided_t_b` /
`touch_partial_edge_b` / `cone_separates_b` / `shares_edge_b` /
`overlap_b`. Do not remint `aa_matrix_*`. Do not mint `522-n`.
Do not mint `Ⅴ`. Do not steal leftover `Ⅰ` / `Ⅱ` / `Ⅲ` /
`522-j` / `522-m` / `522-f` / `522-b` / `522-i`. Do not pile onto
#609, #611, #628, #629, or a `508-*` branch. Do not comment on a
GitHub issue unless the user says `comment`.
