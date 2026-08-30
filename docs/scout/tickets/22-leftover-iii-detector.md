# Leftover `ⅠⅠⅠ` — detector if inhabited

**Type:** task · **Map:** [#522 leftovers](../map-522-leftovers.md)
**Blocked by:** [Compile or empty](21-leftover-iii-compile-or-empty.md) · **Spec:** [`spec-onesided-t.md`](../spec-onesided-t.md) slice B
**claimId:** `ⅠⅠⅠ` · **GitHub:** none · **witness:** none

> Umbrella: leftover `ⅠⅠⅠ`. Cancelled if ticket 21 proves emptiness.
> Does not retire epic 522. Not leftover `Ⅰ`. Not leftover `ⅠⅠ`.

## Question

If ticket 21 compiled a cex, add a detector that is true on that
tuple and false on leftover `Ⅰ`, leftover `ⅠⅠ`, and
`classified_hard_pairs` (`RelateNGComplete.v : classified_hard_pairs`).

Constructor is an **owner call** (reuse vs new). A new constructor
may stay on `im_unsupported`. Fill stays `im_unsupported` until
ticket 21 picks a side (exterior-side stem vs interior-side stem)
and the owner names a matrix. Do not claim CONTEXT Bar 1 with a
`True` `classify_triangle_pair` arm. Do not remint leftover `Ⅰ`
to `FF2F11212` / `FFFF1FFF2`.

## Acceptance

1. A new boolean that is true on the ticket-21 tuple and false on
   leftover `Ⅰ`, leftover `ⅠⅠ`, and `classified_hard_pairs`.
2. Classifier order: after leftover `Ⅰ`'s arm if that letter has
   landed, and after `touch_vertex_b`
   (`RelateNGCore.v : triangle_pair_regime`). Do not reorder the four
   wired certificates.
3. `classify_triangle_pair` must not be `True` if the letter claims
   CONTEXT Bar 1. A `True` arm is leftover `Ⅰ` #609 honesty, not
   Bar 1.
4. Do **not** widen leftover `Ⅰ`'s mutual `touch_partial_edge_b`.
   Do **not** invent leftover `ⅠⅠ`'s cone detector. Do **not**
   silently widen `RelateNGCore.v : cone_separates_b` /
   `touch_vertex_b`. Do **not** widen `shares_edge_b` /
   `touch_edge_b`.

## Non-goals

Nine-cell gtri / CONTEXT Bar 2. Remint of `aa_matrix_*`. Minting
`522-n` or `ⅠⅠⅠⅠ`. Stealing leftover `Ⅰ` / `ⅠⅠ` / `522-j` /
`522-m` / `522-f` / `522-i`. Piling onto #609, #611, #614, or a
`508-*` branch. Commenting on a GitHub issue unless the user says
`comment`.
