# Spec — leftover `ⅠⅠⅠ` (one-sided / non-collinear vertex-in-open-edge T)

A takeable implementation spec. Written 2026-08-30 from the grill
([`map-onesided-t-grill.md`](map-onesided-t-grill.md)) plus the research
chart ([`map-onesided-t-cert.md`](map-onesided-t-cert.md), #614). This
is **not** leftover `Ⅰ`, **not** leftover `ⅠⅠ`, and **not** a remint
of `522-n`. It does **not** invent a 12-tuple. It does **not** retire
epic 522.

> `/implement ⅠⅠⅠ` is the later letter. That letter must not treat
> a prose sketch as the spec pair.

topics: relate
claimId: ⅠⅠⅠ
witness: none

## Destination

**Compile** a both-CCW 12-tuple that inhabits the family. An
exterior-side stem exists; emptiness would be a surprise. Only if
inhabited: a detector that is true on that tuple and false on leftover
`Ⅰ`, leftover `ⅠⅠ`, and the four wired hard pairs
(`RelateNGComplete.v : classified_hard_pairs`). Fill stays
`im_unsupported` until ticket 21 picks a side and the owner names a
matrix. Completeness stays false
(`RelateNGComplete.v : triangle_pair_regime_ccw_incomplete`).

CONTEXT **Regime** is not met until a real `classify_triangle_pair`
arm exists. CONTEXT **Bar 1** is not met until that arm is true
geometry against the specified interior **and** a designated witness
matrix is named. The first implement letter is allowed to stop at
witness-scoped regime reachability (same honesty as leftover `Ⅰ`
#609). Do not call that stop CONTEXT Bar 1.

## Why the grill is the source, not a re-grill

The grill confirmed six claims against the tree. Do not re-verify
them unless the tree moved:

| Claim | Where |
|---|---|
| No compiled pair | `RelateNGComplete.v` has no onesided coords |
| Decline cexes are `Ⅰ` and `ⅠⅠ` | `triangle_pair_regime_incomplete_tjunction`, `triangle_pair_regime_ccw_incomplete_not_tjunction` |
| Wired detectors miss | `RelateNGCore.v : triangle_pair_regime` |
| #609 is mutual | #609, not on `main` |
| Bar 1 not applicable | CONTEXT; no pair, no matrix |
| Uninhabited on the compiled tree | research park; an exterior-side stem exists |

## Family (acceptance predicate, not a pair)

A later compiled 12-tuple inhabits leftover `ⅠⅠⅠ` only if **all**
of the following hold. This list is the filter. It is not a sketch
of coordinates.

1. Both triangles are CCW.
2. A vertex of one sits in the **open interior** of an edge of the
   other (endpoints out; strict on-edge, not a shared vertex).
3. The contact is **not mutual** (leftover `Ⅰ`'s
   `touch_partial_edge_b` on #609 stays false).
4. The triangles share **no vertex** (leftover `ⅠⅠ` / `522-i` stay
   out).
5. The shared set is a **point** (BB dimension 0), not leftover `Ⅰ`'s
   positive-length collinear kiss. An interior-side stem can still
   have II nonempty (overlap) — a different DE-9IM family. Ticket 21
   records which side it compiled. Prove II empty before calling the
   pair areal Touches.
6. The tuple is not a `classified_hard_pairs` row, not leftover `Ⅰ`,
   not leftover `ⅠⅠ`, not the RelatePrepared CW 12-tuple.

Do not write those six bullets as a 12-tuple in this spec.

## Slices for `/implement ⅠⅠⅠ`

One letter may do both. If split, this order is the gate graph:

### Slice A — compile a cex (emptiness would be a surprise)

**Today.** No pair on the compiled tree. Completeness false. An
exterior-side stem exists; compiling a witness is the expected close.

**After this slice.** A named 12-tuple in `RelateNGComplete.v` that
satisfies the family filter, with a finding that the classifier emits
`TPR_Unsupported` (or leftover `Ⅰ`'s constructor if #609 has
landed and the boolean is still false). Both-CCW proofs sit next
to the coords. Record which side (exterior-side stem vs interior-side
stem).

An emptiness theorem is still allowed and would be a surprise. If
proved, slice B is cancelled. Completeness may still be false for
other reasons (leftover `Ⅰ` / `ⅠⅠ` until those letters land).

Do **not** invent the tuple in a comment and treat it as compiled.
Do **not** emit `FFFFFFFFF`. Do **not** move the decline golden
unless the golden pair itself classifies. Do **not** remint leftover
`Ⅰ` to `FF2F11212` / `FFFF1FFF2`.

### Slice B — detector if inhabited

**Blocked by** slice A producing a cex.

**Today.** No boolean.

**After this slice.** A new boolean that is true on the slice-A
tuple and false on leftover `Ⅰ`, leftover `ⅠⅠ`, and
`classified_hard_pairs`. Constructor is an **owner call** (reuse vs
new). A new constructor may stay on `im_unsupported`. Do **not**
widen leftover `Ⅰ`'s mutual `touch_partial_edge_b`. Do **not**
invent leftover `ⅠⅠ`'s cone detector. Do **not** silently widen
`RelateNGCore.v : cone_separates_b` / `touch_vertex_b`. Do **not**
widen `shares_edge_b` / `touch_edge_b`. Do **not** remint
`aa_matrix_*`. Classifier order: after leftover `Ⅰ`'s arm if that
letter has landed, and after `touch_vertex_b`. Do not reorder the
four wired certificates.

`classify_triangle_pair` must not be `True` if the letter claims
CONTEXT Bar 1. A `True` arm is leftover `Ⅰ` #609 honesty, not Bar 1.

## Parks (ADR-0002)

- **Research (slice A).** Uninhabited on the compiled tree.
  Graduates when a cex compiles. Emptiness is still allowed and
  would be a surprise.
- **Sequencing (slice B, fill, harness).** Detector waits on A.
  Exterior-side stem with II empty is areal Touches, BB dim 0.
  Interior-side stem is typically overlap. Fill stays
  `im_unsupported` until ticket 21 picks a side. Designated
  TouchVertex / TouchEdge pin is still `FFFF1FFF2`. Harness golden
  on `main` is leftover `Ⅰ`; after #609 it is leftover `ⅠⅠ`.
  Wiring this family does not move that golden unless the golden
  pair classifies.
- **Technique.** Constructor vs reuse. Owner call.

## Non-goals

- Inventing a 12-tuple in this spec
- Minting `522-n` or `ⅠⅠⅠⅠ`
- Stealing leftover `Ⅰ` / `ⅠⅠ` / `522-j` / `522-m` / `522-f` / `522-i`
- Reminting ADR-0004, `aa_matrix_*`, CurveSegment, Exact\* zoo
- Widening `shares_edge_b`
- Nine-cell gtri / CONTEXT Bar 2 in the first letter
- Retiring epic 522
- Piling onto #609, #611, #614, or a `508-*` branch
- GitHub children (claimId hangs on the leftover numeral)

## If `/implement ⅠⅠⅠ` is asked

Start at scout ticket 21 (slice A). Ticket 22 is slice B. Do not
restage this spec. Do not comment on a GitHub issue unless the user
says `comment`.
