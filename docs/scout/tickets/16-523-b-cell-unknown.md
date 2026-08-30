# `523-b` — consumers accept `?` as a DE-9IM matrix cell

**Type:** task · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** — · **Spec:** [`spec-523.md`](../spec-523.md) slice B
**claimId:** `523-b` · **witness:** none yet

> Part of ticket 523. Does not retire that issue. Not leftover `ⅠⅠⅠ`.
> Not a remint of `522-f`.

## Question

`CURVE_RELATE_MATRIX` will emit `?` in cells it did not compute
(`523-c`). Today every consumer rejects that glyph. Teach them `?`
as a **matrix cell** before the driver prints it.

Consumers (`origin/main` @ `5b7a934`):

- `tests/GeosOracleBugHunt/hunt.py` — `RELATE_MATRIX_CHARS = set("F012")`
- `tests/CurveOracleBugHunt/Program.cs` — `ParseRelateWire` same allowlist
- `oracle/relate_matrix.ml` `lookup_matrix` — a 9-char key must be
  `F`/`0`/`1`/`2`
- `oracle/gen_curve_relate_matrix_tests.py` / `curve_relate_matrix_tests.txt`

## Acceptance

1. A 9-char that contains `?` parses as `("matrix", ninechar)`.
   Example: `parse_relate_wire("FF?FF1212")` succeeds as a matrix.
2. Parsers keep two kinds only: `("token", "UNSUPPORTED")` and
   `("matrix", ninechar)`. No third kind for `?`.
3. Whole-line `UNSUPPORTED` stays Decline
   (`RelateNGCore.v : relate_unsupported_no_predicate`).
   `parse_relate_wire("UNSUPPORTED")` is still `("token", …)`.
4. Unknown whole-line tokens still fail
   (`parse_relate_wire("NOT_A_TOKEN")`).
5. Do **not** add `?` to `RELATE_TOKENS`. A bare `?` or a
   whole-line-that-is-not-a-9-char is not Decline.
6. Do **not** steal `UNSUPPORTED` as a cell character.
7. Do **not** put `?` in catalog keys or in the shared classifier
   pins (FFFFFFFFF / 2FFF1FFF2 / 2FFFFFFF2 / FFFF1FFF2). Those pins
   are also used by `rect_pair_fill`.
8. T-junction decline golden stays `UNSUPPORTED`
   (`oracle/de9im_triangle_vectors.txt` `REGIME DECLINE`). Do not
   turn it into a confident `FFFFFFFFF`. The #530 / #571 pair stays
   classified disjoint (FFFFFFFFF), not a sentinel.

`?` is the issue’s proposed **wire glyph**. It is not a CONTEXT term.
Do not add a glossary entry unless `/domain-modeling` has run and
the owner accepted a name.

This ticket does **not** change `CURVE_RELATE_MATRIX` output. That
is `523-c`, and it waits on this one.

## Non-goals

Do not remint `522-f`. Do not implement leftover `Ⅰ` / `ⅠⅠ`. Do not
mint `ⅠⅠⅠ`. Do not emit `?` from the driver here. Do not comment on
GitHub issue 523 unless the user says `comment`.
