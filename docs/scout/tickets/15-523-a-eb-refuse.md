# `523-a` — `CURVE_RELATE_MATRIX` refuses elliptic / Bézier

**Type:** task · **Map:** [Retire the epic block #64–#69](../map-epic-block-64-69.md)
**Blocked by:** — · **Spec:** [`spec-523.md`](../spec-523.md) slice A
**claimId:** `523-a` · **witness:** none yet

> Part of ticket 523. Does not retire that issue. Not leftover `ⅠⅠⅠ`.
> Not a `522-*` letter.

## Question

Elliptic / Bézier pairs in `CURVE_RELATE_MATRIX` return `[]` or a
centre / control-chord proxy and print `"FFFFFFFFF"`. Refuse them
instead, the way the buffer modes already `failwith` on `E` / `B`.

Grill cites (`origin/main` @ `5b7a934`; re-cite if they drift):

- Lineal `pair_pts` → `[]` → `"FFFFFFFFF"` (`oracle/driver.ml:3983–3985`,
  `:4080`, `:4090`)
- Areal centre / control-chord proxy (`:4195–4204`, `:4236–4238`,
  `:4303–4308`)
- Buffer precedent: `BUFFER_REGION:3353`, `BUFFER_UNIFIED:3482`,
  `ARC_BUFFER_SIMPLE:3372`

## Acceptance

1. Any `E` / `B` segment in either argument refuses the mode.
   Shape: `failwith`, same as those three buffer modes.
2. The mode does **not** print a 9-char. It does **not** print
   `"FFFFFFFFF"`. It does **not** print `UNSUPPORTED` — that is a
   relate Decline (`RelateNGCore.v : relate_unsupported_no_predicate`),
   not a capability refuse.
3. Do **not** use `LENGTH_UNIFIED` as the precedent (it accepts E/B
   and computes).
4. Year 1 stays circular. Do not add Exact\* zoo carriers. Do not
   extend `CurveSegment`. Do not start 64-a r·θ. Refuse until #508.

No consumer-token gate. This ticket can land before `523-b` / `523-c`.

## Non-goals

Shared pins stay put (FFFFFFFFF / 2FFF1FFF2 / 2FFFFFFF2 / FFFF1FFF2).
Decline golden stays `UNSUPPORTED`. Do not implement `523-b` / `523-c`
here unless the same letter claims them. Do not mint `ⅠⅠⅠ`. Do not
comment on GitHub issue 523 unless the user says `comment`.
