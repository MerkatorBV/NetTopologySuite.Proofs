# Spec — #523 `CURVE_RELATE_MATRIX` alphabet

A takeable implementation spec. Written 2026-08-30 from the grill
([`map-523.md`](map-523.md), ticket 12) plus issue #523 and ticket 11
precondition 3. This is **not** a leftover numeral, **not** a remint of
`522-n`, and **not** the driver rewrite. It does **not** retire ticket
523.

> Ticket 11 precondition 3 stays “#523 resolved or explicitly
> accepted.” This spec does not accept the defect. `/implement` of
> ticket 523 is the later letter that can meet that precondition.

topics: relate, precision
claimId: none
witness: none

## Destination

`CURVE_RELATE_MATRIX` prints `F` only where emptiness is established
(`RelateCurveMatrix.v : cell_none_iff_empty`). Where the mode did not
compute the cell, it prints a distinct per-cell glyph. Elliptic and
Bézier pairs refuse instead of returning `[]` or a centre/chord proxy.
The 80×80 grid stays a probe; an exhausted-probe miss is not Coq
`None`.

Whole-matrix Decline stays `UNSUPPORTED` /
`RelateNGCore.v : relate_unsupported_no_predicate`. A per-cell unknown
is not Decline. CONTEXT has no name for it. This spec does not invent
one.

## Why the grill is the source, not a re-grill

Issue #523 still holds. Line numbers in the issue body have drifted;
the facts have not. Pins below are `origin/main` @ `5b7a934` (same
tree the grill cited). The grill is now on `main` via #600; the
facts survived that rebase:

| Claim | Where |
|---|---|
| Lineal E/B `pair_pts` → `[]` → `"FFFFFFFFF"` | `oracle/driver.ml:3983–3985`, `:4080`, `:4090` |
| Areal E/B centre / control-chord proxy | `:4195–4204`, `:4236–4238`, `:4303–4308` |
| Header “others F” | `:3801–3804` |
| Areal miss → `-1` → `'F'` | `:4354–4368` |
| Open cells = 80×80 grid | `:4332–4358`; header `:3778` |
| EE hardcoded 2 | `:4359`; `RelateCurveMatrix.v : geom_de9im_ee_nonempty` |
| Buffer `failwith` on E/B | `BUFFER_REGION:3353`, `BUFFER_UNIFIED:3482`, `ARC_BUFFER_SIMPLE:3372` |

Do not re-verify those three claims unless the tree moved. Re-cite
line numbers if they drift again.

## Alphabet (ask 1)

**Wire today.** A 9-char row-major DE-9IM, each cell `F`/`0`/`1`/`2`,
or `"NAN"`. Header `:3801`. Coq emptiness is `None`
(`RelateCurveMatrix.v : cell_none_iff_empty`). The oracle prints `F`
for three things that are not that. Whether whole-line `"NAN"` survives
this letter is an implement call (keep as a non-matrix, or drop). It
is not `?` and not Decline.

**Wire after this letter.**

| Glyph | Meaning | Not |
|---|---|---|
| `F` / `0` / `1` / `2` | Emptiness or dimension **established** by the mode | a miss, a skipped cell, an E/B no-op |
| `?` | The mode did not compute this cell | Decline; Coq `None`; “proven empty” |
| whole-line `UNSUPPORTED` | Decline / Sentinel (`CONTEXT.md`) | a 9-char; a cell glyph |

`?` is the issue’s proposed **wire glyph**. It is not a CONTEXT term.
Do not add a glossary entry in the implement letter unless
`/domain-modeling` has run and the owner accepted a name. Do not steal
`UNSUPPORTED` as a cell character — that token is result-position only
(`oracle/relate_matrix.ml` `relate_result`; harness
`RELATE_TOKENS = frozenset({"UNSUPPORTED"})`).

A 9-char that contains `?` is still a **matrix** (partial opinion),
not a Decline. Parsers keep two kinds: `("token", "UNSUPPORTED")` and
`("matrix", ninechar)`. They do not grow a third kind for `?`.

**When is emptiness established?**

- **Yes — `F` is honest.** The mode ran an analytical primitive on a
  circular / chord pair (`C` / `A`) and that primitive reported no
  contact. Same kernels as `ARC_ARC_XY` / `ARC_SEGMENT_XY` /
  `HOLES_DISJOINT` (`docs/curve-relate-matrix-lemma-reuse-map.md`).
- **No — print `?`.** Lineal cells the header already calls
  undistinguishable (`:3801–3804`). Areal open cells after an
  exhausted 80×80 probe (`:4332–4358`). Any cell the assembler never
  attempted.
- **No — do not print a matrix.** Elliptic / Bézier input (ask 2).
- **Already established nonempty.** EE stays `2`
  (`RelateCurveMatrix.v : geom_de9im_ee_nonempty` /
  `two_geometries_exterior_meet`). Do not rewrite EE to `?`.

**Consumers must learn `?` before the driver emits it.** Today they
reject it:

- `tests/GeosOracleBugHunt/hunt.py` — `RELATE_MATRIX_CHARS = set("F012")`
- `tests/CurveOracleBugHunt/Program.cs` — `ParseRelateWire` same allowlist
- `oracle/relate_matrix.ml` `lookup_matrix` — a 9-char key must be `F`/`0`/`1`/`2`
- `oracle/gen_curve_relate_matrix_tests.py` / `curve_relate_matrix_tests.txt`

`RELATE_MATRIX` / `RELATE_PREDICATE` stay catalog evaluation. Do not
put `?` in catalog keys or in the shared classifier pins
(FFFFFFFFF / 2FFF1FFF2 / 2FFFFFFF2 / FFFF1FFF2). Those pins are also
used by `rect_pair_fill`. The T-junction decline golden stays
`UNSUPPORTED` (`oracle/de9im_triangle_vectors.txt` `REGIME DECLINE`).
Do not turn that golden into a confident `FFFFFFFFF`. The #530 /
#571 pair stays classified disjoint (FFFFFFFFF), not a sentinel.

Unknown whole-line tokens still fail. `?` as a **whole-line** token
(nine question marks without being a 9-char matrix parse, or a bare
`?`) is not Decline. Do not add `?` to `RELATE_TOKENS`.

## Elliptic / Bézier refuse (ask 2)

**Today.** Parse accepts `E` / `B` (`oracle/driver.ml:3816–3823`).
Lineal `pair_pts` returns `[]` (`:3983–3985`) and prints
`"FFFFFFFFF"`. Areal proxy-samples the elliptic centre or the Bézier
control chord (`:4195–4208`, `:4236–4238`, `:4303–4308`). Same shape
as #511 (elliptic no-op in `RING_ORIENTATION` /
`POINT_IN_CURVE_RING`).

**After this letter.** Any `E` / `B` segment in either argument
**refuses the mode**. Match the buffer precedent: `BUFFER_REGION`,
`BUFFER_UNIFIED`, and `ARC_BUFFER_SIMPLE` `failwith` on anything but
`C` / `A`. Do **not** print a 9-char. Do **not** print
`UNSUPPORTED` — that is a relate Decline (unclassified pair), not a
capability refuse. Do **not** use `LENGTH_UNIFIED` as the precedent;
that mode accepts E/B and computes.

Year 1 stays circular. Do not add Exact\* zoo carriers. Do not extend
`CurveSegment`. Do not start 64-a r·θ. Refuse is the honest interim
until #508.

This slice has **no consumer-token gate**. It can land before ask 1.

## Grid probe (ask 3)

The header already says the open cells are “probed by a grid”
(`:3778`). Keep saying that. After ask 1, state what an exhausted
probe prints:

> An exhausted 80×80 probe over the padded joint box leaves the cell
> as `?`: no sample found. That is not
> `RelateCurveMatrix.v : cell_none_iff_empty`.

A hit still sets the open cell to `2`. EE stays `2` by the exterior-
meet theorem, not by the grid. Tolerances `1e-12` / `1e-9`
(`:3964`, `:3974` and the areal copies) stay interface-boundary float.
This letter does not retune them.

Formal completeness of the 80×80 grid (“miss ⇒ empty”) has no
published true form. That statement is a **research park** (ADR-0002).
It is not required to emit an honest `?`.

## Slices for `/implement` of ticket 523

One letter may do all three. If split, this order is the gate graph:

| Slice | What | Gate |
|---|---|---|
| **A** | E/B `failwith` (ask 2) | none |
| **B** | Consumers accept `?` as a **matrix cell** only | none, but must land before C |
| **C** | Driver emits `?` / keeps `F` only when established; header + probe sentence (asks 1 and 3) | B |

Done when:

1. A circular / chord pair that the analytical kernels report empty
   still prints `F` in those computed cells.
2. A lineal undistinguished cell prints `?`, not `F`.
3. An areal open-cell miss prints `?`, not `F`. EE is still `2`.
4. An `E` / `B` pair does not print `"FFFFFFFFF"` and does not emit a
   9-char. The mode fails the way the buffer modes fail.
5. Harness goldens: Decline is still `UNSUPPORTED`. Shared pins are
   untouched. `parse_relate_wire("FF?FF1212")` is `("matrix", …)`.
   `parse_relate_wire("UNSUPPORTED")` is still `("token", …)`.
   `parse_relate_wire("NOT_A_TOKEN")` still fails.
6. Mode header names the probe and the exhausted-probe `?`.
7. `docs/verified-claims.md` `RelateCurveMatrix.v` row records the
   alphabet (not only the dimension deferral). Ticket 11 precondition
   3 can then be marked met **only if** the owner treats the letter as
   resolving ticket 523 — the implement letter does not auto-retire
   that issue.

## Parks (ADR-0002)

- **Sequencing.** Slices A–C above. Gate for C: consumers (slice B).
  Gate for ticket 11 precondition 3: this letter landing, or an
  explicit accept. This spec is not that accept.
- **Research.** Completeness of the 80×80 grid. Not required here.
- **Technique.** None.

## Non-goals

- Do not remint classifier fills / shared pins (FFFFFFFFF /
  2FFF1FFF2 / 2FFFFFFF2 / FFFF1FFF2). OGC gtri names stay `*_ogc`.
  `pat_disjoint` still rejects FF2FF1212.
- Do not turn the #522 harness decline golden into a confident
  `FFFFFFFFF`.
- Do not implement leftover `Ⅰ` (T-junction) or `ⅠⅠ` (obtuse-at-v).
  Do not mint `ⅠⅠⅠ` for this sibling.
- Do not steal `522-h` / `522-l` / closed `522-a`…`522-m`.
- Do not remint ADR-0004. Do not extend `CurveSegment`. Do not start
  64-a r·θ.
- Do not wire ray parity (ADR-0003). Do not invent T-junction or
  obtuse certificates.
- Do not add a CONTEXT name for per-cell unknown unless
  `/domain-modeling` + owner accept.
- Do not comment on GitHub issue 523 unless the user says `comment`.
- This spec letter does not retire ticket 523 or epic 522.

## Not this leftover

- #522 honesty / bar-1 / bar-2 — wrong matrix, not dishonest alphabet.
- Leftover `Ⅰ` / `ⅠⅠ` — triangle classifier residue
  (`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction`).
- ADR-0003 capstone — specified vs computed interior.
- #511 — sibling shape, different modes.
- #508 — zoo length; Year 1 stays circular.

## Ticket 11

Precondition 3 is **not met** by writing this spec. The geometry-
compute mode still cannot be used as a differential reference for
cells it did not compute. After `/implement` of ticket 523 lands,
that sentence is what becomes false — and only then.
