# SqlMmExampleFactory

claimId: none (tools / docs)

Shelf A start of the north-star path: the **inverse of intake**. A locked
SHC bag (hens / pts / chickens + egg tags) renders ISO/IEC 13249-3:2016
**WKT (§5.1.67)** and **WKB hex (§5.1.68 Table 15)** through
[StringTemplate 4](https://www.stringtemplate.org/) group files.

This directory inhabits **tools bytes**. It does **not** remint Rocq emit
inhabit: `theories/SqlMmSignedTag.v` `ticket_sqlmm_factory_emit_qed_or_qex`
stays the honest **QEX** arm (Rocq does not inhabit byte strings). Do not
flip that ticket to QED from this PR.

Branched from `origin/main` at `f409574f2501647f3979bb9552c10bcd54f3ece1`.
North-star destination: open PR #741 (`docs/NORTH-STAR-SQLMM-ORACLE.md`);
this README copies the path contract so the factory does not depend on
that doc landing.

Consumer: [JTS #7](https://github.com/grootstebozewolf/jts/pull/7).
Grammar pin: [antlr/grammars-v4 #4997](https://github.com/antlr/grammars-v4/pull/4997)
merge `181f4c9` (copies under `tools/WktIntakeWalker/grammar/`).

AI assistance disclosure: this tool was drafted with AI assistance
(Cursor Grok 4.6); human review remains required.

## Path contract

```
tools/WktIntakeWalker/          # ANTLR pin + C# visitor (house style)
tools/SqlMmExampleFactory/      # bag → WKT + WKB  (this directory; Java ST4)
oracle/fixtures/sqlmm/          # optional locked rows (shelf-a smoke hex)
```

Intake already runs the other way:

```
WKT ─ANTLR► tagged CST ─mapper(CST × S)► SHC bag | named Intake Decline
```

Engines still test the **bag**, not the string. Display is a view
(CONTEXT). **No new ADR-0006 oracle keyword** (`INTAKE` / `WKT_EMIT` /
anything else). `oracle/driver.ml` is unchanged.

## Templates and rules

| File | Job |
|---|---|
| `templates/SqlMmWkt.stg` | §5.1.67 text |
| `templates/SqlMmWkb.stg` | §5.1.68 hex assembly |

**SqlMmWkt.stg rules**

| Rule | Surface |
|---|---|
| `wkt` | dispatch |
| `emptyWkt` | `POINT` / `LINESTRING` / `CIRCULARSTRING` `EMPTY` |
| `simpleWkt` | `POINT`, `LINESTRING`, `CIRCULARSTRING`, `CIRCLE` |
| `compoundWkt` / `compoundMember` | `COMPOUNDCURVE`; LS children stay **bare** `(…)`; CS / CIRCLE / CLOTHOID keep type |
| `clothoidWkt` / `clothoidJts` / `clothoidIso` | both clothoid surface forms |
| `xy` | one `x y` pair (trimmed like intake) |

**SqlMmWkb.stg rules**

| Rule | Payload |
|---|---|
| `wkb` | signed path vs named HOLD |
| `wkbSigned` | `orderHex` + `typeHex` + payload |
| `countedPoints` | LineString (2) / CircularString (8): count + xy |
| `compoundPayload` | CompoundCurve (9): count + nested child WKB |
| `wkbHold` | CIRCLE / CLOTHOID / empty Point / unsigned codes |

Byte order: `00` XDR (big-endian), `01` NDR (little-endian) — §5.1.68
items fz–ga. Doubles are IEEE-754 binary64; the Java driver fills the
hex fragments, the group only concatenates.

## Shelf A this slice

| Surface | WKT | WKB | Notes |
|---|---|---|---|
| `POINT` | wired | 1 NDR+XDR | `EMPTY` is WKT-only; WKB HOLD this slice |
| `LINESTRING` (+ `EMPTY`) | wired | 2 NDR+XDR | empty = count 0 |
| `CIRCULARSTRING` | wired | 8 NDR+XDR | locked 3-point; bag pts are endpoints |
| `CIRCLE` | wired | HOLD | full-span `MkCirc`; **not** WKB 18 |
| `COMPOUNDCURVE` of LS + CS | wired | 9 NDR+XDR | children keep type; joints are hen ids |
| `CLOTHOID` JTS `(k0,k1,L)` | wired | HOLD | locked intake-smoke form; **not** WKB 22 |
| `CLOTHOID` ISO `REFERENCELOCATION` | wired | HOLD | same `MkClothoid` bag as JTS |
| `GEODESICSTRING` | emits as `LINESTRING` | 2 | τ=`TagLineString` on `MkChord`; **not** TagGeodesic / WKB 13 |

**Stubbed / HOLD (named; not signed I/O):** WKB codes **13–17** and
**18–21**. Not Circle-as-18. Not Clothoid-as-22. Not first-cook expand.
Polygon / Multi / CurvePolygon / MultiCurve / MultiSurface are later
Shelf A rows, not this starter.

Attribute names on the model match intake: `hens`, `pts`, `chickens`
(`src`/`dst`/`egg` = `MkChord`, `MkCirc`, `MkCirc:quarter`,
`MkCirc:full`, `MkClothoid`), plus `keyword`, `controls` (WKT point
list), `children`, `tau`, and clothoid fields (`k0`/`k1`/`L` vs ISO
placement).

## τ and geodesic

`τ = first_slice_tag` (`SqlMmSignedTag.v`): `MkChord ↦ TagLineString`.
A well-formed geodesic CST bags the same `MkChord` chicken as
`LINESTRING`. Factory emit is therefore **LINESTRING text** (and WKB
2). That is an honest chord bag, not silent densify-as-curve, and not
a signed geodesic I/O lane.

## Run

```
bash tools/SqlMmExampleFactory/smoke.sh
bash tools/SqlMmExampleFactory/generate.sh
java -cp tools/SqlMmExampleFactory/.build:tools/SqlMmExampleFactory/.lib/ST4-4.3.4.jar:tools/SqlMmExampleFactory/.lib/antlr-runtime-3.5.3.jar \
  org.nts.proofs.factory.Main --list
java -cp … org.nts.proofs.factory.Main linestring-02
```

μ parse-back uses the **C#** intake (`pwsh tools/WktIntakeWalker/generate.ps1`
+ `dotnet run --project tools/WktIntakeWalker`). Factory emit stays Java
ST4. `tests/SqlMmFactoryHunt` drives the same C# CLI via `HuntHost`.

`generate.sh` downloads `org.antlr:ST4:4.3.4` and its compile
dependency `org.antlr:antlr-runtime:3.5.3` (ANTLR 3 — ST4's own POM)
into `.lib/` (gitignored). There is no Maven reactor for the monorepo.

Smoke asserts:

1. Locked `LINESTRING` / chord bag → WKT parses under the pinned
   grammar and μ bag equals input.
2. Same bags → WKB hex stable for NDR and XDR on Point, LineString,
   CircularString, and CompoundCurve (9).
3. Both clothoid spellings → the locked `MkClothoid` bag.
4. CIRCLE / CLOTHOID WKB stay HOLD strings.

## Hard no (this directory)

- New oracle keyword / ADR-0006 protocol change
- Silent chord densify framed as curve
- WKB 13–17 / 18–21 as signed I/O; Circle-as-18; Clothoid-as-22
- `MkGeodesic` / `geodesic_eval`; unhold #729; first-cook expand
- Remint claimIds `0007-intake-geodesic` / `0007-sqlmm-signed-tag`
