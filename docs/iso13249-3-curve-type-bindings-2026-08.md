# ISO/IEC 13249-3 curve-type bindings vs. NTS `feat/curves-structure-wkt-foundation`

topic: docs
topics: arc, wkt, relate
claimId: none
witness: none
macro: none
issue: none

## Provenance

- **Spec**: ISO/IEC 13249-3:2016 (SQL/MM Part 3: Spatial, 5th edition). The text
  consulted is the DIS ballot text for that edition (ISO/IEC JTC 1/SC 32 N 2593,
  dated 2015-01-25, page footers "ISO/IEC 13249-3:201x(E)"). Clause numbers below
  are from that text; the published IS may differ in wording detail. The spec is
  **copyrighted and is not in this repo** — citations are by clause number only,
  paraphrased, no long verbatim passages.
- **Branch**: `NetTopologySuite` `feat/curves-structure-wkt-foundation` at commit
  `e84458e` ("Merge branch 'develop' into feat/curves-structure-wkt-foundation"),
  clone at `/home/user/NetTopologySuite`. File:line citations are into that tree.
- **Prior distillation**: `EXACT_CURVE_BIBLE.md` (scratchpad; the *JTS Arc-Native
  Programme* bible, CONTEXT.md "Exact curves") was read first. It is an
  architecture document and contains **no ISO clause citations**, so there was
  nothing to verify clause-by-clause; §7 below cross-checks the few
  spec-adjacent statements it does make. This document is therefore a fresh
  distillation from the spec text.
- Citation style: "§7.3.1 Desc 6)" means item 6 of the *Description* rules of
  subclause 7.3.1.

---

## 1. Type hierarchy and instantiability

The binding hierarchy (§4.2, one concept subclause per type; formal `CREATE
TYPE` definitions in clauses 5–8):

| ISO type | Supertype | Instantiable? | Clause (concept / formal) | NTS type on branch |
|---|---|---|---|---|
| ST_Geometry | — | **no** | §4.2.1 / §5.1.1 | `Geometry` (abstract) |
| ST_Curve | ST_Geometry | **no** (`NOT INSTANTIABLE`) | §4.2.4 / §7.1.1 | `Curve` (abstract), `Geometries/Curve.cs:10` |
| ST_LineString | ST_Curve | yes | §4.2.5 / §7.2.1 | `LineString` |
| ST_CircularString | ST_Curve | yes | §4.2.6 / §7.3.1 | `Curves/CircularString.cs:36` |
| ST_CompoundCurve | ST_Curve | yes | §4.2.13 / §7.10.1 | `Curves/CompoundCurve.cs:36` |
| ST_Surface | ST_Geometry | **no** | §4.2.14 / §8.1.1 | `Surface<T>` (abstract), `Geometries/Surface.cs:16` |
| ST_CurvePolygon | ST_Surface | yes | §4.2.15 / §8.2.1 | `Curves/CurvePolygon.cs:38` (`Surface<Curve>`) |
| ST_Polygon | ST_CurvePolygon | yes | §4.2.16 / §8.3.1 | `Polygon` — **not** a `CurvePolygon` subtype in NTS (pre-existing hierarchy; deliberate divergence) |
| ST_MultiCurve | ST_GeomCollection | "may be instantiable" | §4.2.25 | `Curves/MultiCurve.cs:19` |
| ST_MultiSurface | ST_GeomCollection | "may be instantiable" | §4.2.27 | `Curves/MultiSurface.cs:19` |

The spec also defines further instantiable ST_Curve subtypes the branch does not
model: ST_Circle (§4.2.7), ST_GeodesicString (§4.2.8), ST_EllipticalCurve
(§4.2.9), ST_NURBSCurve (§4.2.10), ST_Clothoid (§4.2.11), ST_SpiralCurve
(§4.2.12 — spiral types "initially limited to" clothoid, bloss, biquadratic,
sine, cosine). These are the CONTEXT.md "expansion backlog", verified present in
the spec. §4.2.1 also explicitly permits an implementation to add subtypes and
to interpose types, provided subtype relationships are preserved — this is the
clause that legitimises `Curve`/`Surface<T>` as interposed abstractions.

ST_Curve semantics that bind every curve subtype (§4.2.4):

- 1-dimensional; homomorphic image of a real closed interval; topologically
  closed (all values include their boundary, also §4.2.1).
- *closed* ⇔ start point = end point; *ring* ⇔ simple ∧ closed.
- Boundary: empty set when closed, else {start point, end point}.
- Not simple if any interior point coincides with another interior or boundary
  point.

Branch: `Curve.IsClosed` / `Curve.IsRing = IsClosed & IsSimple` mirror this
exactly (`Geometries/Curve.cs:40,46`); the Mod-2 boundary is implemented per
type (`Curves/CircularString.cs:152-162`, `Curves/CompoundCurve.cs:195-205`).
Note: `IsSimple` currently fails closed (`Operation/Valid/IsSimpleOp.cs:165`),
so `IsRing` on a non-empty curve throws — a known red-marked gap, see §5.

---

## 2. Per-type structural validity

### 2.1 ST_CircularString (§4.2.6, §7.3.1)

- One or more circular arc segments connected end to end. First segment defined
  by three points: start, *any* intermediate point on the arc other than start
  or end, and end. The end point **shall be distinct from** the start point of
  that segment. Subsequent segments supply intermediate + end point only (start
  is the previous end), and the distinctness constraint applies to them too
  (§7.3.1 Desc 6).
- **Well-formedness count**: with NSEG segments, the value is well formed iff
  NumPoints = 2·NSEG + 1 (§7.3.1 Desc 7). So: odd count, ≥ 3.
- **Arc geometry**: non-collinear triple → the arc is the locus of points at
  distance R from the centre, where the centre is the intersection of the
  perpendicular bisectors of CHORD1 (start–intermediate) and CHORD2
  (intermediate–end), and R is the distance from that centre to any of the three
  points; traversal runs start → intermediate → end (§7.3.1 Desc 8a; prose also
  in §4.2.6).
- **Collinear degenerate**: collinear triple → the segment *degenerates to the
  straight line* from start to end; centre and radius are undefined (§7.3.1
  Desc 8b). Collinear inputs are therefore **legal**, not invalid.
- 3 points exactly = "circular arc"; simple ∧ closed = "circular ring" (§7.3.1
  Desc 9–10).
- Empty = zero points (§7.3.1 Desc 11–12).
- Two alternative single-representation forms exist at the SQL level: control
  point + bulge + bulge-normal arrays (§7.3.1 Desc 13), and centre + radius +
  start/end angle, 2D-only, with numeric angle sweep rules (§7.3.1 Desc 14–15).
  Neither has a WKT form; they are constructor/observer surface only
  (ST_Bulge, ST_Center, ST_Radius, ST_StartAngle …, §4.2.6.1).

Branch: constructor enforces "0, or odd and ≥ 3"
(`Curves/CircularString.cs:56-70`) — matches Desc 7. It does **not** enforce
per-segment start≠end distinctness (Desc 6): `CIRCULARSTRING (0 0, 1 1, 0 0)`
constructs. Ill-formed-but-constructible is tolerable only because ST_IsValid
("tests if … well formed", §4.2.1.1 item 9) is the designated checker and NTS
validity checking for curves currently fails closed — the gap belongs to the
IsValid work, not the constructor. No bulge/centre-angle representation exists
on the branch (untracked gap; SQL-level API, low priority for a geometry
library).

### 2.2 ST_CompoundCurve (§4.2.13, §7.10.1)

- A sequence of contiguous curves: the end point of each curve **shall be**
  coincident with the start point of the next (§4.2.13, §7.10.1 Desc 7).
- **Admissible components: all subtypes of ST_Curve** (§7.10.1 Purpose and
  Desc 7) — that includes ST_LineString, ST_CircularString, *and nested
  ST_CompoundCurve* (also admitted explicitly by the WKT grammar, §4 below).
- Well formed if every component is well formed (§7.10.1 Desc 3).
- Simple ∧ closed ⇒ ring (§7.10.1 Desc 8). Empty = zero components (Desc 9–10).
- Components shall not be null (Desc 5); the spec is **silent on empty
  components**.

Branch: contiguity enforced with `Equals2D` at construction
(`Curves/CompoundCurve.cs:75-86`) — consistent with the spec's default 2D
reading of closedness (ST_IsClosed ignores z/m, §4.2.4.1 item 5), though the
spec text for contiguity itself does not say "ignoring z". Empty components
rejected (`CompoundCurve.cs:64-68`) — stricter than the spec, harmless.
**Nested CompoundCurve components rejected** (`CompoundCurve.cs:69-74`;
`IO/WKTReader.cs:1086-1087`; pinned by test
`CurveWktTest.ReadRejectsNestedCompoundCurves`) — this **contradicts** the
spec; see §6.1.

### 2.3 ST_CurvePolygon (§4.2.15, §8.2.1)

- Planar surface: one exterior boundary, zero or more interior boundaries
  (holes) (§4.2.15).
- **Both the exterior ring and every interior ring are ST_Curve values that are
  rings** (§8.2.1 Desc 2–3) — i.e. **closed ∧ simple** per §4.2.4. Any ST_Curve
  subtype may serve (the WKT `<ring text>` admits them all, §4 below).
- Rings may intersect pairwise **at most at a single point** (§8.2.1 Desc 11,
  given as a point-set formula); no cut lines, spikes, punctures
  (Desc 12: p = Closure(Interior(p))); interior connected (Desc 13); each hole
  disconnects the exterior (Desc 14); values are simple (Desc 8) and
  topologically closed (Desc 10, 15).
- Empty ⇔ exterior ring empty (Desc 17). Well formed only if all rings are well
  formed (Desc 18).

Branch: constructor enforces **closed** rings only
(`Curves/CurvePolygon.cs:96-108`); simplicity, ring non-crossing, and the
interior-connectivity conditions are ST_IsValid territory and currently fail
closed (`IsSimpleOp.cs:165`). Ring accessors stay typed `Curve` and never
collapse to `LinearRing` (the F-CP contract, `CurvePolygon.cs:27-31`) —
compatible with §8.2.1, which types the ring attributes as ST_Curve. Empty ⇔
empty shell matches Desc 17 (`CurvePolygon.cs:138`).

---

## 3. The semantics behind the four Red tests

The branch's four deliberately-red contract tests
(`test/NetTopologySuite.Tests.NUnit/Geometries/Curves/CurveMetricsContractTests.cs`)
each encode a spec obligation. What the spec *actually* requires, honestly:

### 3.1 Length — `Red_Length_UnitSemicircle_IsPi` (:101)

§7.1.2 (ST_Length Methods, on ST_Curve) Desc 2a: empty → null; otherwise
"return the implementation-defined length of SELF". **The computation is
implementation-defined, but the operand is not**: for a non-collinear
CircularString value, SELF *is* the circular-arc locus of §7.3.1 Desc 8a — not
the control polyline. The length of the unit upper semicircle's locus is π; the
control-polyline value 2√2 is the length of a different point set, so returning
it would not be "the length of SELF" under any reading. The spec nowhere gives
an arc-length formula (r·θ is our derivation from the locus definition, not a
quoted rule) — the test's `Within(1e-9)` tolerance is a quality bar, not a
clause. Branch today: `CircularString.Length` throws
(`Curves/CircularString.cs:139-140`) — fail-closed, red-marked.

### 3.2 Distance — `Red_Distance_PointToCircularString_CentreOfUnitSemicircle_IsRadius` (:68) and `..._Endpoint_IsZero` (:85)

§5.1.41 (ST_Distance Methods, on ST_Geometry) Desc 2a: empty operand → null;
**"if SELF and ageometry spatially intersect, then return 0" is normative and
carries no implementation latitude** — the endpoint test (the point (1,0) lies
on the arc, arcs are topologically closed per §4.2.1/§4.2.4) is grounded
directly by Desc 2a-iii. Otherwise return "the distance between two
geometries", with the point-to-point distance algorithm implementation-defined
(Desc 2a-iv). The centre-of-semicircle expectation (distance = r = 1) follows
from §7.3.1 Desc 8a: every point of the locus is at distance R from the centre,
so the geometry-to-geometry minimum is exactly R — the clause delegates the
*algorithm*, not *which point set* is measured. Branch today: `DistanceOp`
fails closed for curved inputs (`Operation/Distance/DistanceOp.cs:98-99`).

### 3.3 Envelope — `Red_Envelope_IncludesAxisExtremeBeyondControls` (:113)

§5.1.19 (ST_Envelope Method, on ST_Geometry — **inherited, not arc-specific;
there is no curve override**) Desc 2b: MINX/MINY/MAXX/MAXY are the minimum and
maximum x/y coordinate values **"in the ST_Geometry value"** — i.e. over the
value's point set, which for a CircularString is the arc locus (§7.3.1 Desc 8).
An arc sweeping −30°…50° on the unit circle contains (1, 0), so MAXX = 1 even
though no control point reaches it. Unlike Length/Distance, §5.1.19 contains
**no implementation-defined escape** for the extremes; a control-point bbox is
simply the envelope of the wrong point set. Two further §5.1.19 details that
bind the SQL-level result shape (informative for NTS's `Envelope` struct, which
is a different surface): degenerate extents are widened by an
implementation-defined ETOL > 0 so the result is always a proper rectangle
(Desc 2c–2e), and the result is an ST_Polygon in the same SRS (Desc 2f, 5).
Branch today: `ComputeEnvelopeInternal` throws for non-empty curves
(`Curves/CircularString.cs:165-169`, `Curves/CompoundCurve.cs:208-212`).

### 3.4 Linearisation (the sanctioned escape hatch)

§7.1.10 (ST_CurveToLine): returns "the implementation-defined ST_LineString
value approximation" of the curve; z considered, m re-interpolated by curve
length (Desc 3–4). This is the spec's own chainsaw: approximation is legitimate
**only** through this named method — which is exactly the house rule
(CONTEXT.md "Chainsaw"; Bible §2.3 "no silent linearisation"). Branch:
`Linearize()` is the explicit chord form (`Curves/CircularString.cs:284-291`);
tolerance-driven `Linearize(double)` not yet implemented
(`CircularString.cs:303-306`). §8.2.7 ST_CurvePolyToPoly is the surface
counterpart, mapped by `CurvePolygon.Linearize()`.

---

## 4. WKT / WKB grammar (§5.1.67, §5.1.68)

### 4.1 WKT (§5.1.67)

Token grammar (BNF in §5.1.67 Desc 1; production-to-value rules in the lettered
items that follow it):

- `CIRCULARSTRING [ <z m> ] <circularstring text>` where `<circularstring
  text>` is `EMPTY` or a parenthesised comma-separated point list. The grammar
  itself admits any count ≥ 1; the odd-count ≥ 3 rule is semantic
  well-formedness (§7.3.1 Desc 7), enforced when the produced point array feeds
  `NEW ST_CircularString` (§5.1.67 item e).
- `COMPOUNDCURVE [ <z m> ] <compoundcurve text>`, components are `<curve
  text>` ::= **bare** `<linestring text body>` (a parenthesised point list with
  *no* LINESTRING keyword) | tagged `<circularstring text representation>` |
  tagged circle/geodesic/elliptical/nurbs/clothoid/spiral representations |
  **tagged `<compoundcurve text representation>`** — nested COMPOUNDCURVE is in
  the grammar (production `<curve text>`, mapping rule item ck-ix).
- `CURVEPOLYGON [ <z m> ] <curvepolygon text>`, rings are `<ring text>` with
  exactly the same alternatives as `<curve text>` (bare linestring body, tagged
  curve representations, COMPOUNDCURVE included; mapping rule item cl).
- `<empty set> ::= EMPTY`; an EMPTY body produces the empty value of the tagged
  type (items e, l, ad).
- `<z m> ::= ZM | Z | M`; every WKT nested inside a WKT that carries `<z m>`
  shall carry the **same** `<z m>` (§5.1.67 dimension-consistency rules).
- Terminal characters (`<left paren>`, `<space>`, `<comma>`, numbers, letters)
  are delegated to ISO/IEC 9075-2 §5.1/§5.3. **The spec is silent on keyword
  case**; all keywords are written uppercase in the BNF. (SQL string
  comparison semantics would make lowercase input non-matching; treat
  "uppercase out, tolerant in" as the safe posture.)

Branch: keywords `WKTConstants.cs:47-63`; reader dispatch
`IO/WKTReader.cs:768-773`; component/ring parsing `ReadCurveText`
(`WKTReader.cs:1061-1094`) accepts the bare linestring body and tagged
CIRCULARSTRING per grammar, **rejects nested COMPOUNDCURVE inside
COMPOUNDCURVE** (contradiction, §6.1) while allowing COMPOUNDCURVE as a
CURVEPOLYGON/MULTICURVE ring or member (`WKTReader.cs:1188-1204`, matching
`<ring text>`). It additionally accepts a **tagged** `LINESTRING` component
(`WKTReader.cs:1071-1075`) — an input-side extension beyond the ISO grammar,
documented in-code as GEOS/PostGIS compatibility; the writer emits conformant
bare bodies for LineString components and tags for CircularString
(`IO/WKTWriter.cs:1046-1070`), so output is grammar-clean. Keyword matching is
case-insensitive on input (`OrdinalIgnoreCase`), uppercase on output —
consistent with the safe posture above. EMPTY round-trips for all three types
(`CurveWktTest.cs:23,26,30`).

### 4.2 WKB (§5.1.68)

Structure: `<byte order> <type code> [ <num> <elements>... ]`; CircularString
elements are points, CompoundCurve elements are `<wkbcurve binary>` (each with
its own byte order + type code), CurvePolygon elements are `<wkbring binary>`.
Type codes (§5.1.68 Table 15):

| Type | 2D | Z | M | ZM |
|---|---|---|---|---|
| CircularString | 8 (or 1000001) | 1008 | 2008 | 3008 |
| CompoundCurve | 9 (or 1000002) | 1009 | 2009 | 3009 |
| CurvePolygon | 10 (or 1000003) | 1010 | 2010 | 3010 |
| MultiCurve | 11 (or 1000004) | 1011 | 2011 | 3011 |
| MultiSurface | 12 (or 1000005) | 1012 | 2012 | 3012 |

Byte-order bytes: 0 = big endian, 1 = little endian (§5.1.68 items fz–ga).

Branch: base codes 8–12 in `IO/WKBGeometryTypes.cs:63-83`; the +1000/+2000/+3000
Z/M offsets are decoded generically (`IO/WKBReader.cs:283,297`). The alternate
`100000x` code series that Table 15 lists as a second legal encoding is **not**
decoded (`(type & 0xffff) % 1000` cannot recover it) — acceptable in practice
(no known producer), recorded here for completeness.

---

## 5. Mapping table: ISO rule → branch → gap

| ISO rule (clause) | Branch behaviour (file:line) | Status |
|---|---|---|
| ST_Curve / ST_Surface not instantiable (§7.1.1, §8.1.1) | `Curve`, `Surface<T>` abstract (`Geometries/Curve.cs:10`, `Geometries/Surface.cs:16`) | ok |
| ring = closed ∧ simple (§4.2.4) | `Curve.IsRing` (`Curve.cs:40`); `IsSimple` fails closed (`Operation/Valid/IsSimpleOp.cs:165`) | definition ok; evaluation red-marked |
| CS well-formed ⇔ 2n+1 points, ≥3 (§7.3.1 Desc 7) | ctor enforces 0 or odd ≥3 (`CircularString.cs:56-70`) | ok |
| CS arc end ≠ arc start per segment (§7.3.1 Desc 6) | not enforced anywhere | **gap** — spec "shall"; belongs to IsValid work |
| CS collinear triple → straight-line segment (§7.3.1 Desc 8b) | no arc math yet; semantics unimplemented | pending (metrics follow-up) |
| CS bulge / centre-radius-angle representations (§7.3.1 Desc 13–15) | absent | untracked gap (SQL API surface; optional for NTS) |
| CC components: **all** ST_Curve subtypes, nested CC included (§7.10.1 Desc 7; §5.1.67 `<curve text>`) | rejected (`CompoundCurve.cs:69-74`, `WKTReader.cs:1086-1087`; test `CurveWktTest.ReadRejectsNestedCompoundCurves`) | **contradiction** — see §6.1 |
| CC contiguity: end = next start (§7.10.1 Desc 7) | `Equals2D` check in ctor (`CompoundCurve.cs:75-86`) | ok (2D reading; spec default closedness is 2D, §4.2.4.1) |
| CC empty components (spec silent; only null forbidden, §7.10.1 Desc 5) | rejected (`CompoundCurve.cs:64-68`) | stricter than spec, harmless |
| CP rings are rings = closed ∧ simple, any ST_Curve (§8.2.1 Desc 2–3) | ctor: closed only (`CurvePolygon.cs:96-108`); simplicity deferred | partial; red-marked via IsSimple |
| CP ring intersection ≤ 1 point, no spikes/cuts, connected interior (§8.2.1 Desc 11–14) | not evaluated (IsValid fail-closed) | known gap (IsValid work) |
| ST_Length on curves (§7.1.2 Desc 2; operand = arc locus §7.3.1 Desc 8) | throws (`CircularString.cs:139-140`, `CompoundCurve.cs:188-189`) | red: `Red_Length_UnitSemicircle_IsPi` |
| ST_Distance: intersect → 0; else min distance (§5.1.41 Desc 2a) | `DistanceOp` fails closed (`DistanceOp.cs:98-99`) | red: `Red_Distance_..._Endpoint_IsZero` (Desc 2a-iii), `Red_Distance_..._CentreOfUnitSemicircle_IsRadius` (Desc 2a-iv + §7.3.1 Desc 8a) |
| ST_Envelope: extremes over the value's point set (§5.1.19 Desc 2b) | `ComputeEnvelopeInternal` throws (`CircularString.cs:165-169`) | red: `Red_Envelope_IncludesAxisExtremeBeyondControls` |
| ST_CurveToLine / ST_CurvePolyToPoly explicit approximation (§7.1.10, §8.2.7) | `Linearize()` (`CircularString.cs:284-291`); tolerance overload throws (`CircularString.cs:303-306`) | ok as chainsaw; tolerance form pending |
| WKT grammar incl. bare linestring bodies, EMPTY, Z/M (§5.1.67) | reader/writer (`WKTReader.cs:768-773,1061-1204`, `WKTWriter.cs:1002-1096`) | ok; input-side tagged-LINESTRING extension (GEOS/PostGIS compat) |
| WKB Table 15 codes + Z/M offsets (§5.1.68) | `WKBGeometryTypes.cs:63-83`, `WKBReader.cs:283,297` | ok; alternate 100000x codes unsupported |

---

## 6. Where the spec contradicts or is stricter than the branch

### 6.1 Nested CompoundCurve — the branch contradicts the spec (warn)

§7.10.1 (Purpose and Desc 7): "the contributing curve types include **all
subtypes of ST_Curve**" — ST_CompoundCurve is itself a subtype of ST_Curve, and
the WKT grammar makes the admission explicit: `<curve text>` includes
`<compoundcurve text representation>` (§5.1.67, mapping item ck-ix), likewise
`<ring text>` (item cl-ix). The branch rejects nested components in the
constructor (`CompoundCurve.cs:69-74`), rejects them in the parser
(`WKTReader.cs:1086-1087`), pins the rejection in a test
(`CurveWktTest.ReadRejectsNestedCompoundCurves`), and — the actual defect — its
doc comment claims the flat list is "matching SQL/MM and common
implementations" (`CompoundCurve.cs:27-29`). The "common implementations" half
is true (PostGIS/GEOS flatten or reject); the "SQL/MM" half is false. Design
options for the interview: keep the restriction but fix the comment (document
it as a deliberate deviation), or accept-and-flatten on input (what PostGIS
does), or model nesting. What is not tenable is citing SQL/MM for the
rejection.

### 6.2 Arc-segment endpoint distinctness — spec stricter than the branch

§7.3.1 Desc 6 says each arc segment's end point **shall** be distinct from its
start point (a closed single "arc" is ST_Circle's job, §4.2.7). The branch
constructs such values without complaint (`CircularString.cs:50-72` checks
count only). Not a behavioural contradiction — NTS defers value validity to
`IsValid`, which fails closed — but the rule must land in arc-aware
IsValid/IsSimple, and constructor-level enforcement is worth the interview's
attention (it is cheap: pairwise `Equals2D` per segment).

### 6.3 Ring simplicity for CurvePolygon — spec stricter than the constructor

§8.2.1 Desc 2–3 require rings (closed **and simple**); the branch checks closed
only (`CurvePolygon.cs:96-108`). Same posture as 6.2: fine while IsValid fails
closed, must not be forgotten when it stops failing closed.

### 6.4 Envelope of degenerate extents — SQL-level rule, note only

§5.1.19 Desc 2c–e mandate widening a zero-width/height envelope by ETOL so
ST_Envelope always returns a proper rectangle. NTS's `Envelope`/
`EnvelopeInternal` intentionally represents degenerate extents; if an
SQL/MM-conformant `ST_Envelope`-shaped API is ever exposed, the widening
belongs there, not in `Envelope`.

### 6.5 Fail-closed metrics vs. spec-required answers

ST_Length, ST_Distance, ST_Envelope are total over non-empty values in the
spec; the branch throws `NotSupportedException`. This is a deliberate,
documented, red-test-marked interim (headers of `CircularString.cs:10-14`,
`CurveMetricsContractTests.cs:2-6`), preferred over silently returning
chord-approx numbers — which would satisfy the type signature while violating
§7.3.1 Desc 8's definition of the value being measured. The Red tests are the
spec's side of that contract.

---

## 7. Cross-check against EXACT_CURVE_BIBLE.md

The Bible is architecture, not spec exegesis; it cites no ISO clauses. Its
spec-adjacent statements, checked:

- "Colinear 3-control windows degrade to an exact chord" (Implementation notes)
  — **verified**: §7.3.1 Desc 8b says exactly this for the value semantics.
- "No silent linearisation … `toLinear(tolerance)` is the only densify path"
  (§2.3, notes) — **consistent with** the spec's structure: approximation
  exists only as the named methods ST_CurveToLine (§7.1.10) and
  ST_CurvePolyToPoly (§8.2.7); no metric clause authorises approximating the
  operand.
- CONTEXT.md "Zoo" backlog list (SPIRALCURVE's bloss, biquadratic, sine,
  cosine; CIRCLE; GEODESICSTRING) — **verified**: §4.2.12 (spiral types
  "initially limited to clothoid, bloss, biquadratic, sine and cosine"),
  §4.2.7, §4.2.8.
- Everything else in the Bible (ExactCurve protocol, 1.15× ratchet, package
  layout) is out of the spec's scope — neither confirmed nor contradicted.

## 8. Claims not fully grounded in the spec text (honesty ledger)

- **WKT keyword case-insensitivity**: the spec never states it; terminals
  delegate to ISO/IEC 9075-2. NTS's case-insensitive reading is a compatibility
  choice, not a clause. Marked unverified.
- **r·θ as "the" arc length and 1e-9 tolerances**: derived from the locus
  definition (§7.3.1 Desc 8a) + §7.1.2; the spec states no formula and no
  precision. The Red tests' numeric expectations are quality bars.
- **Nested-tag `<z m>` consistency enforcement in the NTS reader** (spec rule
  in §5.1.67): not audited on the branch; only outer-tag Z round-trip is
  test-covered (`CurveWktTest.ReadSupportsZOrdinates`).
- **Published-IS wording**: citations are from the DIS ballot text of the 5th
  edition (N 2593). No claim here was found only in ballot-specific front
  matter, but clause-item numbering in the published 2016 IS could differ.

---

SUMMARY warn — branch rejects nested COMPOUNDCURVE components and mis-attributes that restriction to SQL/MM (`CompoundCurve.cs:27-29,69-74`, `WKTReader.cs:1086-1087`) while §7.10.1 Desc 7 and §5.1.67 `<curve text>`/`<ring text>` admit them; all other divergences are either red-test-marked fail-closed gaps (Length §7.1.2, Distance §5.1.41, Envelope §5.1.19 — the four Red tests in `CurveMetricsContractTests.cs`) or deferred-validity gaps (§7.3.1 Desc 6 distinctness, §8.2.1 ring simplicity) awaiting arc-aware IsValid/IsSimple.
