# Guardrails from CurvePolygon self-overlay dumps

**Source.** FunctionRegistry / overlay-function bench on identical inputs
`G = CurvePolygon[5]` (five vertices on the curved shell; `TypeName[NumPoints]`
notation as printed by the runner).

**Canonical Phase 0 suite + CAP/CUP/SUB/XOR mnemonics:**  
[`docs/overlay-ng-curve-ops-mnemonics.md`](overlay-ng-curve-ops-mnemonics.md)
(G1 CAP · G2 CUP · G3 SUB · G4 XOR · G5 empty partner · V/R/F policies).

**Spec home.** Point-set algebra is `theories/Overlay.v` (`boolean_op`);
self-op lemmas:

| Lemma | Sticky | Spec |
|-------|--------|------|
| `boolean_op_intersection_self` | **CAP** ∩ | `A ∩ A = A` (G1) |
| `boolean_op_union_self` | **CUP** ∪ | `A ∪ A = A` (G2) |
| `boolean_op_difference_self_empty` | **SUB** ∖ | `A \ A = ∅` (G3) |
| `boolean_op_symdiff_self_empty` | **XOR** Δ | `A Δ A = ∅` (G4) |

These are the **semantic guardrails**. Implementations may change representation
(curve → linearised polygon) but must not invent interior for difference/symDiff
or drop the body of a self-intersection.

---

## 1. Algebraic checks (run on every overlay path)

For a non-empty valid geometry `G` and path `Op` (classic / OverlayNG / …):

| # | Guardrail | Predicate (NTS) | Spec |
|---|-----------|-----------------|------|
| G1 | self-difference empty | `Op.difference(G,G).IsEmpty` | `A \ A = ∅` |
| G2 | self-differenceBA empty | `Op.differenceBA(G,G).IsEmpty` | `B \ A` with `A=B` |
| G3 | self-symDifference empty | `Op.symDifference(G,G).IsEmpty` | `A Δ A = ∅` |
| G4 | self-intersection covers G | `Op.intersection(G,G).EqualsTopo(G)` *or* same coverage + area | `A ∩ A = A` |
| G5 | self-union covers G | `Op.union(G,G).EqualsTopo(G)` (or unaryUnion) | `A ∪ A = A` |
| G6 | no crash / non-null | result not null; op completes | — |

**Soft (representation) checks** — failures are degradations, not necessarily
point-set wrong:

| # | Guardrail | Predicate |
|---|-----------|-----------|
| R1 | curve retention | preferred paths keep `CurvePolygon` when both inputs are CP |
| R2 | no linearise explosion | `result.NumPoints` within a small factor of `G.NumPoints` (e.g. ≤ 4× for NG; classic may explode) |
| R3 | unaryUnion identity | `unaryUnion(G)` equals `G` (type + topology) |

---

## 2. Scorecard from the pasted dump (`G = CurvePolygon[5]`)

Legend: **pass** / **fail** / **degrade** (type or size only) / **blank** (no result line — treat as fail/timeout until confirmed).

### Emptiness laws (hard)

| Path | G1 difference | G2 differenceBA | G3 symDifference |
|------|---------------|-----------------|------------------|
| Overlay (classic) | **fail** `Polygon[3146]` | **pass** `Polygon[0]` | **fail** `Polygon[3146]` |
| OverlayNG | blank | **pass** `Polygon[0]` | **fail** `Polygon[10]` |
| OverlayNGOpt | **fail** `Polygon[10]` | — | — |
| OverlayNGRobust | **fail** `Polygon[10]` | **pass** `Polygon[0]` | **fail** `Polygon[10]` |
| OverlayNGSR (10) | **fail** `Polygon[10]` | **pass** `Polygon[0]` | **fail** `Polygon[10]` |
| OverlayNGSnapping (10) | blank | — | — |
| OverlayNGStrict | blank | **pass** `Polygon[0]` | **fail** `Polygon[10]` |
| OverlayNoSnap | **fail** `Polygon[10]` | **pass** `Polygon[0]` | **fail** `Polygon[10]` |

**Extracted rule:** almost every modern path keeps **G2** (differenceBA empty)
but **breaks G1/G3** (self-difference / self-symDiff non-empty, often
`Polygon[10]`). Classic Overlay is worst (thousands of points of junk).

### Idempotent laws (hard, up to EqualsTopo)

| Path | G4 intersection | G5 union / unaryUnion |
|------|-----------------|------------------------|
| Overlay | degrade `Polygon[1573]` (linearised bulk) | degrade `Polygon[1573]`; **unaryUnion pass** `CurvePolygon[5]` |
| Overlay.unionUsingGeometryCollection | — | degrade `Polygon[5]` |
| OverlayNG | degrade/ok `Polygon[5]` | blank union |
| OverlayNGOpt (+ prep variants) | **pass** type `CurvePolygon[5]` | — |
| OverlayNGRobust / SR / NoSnap | degrade `Polygon[5]` | degrade `Polygon[5]` |
| OverlayNGSnapping.intersection | **fail** `Polygon[0]` | blank |

**Extracted rules:**

1. **unaryUnion** is the clean identity on this sample — good regression anchor.
2. **OverlayNGOpt.intersection\*** family preserves **CurvePolygon[5]** — best
   curve-fidelity intersection guardrail.
3. **Snapping intersection → empty** is a red-line failure (G4 false).
4. Classic **1573 / 3146** NumPoints is a linearisation explosion R2 fail;
   use as a *ceiling* guard only for non-classic paths.

### Diagnostic / edge dumps (not full boolean_op)

`OverlayNGTest.edges*` → MultiLineString/LineString noding views; useful for
noding guardrails (edge count stable under self-pair) but not G1–G5.

`PolygonOverlay.overlay` → `GeometryCollection[15]` — collection packing of
labelled faces; separate contract.

---

## 3. Minimal NUnit / xUnit sketch

```csharp
// For each IOverlayPath path under test:
void AssertSelfOverlayGuardrails(Geometry g, IOverlayPath path)
{
    Assert.That(path.Difference(g, g).IsEmpty, Is.True, "G1 A\\\\A");
    Assert.That(path.Difference(g, g) /* BA if API */, Is.Empty, "G2"); // if exposed
    Assert.That(path.SymDifference(g, g).IsEmpty, Is.True, "G3 AΔA");
    Assert.That(path.Intersection(g, g).EqualsTopo(g), Is.True, "G4 A∩A");
    Assert.That(path.Union(g, g).EqualsTopo(g), Is.True, "G5 A∪A");
}
```

Split suites:

- **Hard gate (must pass for “correct” label):** G1, G2, G3.
- **Topo gate:** G4, G5 with `EqualsTopo` / area+covers.
- **Fidelity gate (curve paths only):** R1 + R2 with bound e.g. `NumPoints ≤ 20` for input 5.

---

## 4. What to pin in the proofs corpus

Already cheap and landed next to the existing comm lemmas in `Overlay.v`:

- self-idempotence and self-emptiness of `boolean_op` (no Jordan needed).

Still open (engine-facing):

- A bridge hypothesis “`extract` implements `boolean_op`” + self-op
  specialisation ⇒ `IsEmpty` / coverage corollaries once extraction is
  hooked for curve inputs.

---

## 5. One-line summary for CI badges

> On any self-pair `G⋆G`: **difference and symDifference must be empty**;
> **intersection and union must cover G**; **differenceBA empty** is the
> one law current OverlayNG already holds consistently; **do not accept
> snapping self-intersection → empty** or classic **NumPoints ≫ |G|** as
> green for curved inputs.

---

## 6. Adversarial pair: concentric disks with a scrambled CIRCULARSTRING

### Inputs (as pasted)

```text
A: CURVEPOLYGON (CIRCULARSTRING (
     5 0, 2.5 4.330127019, -2.5 4.330127019, -5 0,
     -2.5 -4.330127019, 2.5 -4.330127019, 5 0))

B: CURVEPOLYGON (CIRCULARSTRING (
     3 0, -1.5 -2.598076211, 1.5 -2.598076211, -3 0,
     1.5 2.598076211, -1.5 2.598076211, 3 0))
```

### Geometry diagnosis (why “almost all errors”)

| | **A** | **B (as written)** |
|---|--------|---------------------|
| Radii of vertices | all 5 | all 3 |
| Angular steps (atan2) | **+60° six times** (CCW hex sample) | **240°, 60°, 240°, 240°, 60°, 240°** (scrambled) |
| CircularString arcs | 3× **minor** ~120° on the r=5 circle | mix of **~300° / ~240° major** arcs |
| Total oriented arc span | **360°** (one simple cover) | **~840°** (multi-cover + direction flips) |
| Intended shape? | disk radius 5 at origin | *not* the disk radius 3 — path is not a simple boundary |

So **A is a well-formed circular disk shell**. **B is not a smaller concentric disk**:
the control-point order walks the r=3 circle in a non-monotone way, so each
SQL/MM arc (start–mid–end on the same circle) takes the long way / reverses.
Overlay then nodes a self-overlapping multi-wound curve against a clean disk
→ exceptions, empty junk, or huge linearised garbage on almost every path.

This is a **precondition / validity** failure more than an overlay-algebra failure.
Guardrails G1–G5 assume valid simple-feature polygons; they do not apply until
both inputs pass ring simplicity / winding checks.

### Correct concentric B (CCW, same sampling style as A)

```text
B_fix: CURVEPOLYGON (CIRCULARSTRING (
  3 0, 1.5 2.598076211, -1.5 2.598076211, -3 0,
  -1.5 -2.598076211, 1.5 -2.598076211, 3 0))
```

Angular steps: +60° × 6. Total span 360°. Nested disks: `B_fix ⊂ A`.

Expected algebra (point-set, ideal):

| Op | Result |
|----|--------|
| `A ∩ B_fix` | `B_fix` (disk r=3) |
| `A ∪ B_fix` | `A` (disk r=5) |
| `A \ B_fix` | annulus |
| `B_fix \ A` | empty |
| `A Δ B_fix` | annulus |

### Extra guardrails for curve inputs

| # | Guardrail | Check |
|---|-----------|--------|
| **V0** | WKT parse succeeds | reader does not throw |
| **V1** | `IsValid` / curve validation | reject multi-wound CIRCULARSTRING shells |
| **V2** | Monotone polar order (disk samples) | consecutive vertex angles advance with constant sign and total ~±360° for a single circle shell |
| **V3** | Per-arc central angle | prefer minor arcs for “round disk” fixtures (`|Δθ| ≤ π` per SQL/MM arc) unless explicitly testing major arcs |
| **V4** | Fixture liveness | known-good pair `A` vs `B_fix` must pass G1–G5 on at least one OverlayNG path before blaming the engine |

### Regression split

1. **Negative fixture** — keep **B as written** under `InvalidOrPathologicalCurvePolygon`;
   assert validator fails *or* document “overlay undefined / may throw”.
2. **Positive fixture** — `A` vs `B_fix` for boolean overlay + curve-fidelity (R1).
3. Do not mix them: scrambled **B** will make “almost all errors” look like
   engine regressions when the shell itself is not a simple ring.

---

## 7. Scorecard: `G = CurvePolygon[7]` self-pair dump

Same runner notation `TypeName[NumPoints]`. Two waves appear in the log:
(1) many ops finish with **no result line** (exception / empty print —
treat as **G6 fail**); (2) a second pass prints classic explosion sizes
identical to the CP[5] linearised path (**1573 / 3146**).

### Edit path (not boolean_op, but related)

| Call | Result | Notes |
|------|--------|--------|
| `Edit.addHole(G, G)` | `CurvePolygon[14]` | Shell copied in as a hole: 7+7 points. Point-set of “polygon with itself as hole” is empty / invalid for OGC; **do not** use as a green identity. Guardrail **E1:** `addHole(G,G)` should reject (hole not interior / equal ring) or fail validation. |

### Hard emptiness (second pass, where printed)

| Path | G1 difference | G2 differenceBA | G3 symDifference |
|------|---------------|-----------------|------------------|
| Overlay | **fail** `Polygon[3146]` | **pass** `Polygon[0]` | **fail** `Polygon[3146]` |
| OverlayNG | **fail** `Polygon[3146]` | **pass** `Polygon[0]` | **fail** `Polygon[3146]` |
| OverlayNGRobust | **fail** `Polygon[3146]` | **pass** `Polygon[0]` | **fail** `Polygon[3146]` |
| OverlayNGOpt | **fail** `Polygon[14]` | — | — |

Same pattern as CP[5]: **G2 holds; G1/G3 die**, now with the **full classic
explosion** on NG/Robust too (not just `Polygon[10]`). Opt difference is
smaller junk (`[14]`) but still **not empty**.

### Idempotence / fidelity (printed)

| Path | G4 intersection | G5 union | R1 curve keep | R2 size |
|------|-----------------|----------|---------------|---------|
| OverlayNGOpt.intersection\* (all prep/SR variants) | **pass** type `CurvePolygon[7]` | — | **pass** | **pass** (7) |
| Overlay / OverlayNG / Robust intersection | linearise `Polygon[1573]` | linearise `Polygon[1573]` | fail | **fail** (225×) |
| Overlay.clip | `Polygon[1573]` | — | fail | fail |

### First-pass blanks (G6)

First block: `OverlayNG.{difference,differenceBA,intersection,symDifference,union}`,
classic Overlay ops, `unionUsingGeometryCollection` (662 ms), and a long
`OverlayNGRobust.*` burst (~300 ms) with **no `==>` line**. Second block
prints results for the same names. Guardrail:

| # | Guardrail | Predicate |
|---|-----------|-----------|
| **G6** | completes with a geometry | non-null result; no throw |
| **G6b** | deterministic print | same op twice → same type/size (or document flaky path) |

**G6b** is live here: first NGRobust wave blank/slow, second wave returns
`Polygon[3146]` etc. Treat dual outcomes as a **registry flaky** flag.

### What this dump adds beyond CP[5]

1. **Opt intersection is the only consistently green family** on self-CP —
   type-preserving identity (`CurvePolygon[7]`). Pin these as the R1/G4
   gold path for curved self-pairs.
2. **NG/Robust now match classic explosion** on this 7-pt shell (1573/3146),
   worse than the earlier CP[5] NG `Polygon[5]`/`[10]` regime — linearise
   width depends on fixture, so R2 bounds must be **fixture-keyed**, not a
   global “NG is small” assumption.
3. **Opt.difference → Polygon[14]** is a new mid-size failure mode (≈2×
   input points, not empty): still G1 fail, good unit for a reduced red.
4. **addHole(G,G) → CP[14]** is a separate edit guardrail (reject or invalid).

### Minimal asserts for this fixture

```text
G1  difference(G,G).IsEmpty
G2  differenceBA(G,G).IsEmpty          // currently green
G3  symDifference(G,G).IsEmpty
G4  Opt.intersection(G,G) is CurvePolygon && EqualsTopo(G)  // currently green
G6  every registered Op returns non-null (no silent blank)
E1  addHole(G,G) throws or result.IsValid == false
R2  if Type == Polygon after self-op, flag NumPoints > 50 as explosion
```

---

## 8. RGR land: `OverlayNGCurve` (NetTopologySuite.Curve)

**Branch (Curve repo):** `feat/overlay-ng-curve-rgr`  
**Mnemonics:** [`overlay-ng-curve-ops-mnemonics.md`](overlay-ng-curve-ops-mnemonics.md)

| Phase | Deliverable |
|-------|-------------|
| **Red** | `OverlayNGCurveSelfOpTest` — G1 CAP · G2 CUP · G3 SUB · G4 XOR · G5 empty · F1 clones · V3 name |
| **Green** | `OverlayNGCurve` — F1 short-circuit before flatten; CAP/CUP → `Copy()`; SUB/XOR → empty |
| **Refactor** | `CurveV2` alias; services wire `OverlayNGCurve`; never `Curved` (NTSC0001) |

**Green:** G1–G4 (+ F1 / R1 self), partial G5 via base empty cases.  
**Open:** V1 wound · V2 hole nest · R2 approx flag · true curve noding for A ≠ B.

