# OverlayNGCurve · ops mnemonics

**Name:** `OverlayNGCurve` (NTSC0001: never `OverlayNGCurved`)

**Homes:**

- Implementation: `NetTopologySuite.Curve` → `CurveGeometryOverlay.OverlayNGCurve`
- Spec algebra: `theories/Overlay.v` (`boolean_op_*_self*`)
- Empirical scorecards: `docs/curve-polygon-self-overlay-guardrails.md`

---

## Four ops

| Sticky | Symbol | Method | Phrase | Self-op |
|--------|--------|--------|--------|---------|
| **CAP** | ∩ | `intersection` | **C**ommon **A**rea of **P**artners — only where both stand | G1 · A ∩ A → A  (I meet myself → me) |
| **CUP** | ∪ | `union` | **C**over **U**nder **P**artners — either side fills the cup | G2 · A ∪ A → A  (double pour → same cup) |
| **SUB** | ∖ | `difference` | **S**ubtract B’s shadow — erase the second from the first | G3 · A ∖ A → ∅  (erase myself → empty) |
| **XOR** | Δ | `symDifference` | e**X**clusive **OR** — keep only what isn’t shared | G4 · A Δ A → ∅  (mirror cancel → empty) |

---

## Phase 0 suite

### Self-ops & empty partner

| Id | Sticky | Phrase | Spec |
|----|--------|--------|------|
| **G1** | CAP self | *I meet myself → me* | A ∩ A → A (same instance / `EqualsExact` curve) |
| **G2** | CUP self | *Double pour → same cup* | A ∪ A → A |
| **G3** | SUB self | *Erase myself → empty* | A ∖ A → ∅ |
| **G4** | XOR self | *Mirror cancel → empty* | A Δ A → ∅ |
| **G5** | Empty partner | *Nothing in the room* | A ∩ ∅ → ∅ · A ∪ ∅ → A · A ∖ ∅ → A · ∅ ∖ A → ∅ |

### Preconditions & policy

| Id | Name | Phrase | Spec |
|----|------|--------|------|
| **V1** | Wound check | *No scrambled shell* | Reject multi-wound / self-crossing structural shells before noding |
| **V2** | Hole nest | *Holes live inside* | Hole rings properly interior to shell (curve-aware envelope) |
| **V3** | Type gate | *Curve path for Curve\** | Lineal/`Curve*` inputs take **OverlayNGCurve** — never silent stock NG only |
| **R1** | Keep the arc | *Retention when representable* | Both CP + result representable as CP → return `CurvePolygon`, not dense `Polygon` |
| **R2** | Honest approx | *Flag when densified* | `Linearize(tol)`+OverlayNG must set approx / document non-exact |
| **F1** | Fast before fat | *Short-circuit before densify* | G1–G5 algebra runs **before** densify/flatten — ratchet vs densify path |

---

## Memory palace

1. **CAP** ∩ — Common Area of Partners  
2. **CUP** ∪ — Cover Under Partners  
3. **SUB** ∖ — Subtract the second  
4. **XOR** Δ — eXclusive OR (not shared)

**Self:** CAP/CUP keep me · SUB/XOR empty me · **Empty partner (G5)** is the fifth guard.

---

## Phase 0 implementation map (2026-08)

| Suite id | OverlayNGCurve today |
|----------|----------------------|
| G1–G4 | **Green** when `ReferenceEquals` or `EqualsExact` — short-circuit before flatten |
| G5 | Partially via base `GeometryOverlay` empty cases; Curve path inherits them |
| F1 | **Green** for G1–G4 self-ops (short-circuit before `Flatten`) |
| R1 | **Green** for G1/G2 self (return `Copy()` of curve) |
| R2 | **Open** — densify path still silent (no approx flag) |
| V1–V3 | **Open** — preconditions / dispatch policy not yet enforced |

---

## Cross-walk (legacy numbering)

Older scorecards used different G-ids. Prefer this mnemonic suite going forward.

| Legacy (guardrails.md §1) | This suite |
|---------------------------|------------|
| G1 difference empty | **G3** SUB self |
| G2 differenceBA empty | G5 / nested BA (not a sticky four-op) |
| G3 symDifference empty | **G4** XOR self |
| G4 intersection covers | **G1** CAP self |
| G5 union covers | **G2** CUP self |
