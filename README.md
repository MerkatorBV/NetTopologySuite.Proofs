# NetTopologySuite.Proofs

[![build proofs](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/actions/workflows/ci.yml/badge.svg)](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/actions/workflows/ci.yml)
[![dashboard](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/actions/workflows/pages.yml/badge.svg)](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/actions/workflows/pages.yml)

📊 **[Observatory dashboard](https://grootstebozewolf.github.io/NetTopologySuite.Proofs/)** — a generated status view of the corpus (cited theorems by regime, per-issue verdicts, oracle coverage, trust footprint). Reports only in-repo source of record and deep-links out to [JTS](https://github.com/locationtech/jts) / [NTS](https://github.com/NetTopologySuite/NetTopologySuite); not a JTS/NTS test runner. See [`dashboard/`](dashboard/).

Mechanically-checked proofs of load-bearing geometry facts used by
[NetTopologySuite](https://github.com/NetTopologySuite/NetTopologySuite),
written in [Rocq Prover](https://rocq-prover.org/). Every theorem ends
with `Qed.` on the three standard classical-reals axioms Rocq ships
with; there are no live `Admitted` theorems. This is a proof corpus,
not a verified implementation of NTS.

The only axioms used are the three standard ones bundled with Rocq's
classical real arithmetic library:

```
ClassicalDedekindReals.sig_not_dec
ClassicalDedekindReals.sig_forall_dec
FunctionalExtensionality.functional_extensionality_dep
```

The allowlisted trio is the only *corpus-introduced* axiom set; some
host-lane files and the Flocq lane inherit more. Long-form invariant,
roadmap, and build notes live in
[`docs/READING-GUIDE.md`](docs/READING-GUIDE.md#long-form-corpus-notes-off-the-readme-first-screen).

> **Licence.** [BSD-3-Clause](LICENSE), matching NetTopologySuite. No DOI.

## 60 seconds

```sh
make help
```

Works with no Rocq installed. Then [`docs/HELP.md`](docs/HELP.md).

## Contents

### `theories/` — Stdlib-only modules

Host CI target (`make host`). Foundational geometry on pairs of reals.

### `theories-flocq/` — Flocq binary64 modules

Plus the Stdlib-only Phase 3/4 modules built alongside them. Container only.

### `oracle/` — extracted reference driver

Consumed by [NetTopologySuite.Curve](https://github.com/grootstebozewolf/NetTopologySuite.Curve). Not a verified NTS runtime.

### `docs/` — actor cards, audits, registries

Start at [`docs/HELP.md`](docs/HELP.md).

### `dashboard/` — Observatory source

Generated status view; in-repo source of record only.

Where this corpus talks about curves it names SQL/MM ISO/IEC 13249-3
`CIRCULARSTRING` / `COMPOUNDCURVE` / `CURVEPOLYGON`. Linearisation is
the named `chord_approx` (`Linearise`); NTS `Flatten()` to chords is
lossy and is not the curve.

## Reproduction

```sh
make help
make host
```

`make host` builds the 47 foundational Stdlib-only modules. The full
corpus (515 registered modules) is the pinned container. Toolchain:
**Rocq 9.2.0 + Flocq 4.2.2**.

## What this is not

- **Not** a verified implementation of NTS. The C# is not extracted from Rocq. Proofs are over an abstract model; they apply only when the implementation encodes the same mathematics.
- **Not** a substitute for unit tests. Tests still cover rounding, exceptions, performance, and the rest of the runtime.
- **Not** complete. Coverage is the foundational layer plus early-to-mid chokepoint phases; gaps are named in the Reading Guide, not silent.

**Shewchuk-13.** Corpus postcondition (half-ulp `strict_succ_b64`), not a disproof of Shewchuk 1997 — [Proofs #482](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/482).

## Doors

- [`docs/HELP.md`](docs/HELP.md) — pick your path
- [`docs/READING-GUIDE.md`](docs/READING-GUIDE.md) — full map + long-form status
- [`GETTING-STARTED.md`](GETTING-STARTED.md) — 60-second on-ramp
- [`CONTRIBUTING.md`](CONTRIBUTING.md) — how to add theorems

Joost is BDFL on corpus honesty and pruning, not product owner. Jeroen is PO.
