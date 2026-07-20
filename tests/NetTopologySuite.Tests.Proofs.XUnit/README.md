# NetTopologySuite.Tests.Proofs.XUnit

An [xUnit.net v3](https://xunit.net/) test project that validates the **real
NetTopologySuite implementation** (from NuGet) against the **proof-derived
vectors** of this repository's [`oracle/`](../../oracle/) directory. Every
vector consumed here is pinned to a Qed-closed Rocq theorem; the provenance
header of each vector file names it.

This is the executable end of the corpus: the proofs establish what is true,
the oracle emits concrete witnesses of those truths, and this project checks
where NTS's floating-point implementations agree with them — and *pins* the
places where they provably cannot.

## Suites

| Suite | Vector file | NTS API under test | Backing proof |
| ----- | ----------- | ------------------ | ------------- |
| `OrientationProofVectorTests` | `orientation_proof_vectors.txt` | `Orientation.Index` | `theories-flocq/Orient_b64_exact_full.v` (`b64_orient2d_exact_sound`) |
| `AdversarialOrientationTests` | `adversarial_tests.txt` (§A) | `Orientation.Index` | RocqRefRunner exact oracle (near-collinear product-collision family) |
| `De9ImLineLineVectorTests` | `de9im_line_line_vectors.txt` | `Geometry.Relate` | `theories/RelateLineLine.v` (`ll_matrix_paper_test*`) |

Two kinds of assertions appear:

- **Agreement** — NTS must reproduce the proven verdict (orientation sign,
  full DE-9IM matrix). This includes the adversarial near-collinear family
  where a naive double determinant is provably ZERO while the exact answer is
  POS: NTS's double-double pipeline gets these right, and the tests demonstrate
  it against machine-checked ground truth.
- **Divergence pins** — where the proofs show a floating-point technique
  *cannot* return the true sign (the ~2^-540 underflow band, where products
  flush to zero), the tests assert NTS's documented wrong ZERO. If NTS ever
  starts agreeing with the proofs there, the pin fails loudly and the vector
  gets promoted to the agreement group. (In the ~2^512 overflow band NTS's
  filter saturates to ±infinity, whose sign is still correct — those vectors
  run in the agreement group even though pure double-double expansion fails
  there.)

## Running

```sh
dotnet test tests/NetTopologySuite.Tests.Proofs.XUnit
```

Requires the .NET 10 SDK (the repository `global.json` opts `dotnet test` into
the Microsoft.Testing.Platform runner that xUnit v3 uses). The vector files
are read from the repository's `oracle/` directory at run time — no copying.

## Growth path

The oracle emits many more vector families than the three consumed so far.
Good next candidates, in rough order of directness:

- `passes_through_proof_vectors.txt` — hot-pixel passes-through semantics
  (needs a mapping onto `NetTopologySuite.Noding.Snapround.HotPixel`).
- The remaining `de9im_*_vectors.txt` families use *witness* matrices from the
  fill vocabulary (pattern-level, not geometry-derived), so they need the
  predicate-level comparison (`Intersects`/`Crosses`/…) rather than full
  matrix equality.
- The curve families (`arc_*`, `cp_*`, `ring_*`) become runnable against NTS
  once the curve MVP (NetTopologySuite/NetTopologySuite#854) ships types the
  vectors can build.
