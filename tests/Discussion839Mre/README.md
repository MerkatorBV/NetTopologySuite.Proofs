# Discussion #839 MRE harness

Replays
[NetTopologySuite discussion #839](https://github.com/NetTopologySuite/NetTopologySuite/discussions/839)
(`ConformingDelaunayTriangulationBuilder` + concave polygon + centroid filter)
and checks **local Delaunay legality** of every internal edge with the
proofs-repo Rocq oracle kernel.

## What it measures

1. **CDTB output** under the reporter’s scale / tolerance settings.
2. **Centroid filter** via `IndexedPointInAreaLocator` (Interior / Boundary / Exterior).
3. **Straddle check**: whether any Interior-centroid triangle fails `polygon.Covers(t)`.
4. **Empty-circle test** on every internal edge:
   - Oracle mode `INCIRCLE_SIGN` → extracted `b64_inCircle`
   - Same arithmetic as Phase 5 FFI entry `nts_rocq_in_circle` (`oracle/nts_ffi.h`)
   - Pin: flip witness from `DelaunayLocallyDelaunay.loc_in_circle_test_D` (expect `POS 1.5`)

## Run

```powershell
# Requires WSL oracle_bin (default path below) or ORACLE_BIN
dotnet run --project tests/Discussion839Mre -c Release

# Variants
dotnet run --project tests/Discussion839Mre -c Release -- --no-scale
dotnet run --project tests/Discussion839Mre -c Release -- --tol0
dotnet run --project tests/Discussion839Mre -c Release -- --verbose
```

Oracle resolution order:

1. `ORACLE_BIN` — native Windows path to `oracle_bin` if present  
2. `WSL_ORACLE_BIN` — Linux path, invoked as `wsl.exe -e <path>`  
3. Built-in fallback: `/home/user/nettopologysuite.proofs/oracle/oracle_bin`

The fallback path is a **local template** (one developer’s WSL home layout), not
portable. Set `ORACLE_BIN` or `WSL_ORACLE_BIN` on any other machine.

## Relation to Phase 5 FFI

In-process `DllImport("ntsrocq")` / `RocqNative.InCircle` is preferred when
`libntsrocq` is on the loader path. This harness uses the **oracle protocol**
path so it runs on hosts where only `oracle_bin` is built (WSL). Both call the
same extracted `b64_inCircle` (parity-gated in CI by `oracle/gen_ffi_parity_tests.py`).

## Scout

Analysis + corpus answer: [`docs/nts-discussion-839-scout.md`](../../docs/nts-discussion-839-scout.md).
