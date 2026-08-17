# Phase 5 consumer bindings

In-process bindings for `libntsrocq` (`oracle/nts_ffi.h`). These replace the
RocqRefRunner subprocess for hot predicates. The subprocess stays the
differential reference.

| Language | File | Load |
|---|---|---|
| C# | [`csharp/RocqNative.cs`](csharp/RocqNative.cs) | `DllImport("ntsrocq")` |
| C++ | [`cpp/RocqNative.hpp`](cpp/RocqNative.hpp) | `dlopen` / `LoadLibrary`, path override `NTS_ROCQ_LIB` |
| Java | [`java/org/locationtech/jts/algorithm/rocq/RocqNative.java`](java/org/locationtech/jts/algorithm/rocq/RocqNative.java) | JNA `Native.load("ntsrocq")`, path override `NTS_ROCQ_LIB` |

Copy the file into the consumer. Do not add a link-time dependency on
`libntsrocq` to production defaults. Call `isAvailable()` / `IsAvailable()`
and skip when the native library is absent.

## Where they land

- **GEOS** — header copied to `include/geos/algorithm/RocqNative.h`. Opt-in;
  `libgeos` does not link `libntsrocq`.
- **JTS** — Java class copied into `jts-curve` on fork PR #7
  (`grootstebozewolf/jts`, `feature/sfa-curve-rgr`). That branch is the
  Java SoT. Do not wait on locationtech/jts or dr-jts; do not open a
  locationtech PR for this lane.
- **NTS** — C# class copied into `NetTopologySuite.Lab`. Core
  `RobustLineIntersector` stays on the stock path unless a caller opts in.

ABI contract and soundness ledger: [`docs/phase5-ffi-abi.md`](../docs/phase5-ffi-abi.md).

AI disclosure: authored with AI assistance (see CONTRIBUTING.md).
