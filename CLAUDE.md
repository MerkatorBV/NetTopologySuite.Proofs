# NetTopologySuite.Proofs — agent notes

Proofs repo: validates NetTopologySuite (NTS) and GEOS behaviour against a
Rocq-extracted oracle (`oracle_bin`). Docs of record live in `docs/`.

## WktUnicodeIllustrator (tools/WktUnicodeIllustrator)

Terminal sketches of WKT cases — A blue, B red, op result green, A∩B magenta,
self-overlap maroon/navy. Use it to *see* a geometry case before reasoning
about it, and to illustrate bug-hunt writeups.

```
dotnet run --project tools/WktUnicodeIllustrator -- [options] "WKT_A" "WKT_B"
  --op intersection|union|difference|symdifference|none
  --width N --height N        grid size (default 41×21)
  --cell-aspect R             terminal cell h/w (default 2.0)
  --no-color                  plain Unicode (use when output is captured)
  --demo curve|overshoot
```

Exit codes: `0` ok · `2` bad args/parse/empty · `3` overlay or overshoot
failure (the message is a finding, not noise — e.g. "side location conflict")
· `4` curve WKT in a lines-only build.

**Curve dependency:** SQL/MM curves (CIRCULARSTRING/…) need the sibling clone
`../NetTopologySuite` (branch `feat/curves-structure-wkt-foundation`), wired
via `-p:NtsProject=...` with an existence check. Without it the build falls
back to NuGet NTS (lines only) and curve WKT **exits 4 by design** — never
render a chord approximation of an arc.

Tests: `dotnet test tools/WktUnicodeIllustrator.Tests` (curve facts skip in
lines-only builds).

## Oracle harnesses

- `tests/CurveOracleBugHunt` — C# console, NTS-vs-oracle differential
  (`dotnet run --project tests/CurveOracleBugHunt`, oracle via `ORACLE` env
  var, default `.ci-artifacts/oracle-bin-linux/oracle_bin` under WSL).
- `tests/GeosOracleBugHunt` — Python, geosop-vs-oracle
  (`python3 tests/GeosOracleBugHunt/hunt.py`, env `GEOSOP` and `ORACLE`).
- Local GEOS lives in WSL at `/home/user/geos-src` (build:
  `/home/user/geos-build/bin/geosop`).
- `.ci-artifacts/` holds downloaded CI binaries — reproducible cache, never
  commit it (gitignored).

## Conventions

- Bug-hunt writeups: `docs/<topic>-<yyyy-mm>.md`, pin oracle/tool provenance
  (run id, commit) and record a `SUMMARY ok/warn/bug` line.
- There is no solution file; build/test per-project by path.
