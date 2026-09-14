# oracle/fixtures/sqlmm

claimId: none (docs / packaging)

Optional locked rows for `tools/SqlMmExampleFactory` smoke. North-star
path contract (copied; does not require PR #741 to land):

```
tools/WktIntakeWalker/          # ANTLR pin + C# visitor (house style)
tools/SqlMmExampleFactory/      # bag → WKT + WKB
oracle/fixtures/sqlmm/          # optional locked rows
  shelf-a/*.wkt + *.wkb-*.hex
  shelf-c/HOLD-codes.md         # 13–17 / 18–21 named HOLD
```

Hex is lowercase. Engines still test the bag. No new ADR-0006 keyword.
These files are **not** oracle line-protocol input.
