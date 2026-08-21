# GEOS ↔ Rocq oracle differential hunt

Gates GEOS curve / predicate behaviour against NetTopologySuite.Proofs `oracle_bin`.

## Requirements

- `geosop` (GEOS build, e.g. WSL `/home/user/geos-build/bin/geosop`)
- `oracle_bin` Linux CI artifact under `.ci-artifacts/oracle-bin-linux/`

## Run

```bash
export GEOSOP=/path/to/geosop
export ORACLE=/path/to/oracle_bin
python3 hunt.py
```

## Surfaces

| Tag | Oracle / pin |
|---|---|
| LEN/* | `ARC_LENGTH` |
| DIST/* | `ARC_DISTANCE` |
| ENV/* | arc extrema |
| AREA/* | `ARC_AREA` / π |
| PIP/* | `POINT_IN_CURVE_RING` |
| COVERS968/* | GEOS #968 |
| SPLIT1497/* | GEOS #1497 / #1500 |
| MS/* | MultiSurface A/P (#1502) |

See `docs/geos-oracle-rung-2026-08.md`.
