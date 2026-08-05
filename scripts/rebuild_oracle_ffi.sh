#!/usr/bin/env bash
# Rebuild oracle/extracted.ml + oracle_bin + libntsrocq (Phase 5 FFI).
#
# Requires: Rocq 9.x, Flocq, ocamlfind/ocamlopt, a compiled theories-flocq/
# dependency closure for Validate_binary64_extract.v (and its Requires).
#
# Usage (repo root):
#   ./scripts/rebuild_oracle_ffi.sh
#   ./scripts/rebuild_oracle_ffi.sh --parity   # also run ffi-parity gate
#
# extracted.ml is gitignored; this script is the supported refresh path after
# the b64_orient2d_exact gap (see docs/ffi-rungs-2026-08.md).

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

PARITY=0
for arg in "$@"; do
  case "$arg" in
    --parity) PARITY=1 ;;
    -h|--help)
      sed -n '2,14p' "$0"
      exit 0
      ;;
  esac
done

if ! command -v coqc >/dev/null 2>&1; then
  echo "error: coqc not on PATH" >&2
  exit 2
fi

echo "==> Extraction: theories-flocq/Validate_binary64_extract.v"
coqc -Q theories NTS.Proofs -Q theories-flocq NTS.Proofs.Flocq \
  theories-flocq/Validate_binary64_extract.v

if ! grep -q 'b64_orient2d_exact' oracle/extracted.ml; then
  echo "error: extracted.ml missing b64_orient2d_exact after extract" >&2
  exit 1
fi
echo "    OK: b64_orient2d_exact present in oracle/extracted.ml"

echo "==> make -C oracle (oracle_bin)"
make -C oracle

echo "==> make -C oracle ffi (libntsrocq + ffi_probe)"
make -C oracle ffi

echo "==> smoke: ORIENT_EXACT via ffi_probe"
printf '0 0\n1 0\n0 1\n' | oracle/ffi_probe ORIENT_EXACT
echo

if [[ "$PARITY" -eq 1 ]]; then
  echo "==> make -C oracle ffi-parity"
  make -C oracle ffi-parity
fi

echo "Done. See docs/ffi-rungs-2026-08.md"
