#!/usr/bin/env bash
# Verification plan steps for C-3e on the manifest spine (CornerCorridorBridge.v).
# Run on a clean git tree; writes evidence to ${C3E_SCRATCH:-/tmp/c3e-verify}.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SCRATCH="${C3E_SCRATCH:-/tmp/c3e-verify}"
cd "$ROOT"

if [[ -n "$(git status --porcelain)" ]]; then
  echo "ABORT: git working tree is not clean" >&2
  exit 1
fi

mkdir -p "$SCRATCH"
rm -f "$SCRATCH"/*.log

{
  echo "=== VP1: git status + log ==="
  git status --short
  echo "BRANCH=$(git branch --show-current)"
  echo "HEAD=$(git rev-parse --short HEAD)"
  git log --oneline -8
  git log --oneline -15 | grep -F "chore(C-3e): document ef-vs-corridor" || true
  echo ""
  echo "=== VP2: design note + headline grep ==="
  grep -n "TODO: C-3e open design note" theories/CornerCorridorBridge.v \
    theories/C-3e-ef-corridor-assumption.v
  grep -n "Lemma corridor_absorbs_ef\|Lemma descending_sample_west_transport_clear" \
    theories/CornerCorridorBridge.v
  echo ""
} | tee "$SCRATCH/verification-plan.log"

{
  echo "=== VP3: standard project build ==="
  echo "COMMAND: make -f Makefile.full.gen theories/CornerCorridorBridge.vo"
  echo "MANIFEST: theories/CornerCorridorBridge.v (listed in _CoqProject.full)"
  echo ""
  rm -f theories/CornerCorridorBridge.vo theories/CornerCorridorBridge.glob
  make -f Makefile.full.gen theories/CornerCorridorBridge.vo
  echo "BUILD_EXIT=0"
} 2>&1 | tee "$SCRATCH/build-corner-corridor-bridge.log"

if grep -qE "^Error:" "$SCRATCH/build-corner-corridor-bridge.log"; then
  echo "STEP3_BUILD_FAIL" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
echo "STEP3_BUILD_OK" | tee -a "$SCRATCH/verification-plan.log"

bash scripts/check_admitted.sh 2>&1 | tee "$SCRATCH/check-admitted.log"
echo "STEP4_CHECK_ADMITTED_OK" | tee -a "$SCRATCH/verification-plan.log"
echo "C3E_EVIDENCE_CAPTURE_OK" | tee -a "$SCRATCH/verification-plan.log"