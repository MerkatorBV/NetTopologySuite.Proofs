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

CHORE_MSG="chore(C-3e): document ef-vs-corridor open question + proposed lemma sketch"
CHORE_HASH="$(git log --oneline --grep="$CHORE_MSG" -1 --format=%H 2>/dev/null || true)"
CHORE_PARENT="$(git log -1 --format=%P "$CHORE_HASH" 2>/dev/null || true)"
MAIN_TIP="$(git rev-parse origin/main 2>/dev/null || true)"
FIRST_POST_FETCH="unknown"
if [[ -n "$CHORE_HASH" && -n "$MAIN_TIP" ]]; then
  if [[ "$CHORE_PARENT" == *"$MAIN_TIP"* ]]; then
    FIRST_POST_FETCH="yes"
  else
    FIRST_POST_FETCH="no"
  fi
fi

{
  echo "=== VP1: git status + log ==="
  git status --short
  echo "BRANCH=$(git branch --show-current)"
  echo "HEAD=$(git rev-parse --short HEAD)"
  git log --oneline -8
  echo "CHORE_COMMIT=${CHORE_HASH:-missing}"
  echo "CHORE_FIRST_POST_FETCH=${FIRST_POST_FETCH}"
  git log --oneline -15 | grep -F "$CHORE_MSG" || echo "CHORE_MSG_MISSING"
  echo ""
  echo "=== VP2: verbatim design note + doc stub + headline ==="
  grep -n "C-3e open design note (post-PR#339)" theories/CornerCorridorBridge.v \
    theories/C-3e-ef-corridor-assumption.v
  grep -n "δ < threshold" theories/CornerCorridorBridge.v \
    theories/C-3e-ef-corridor-assumption.v
  grep -n "∃ ε₀ > 0" theories/CornerCorridorBridge.v \
    theories/C-3e-ef-corridor-assumption.v
  echo "DOC_STUB_LINES=$(wc -l < theories/C-3e-ef-corridor-assumption.v)"
  grep -n "Lemma corridor_absorbs_ef\|Lemma descending_sample_west_transport_clear" \
    theories/CornerCorridorBridge.v
  echo ""
} | tee "$SCRATCH/verification-plan.log"

if ! grep -q "δ < threshold" theories/C-3e-ef-corridor-assumption.v; then
  echo "VP2_FAIL: verbatim δ marker missing in doc stub" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi

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