#!/usr/bin/env bash
# Capture C-3e verification evidence (run only on a clean git tree).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SCRATCH="${C3E_SCRATCH:-/tmp/grok-goal-8b5204f58ee6/implementer}"
cd "$ROOT"

if [[ -n "$(git status --porcelain)" ]]; then
  echo "ABORT: git working tree is not clean" >&2
  git status --short >&2
  exit 1
fi

rm -f "$SCRATCH"/*.log
mkdir -p "$SCRATCH"

{
  echo "=== STEP1_GIT_OK ==="
  git log --oneline -5
  echo ""
  echo "=== STEP2_DESIGN_NOTE_OK ==="
  grep -n "TODO: C-3e open design note" theories/C3eEfCorridorAssumption.v \
    theories/C-3e-ef-corridor-assumption.v
  grep -n "descending_sample_west_transport_clear" theories/BaseToTipHeadline.v
  echo ""
} | tee "$SCRATCH/verification-plan.log"

# C-3e chain modules are intentionally off _CoqProject.full (plan non-goal).
# Build via direct rocq c; upstream .vo from the registered corpus must exist.
COQFLAGS=(-q -Q "$ROOT/theories" NTS.Proofs)
C3E_CHAIN=(
  theories/C3eEfCorridorAssumption.v
  theories/HandoffConnector.v
  theories/BaseToTipHeadline.v
)

rm -f theories/C3eEfCorridorAssumption.vo \
      theories/HandoffConnector.vo \
      theories/BaseToTipHeadline.vo

{
  for vf in "${C3E_CHAIN[@]}"; do
    echo "=== ROCQ compile $vf ==="
    rocq c "${COQFLAGS[@]}" "$vf"
  done
} 2>&1 | tee "$SCRATCH/build-c3e-chain.log"

if grep -qE "^Error:" "$SCRATCH/build-c3e-chain.log"; then
  echo "BUILD_FAIL" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
echo "STEP3_BUILD_OK" | tee -a "$SCRATCH/verification-plan.log"

rm -f theories/C3eEfCorridorAssumption.vo
{
  echo "=== ROCQ compile theories/C3eEfCorridorAssumption.v (fresh) ==="
  rocq c "${COQFLAGS[@]}" theories/C3eEfCorridorAssumption.v
} 2>&1 | tee "$SCRATCH/corridor-absorbs.log"
echo "CORRIDOR_ABSORBS_OK" | tee -a "$SCRATCH/corridor-absorbs.log"

bash scripts/check_admitted.sh 2>&1 | tee "$SCRATCH/check-admitted.log"
echo "STEP4_CHECK_ADMITTED_OK" | tee -a "$SCRATCH/verification-plan.log"

cp "$SCRATCH/build-c3e-chain.log" "$SCRATCH/build-c3e.log"
echo "C3E_EVIDENCE_CAPTURE_OK" | tee -a "$SCRATCH/verification-plan.log"