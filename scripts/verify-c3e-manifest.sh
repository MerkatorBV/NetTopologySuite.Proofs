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
  echo ""
  echo "=== VP2: C-3e-4 plan + corridor_safe_for_ef + face_transport wiring ==="
  grep -n "## C-3e-4 (along-dart headline) – IN PROGRESS" plan.md
  grep -n "connect to exact (edge_x_at … ±ef, my) targets" plan.md
  grep -n "corridor_safe_for_ef" plan.md theories/CornerCorridorBridge.v
  grep -n "face_transport_straddle_pair_eq\|face_transport_premise" \
    theories/CornerCorridorBridge.v theories/HBridgeCoreSlice.v | head -20
  grep -n "Theorem corridor_safe_for_ef\|Lemma descending_sample_corridor_safe_for_ef" \
    theories/CornerCorridorBridge.v
  echo ""
  echo "=== VP2b: verbatim design note + doc stub ==="
  grep -n "C-3e open design note (post-PR#339)" theories/CornerCorridorBridge.v \
    theories/C-3e-ef-corridor-assumption.v
  grep -n "δ < threshold" theories/CornerCorridorBridge.v \
    theories/C-3e-ef-corridor-assumption.v
  echo "DOC_STUB_LINES=$(wc -l < theories/C-3e-ef-corridor-assumption.v)"
  echo ""
} | tee "$SCRATCH/verification-plan.log"

if ! grep -q "## C-3e-4 (along-dart headline) – IN PROGRESS" plan.md; then
  echo "VP2_FAIL: C-3e-4 section missing in plan.md" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "Theorem corridor_safe_for_ef" theories/CornerCorridorBridge.v; then
  echo "VP2_FAIL: corridor_safe_for_ef missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "Lemma descending_sample_corridor_safe_for_ef" theories/CornerCorridorBridge.v; then
  echo "VP2_FAIL: concrete sample application missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
echo "VP2_C3E4_OK" | tee -a "$SCRATCH/verification-plan.log"

{
  echo "=== VP3: standard project build ==="
  echo "COMMAND: make -f Makefile.full.gen theories/CornerCorridorBridge.vo"
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

cat > "$SCRATCH/exercise_c3e.v" <<'COQ'
From NTS.Proofs Require Import CornerCorridorBridge.
Check corridor_safe_for_ef.
Print corridor_safe_for_ef.
Check descending_sample_corridor_safe_for_ef.
Print descending_sample_corridor_safe_for_ef.
Print face_transport_straddle_pair_eq.
Eval compute in sample_ef.
Eval compute in sample_my.
COQ

{
  echo "=== VP4: lemma exercise (instantiated apply) ==="
  rocq top -batch -quiet \
    -Q theories NTS.Proofs -Q theories-flocq NTS.Proofs.Flocq \
    -load-vernac-source "$SCRATCH/exercise_c3e.v"
} 2>&1 | tee "$SCRATCH/c3e-lemma.log"

if ! grep -q "edge_x_at descending_sample_dart sample_my" "$SCRATCH/c3e-lemma.log"; then
  echo "VP4_FAIL: edge_x_at sample_my missing from Print output" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "Rminus.*sample_ef\|sample_ef.*Rplus" "$SCRATCH/c3e-lemma.log"; then
  echo "VP4_FAIL: ±sample_ef targets missing from Print output" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "corner_sample_left descending_sample_dart sample_rho sample_ef" "$SCRATCH/c3e-lemma.log"; then
  echo "VP4_FAIL: corner_sample_left instantiation missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
echo "VP4_LEMMA_OK" | tee -a "$SCRATCH/verification-plan.log"
echo "C3E_EVIDENCE_CAPTURE_OK" | tee -a "$SCRATCH/verification-plan.log"