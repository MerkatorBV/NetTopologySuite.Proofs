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
# Preserve git-c3e.log across runs; refresh other logs.
rm -f "$SCRATCH"/build-*.log "$SCRATCH"/check-admitted.log \
      "$SCRATCH"/c3e-lemma.log "$SCRATCH"/verification-plan.log \
      "$SCRATCH"/vp5-wiring.log

{
  echo "=== VP0: objective git sequence (verification plan step 2) ==="
  git fetch origin
  git status
  git log --oneline -8 origin/main
  cat plan.md | grep -A 30 "C-3e\|face_transport_premise"
  echo ""
} | tee -a "$SCRATCH/git-c3e.log"

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
  grep -n "corridor_safe_for_ef\|face_transport_west_straddle_headline_connected" \
    plan.md theories/CornerCorridorBridge.v
  grep -n "face_transport_straddle_pair_eq\|face_transport_premise" \
    theories/CornerCorridorBridge.v theories/HBridgeCoreSlice.v | head -25
  grep -n "Theorem corridor_safe_for_ef\|Lemma descending_sample_corridor_safe_for_ef\|Lemma face_transport_west_straddle" \
    theories/CornerCorridorBridge.v
  echo ""
  echo "=== VP2b: verbatim design note + doc stub ==="
  grep -n "C-3e open design note (post-PR#339)" theories/CornerCorridorBridge.v \
    theories/C-3e-ef-corridor-assumption.v
  grep -n "δ < threshold" theories/CornerCorridorBridge.v \
    theories/C-3e-ef-corridor-assumption.v
  echo "DOC_STUB_LINES=$(wc -l < theories/C-3e-ef-corridor-assumption.v)"
  echo ""
  echo "=== VP5: cross-file straddle wiring ==="
  grep -n "edge_x_at d my - ef\|edge_x_at d my + ef" theories/HBridgeCoreSlice.v
  grep -n "face_transport_west_straddle_headline_connected\|face_transport_straddle_pair_eq" \
    theories/CornerCorridorBridge.v
} | tee "$SCRATCH/verification-plan.log"

if ! grep -q "## C-3e-4 (along-dart headline) – IN PROGRESS" plan.md; then
  echo "VP2_FAIL: C-3e-4 section missing in plan.md" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "Theorem corridor_safe_for_ef" theories/CornerCorridorBridge.v; then
  echo "VP2_FAIL: corridor_safe_for_ef missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "Lemma face_transport_west_straddle_headline_connected" theories/CornerCorridorBridge.v; then
  echo "VP2_FAIL: face_transport bridge lemma missing" | tee -a "$SCRATCH/verification-plan.log"
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
Print descending_sample_corridor_safe_for_ef.
Check face_transport_west_straddle_headline_connected.
Goal JordanCurveSeam.connected_in_complement_cont sample_ring
  (corner_sample_left descending_sample_dart sample_rho sample_ef)
  (mkPoint (edge_x_at descending_sample_dart sample_my - sample_ef) sample_my).
  apply (proj1 (descending_sample_corridor_safe_for_ef)).
Qed.
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
if ! grep -q "face_transport_west_straddle_headline_connected" "$SCRATCH/c3e-lemma.log"; then
  echo "VP4_FAIL: face_transport bridge missing from exercise" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
echo "VP4_LEMMA_OK" | tee -a "$SCRATCH/verification-plan.log"
echo "C3E_EVIDENCE_CAPTURE_OK" | tee -a "$SCRATCH/verification-plan.log"