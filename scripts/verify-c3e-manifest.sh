#!/usr/bin/env bash
# Verification plan steps for C-3e on the manifest spine
# (CornerCorridorBridge + C3eEfCorridorAssumption + HandoffConnector + BaseToTipHeadline).
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
rm -f "$SCRATCH"/build-*.log "$SCRATCH"/check-admitted.log \
      "$SCRATCH"/c3e-lemma.log "$SCRATCH"/verification-plan.log \
      "$SCRATCH"/vp5-wiring.log "$SCRATCH"/git-c3e.log \
      "$SCRATCH"/git-c3e-run1.log "$SCRATCH"/git-c3e-run2.log \
      "$SCRATCH"/plan-c3e-grep.log "$SCRATCH"/objective-full.log \
      "$SCRATCH"/objective-full-run1.log "$SCRATCH"/objective-full-run2.log

# VP0: clean git literal sequence (fetch; status; log) x2 — no plan grep.
capture_git_sequence() {
  git fetch origin
  git status
  git log --oneline -8 origin/main
  echo ""
}

# VP2: plan narrative captured separately (grep pollutes git-c3e.log).
capture_plan_c3e_grep() {
  cat plan.md | grep -A 30 "C-3e\|face_transport_premise"
  echo ""
}

capture_git_sequence | tee "$SCRATCH/git-c3e-run1.log" >/dev/null
capture_git_sequence | tee "$SCRATCH/git-c3e-run2.log" >/dev/null
capture_plan_c3e_grep | tee "$SCRATCH/plan-c3e-grep.log" >/dev/null

if ! cmp -s "$SCRATCH/git-c3e-run1.log" "$SCRATCH/git-c3e-run2.log"; then
  echo "VP0_FAIL: git-c3e-run1.log and git-c3e-run2.log differ" >&2
  exit 1
fi

# Named artifacts: clean git-only log + full objective sequence (git + grep) x2.
cat "$SCRATCH/git-c3e-run1.log" "$SCRATCH/git-c3e-run2.log" >"$SCRATCH/git-c3e.log"

# VP0b: git-c3e.log must be git-only (plan grep lives in plan-c3e-grep.log).
if grep -qE "face_transport_premise|Discharge campaign|## C-3e-4" "$SCRATCH/git-c3e.log"; then
  echo "VP0_FAIL: git-c3e.log polluted with plan.md narrative" >&2
  exit 1
fi
{
  capture_git_sequence
  capture_plan_c3e_grep
} >"$SCRATCH/objective-full-run1.log"
{
  capture_git_sequence
  capture_plan_c3e_grep
} >"$SCRATCH/objective-full-run2.log"
if ! cmp -s "$SCRATCH/objective-full-run1.log" "$SCRATCH/objective-full-run2.log"; then
  echo "VP0_FAIL: objective-full-run1.log and objective-full-run2.log differ" >&2
  exit 1
fi
cat "$SCRATCH/objective-full-run1.log" "$SCRATCH/objective-full-run2.log" \
  >"$SCRATCH/objective-full.log"

{
  echo "VP0_GIT_CAPTURE_OK"
  echo "GIT_C3E_LOG_LINES=$(wc -l < "$SCRATCH/git-c3e.log")"
  echo "GIT_C3E_POLLUTION_CHECK=clean"
  echo "OBJECTIVE_FULL_LOG_LINES=$(wc -l < "$SCRATCH/objective-full.log")"
  echo "=== VP1: git status + log ==="
  git status --short
  echo "BRANCH=$(git branch --show-current)"
  echo "HEAD=$(git rev-parse --short HEAD)"
  git log --oneline -8
  echo ""
  echo "=== VP2: plan C-3e grep (separate artifact) ==="
  head -5 "$SCRATCH/plan-c3e-grep.log"
  echo "PLAN_C3E_GREP_LINES=$(wc -l < "$SCRATCH/plan-c3e-grep.log")"
  echo "=== VP2b: C-3e-4 plan + corridor_safe_for_ef + face_transport wiring ==="
  grep -n "## C-3e-4 (along-dart headline) – IN PROGRESS" plan.md
  grep -n "connect to exact (edge_x_at … ±ef, my) targets" plan.md
  grep -n "corridor_safe_for_ef\|face_transport_premise_ring_dart_west_straddle_connected" \
    plan.md theories/BaseToTipHeadline.v
  grep -n -m 25 "face_transport_straddle_pair_eq\|face_transport_premise" \
    theories/BaseToTipHeadline.v theories/HBridgeCoreSlice.v
  grep -n "Theorem corridor_safe_for_ef\|Lemma descending_sample_corridor_safe_for_ef\|Lemma face_transport_premise_ring_dart" \
    theories/BaseToTipHeadline.v
  echo ""
  echo "=== VP2b: verbatim design note + ef-threshold module ==="
  grep -n "C-3e open design note (post-PR#339)" theories/C3eEfCorridorAssumption.v
  grep -n "δ < threshold" theories/C3eEfCorridorAssumption.v
  echo "C3E_EF_LINES=$(wc -l < theories/C3eEfCorridorAssumption.v)"
} | tee "$SCRATCH/verification-plan.log"

if ! grep -q "## C-3e-4 (along-dart headline) – IN PROGRESS" plan.md; then
  echo "VP2_FAIL: C-3e-4 section missing in plan.md" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "Theorem corridor_safe_for_ef" theories/BaseToTipHeadline.v; then
  echo "VP2_FAIL: corridor_safe_for_ef missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "Lemma face_transport_premise_ring_dart_west_straddle_connected" theories/BaseToTipHeadline.v; then
  echo "VP2_FAIL: ring-dart west discharge lemma missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "Lemma face_transport_premise_ring_dart_east_straddle_connected" theories/BaseToTipHeadline.v; then
  echo "VP2_FAIL: ring-dart east discharge lemma missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "Lemma face_transport_premise_ring_dart_straddle_pair_connected" theories/BaseToTipHeadline.v; then
  echo "VP2_FAIL: ring-dart straddle pair discharge lemma missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "Lemma descending_sample_corridor_safe_for_ef" theories/BaseToTipHeadline.v; then
  echo "VP2_FAIL: concrete sample application missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
echo "VP2_C3E4_OK" | tee -a "$SCRATCH/verification-plan.log"

{
  echo "=== VP3: standard project build ==="
  echo "COMMAND: make -f Makefile.full.gen theories/BaseToTipHeadline.vo"
  rm -f theories/CornerCorridorBridge.vo theories/CornerCorridorBridge.glob \
        theories/C3eEfCorridorAssumption.vo theories/C3eEfCorridorAssumption.glob \
        theories/HandoffConnector.vo theories/HandoffConnector.glob \
        theories/BaseToTipHeadline.vo theories/BaseToTipHeadline.glob
  make -f Makefile.full.gen theories/BaseToTipHeadline.vo
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
From NTS.Proofs Require Import HBridgeCoreSlice BaseToTipHeadline.
Check face_transport_straddle_pair_eq.
Check corridor_safe_for_ef.
Print descending_sample_corridor_safe_for_ef.
Check face_transport_premise_ring_dart_straddle_pair_connected.
Check face_transport_straddle_target_in_complement.
Check face_transport_premise_ring_dart_west_straddle_in_complement.
Check face_transport_premise_foreign_straddle_pair_in_complement.
Check straddle_transport_clash_from_connected.
Check c3e_ring_west_straddle_complement_via_connected.
Print Assumptions face_transport_premise_ring_dart_straddle_pair_in_complement.
COQ

{
  echo "=== VP4: lemma exercise (instantiated apply) ==="
  rocq top -batch -quiet \
    -Q theories NTS.Proofs -Q theories-flocq NTS.Proofs.Flocq \
    -load-vernac-source "$SCRATCH/exercise_c3e.v"
} 2>&1 | tee "$SCRATCH/c3e-lemma.log"

if ! grep -qE "edge_x_at d my - ef|edge_x_at descending_sample_dart sample_my" \
     "$SCRATCH/c3e-lemma.log"; then
  echo "VP4_FAIL: edge_x_at ±ef target missing from Check/Print output" \
    | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "face_transport_premise_ring_dart_straddle_pair_connected" "$SCRATCH/c3e-lemma.log"; then
  echo "VP4_FAIL: ring-dart straddle pair discharge missing from exercise" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "face_transport_premise_ring_dart_west_straddle_in_complement" "$SCRATCH/c3e-lemma.log"; then
  echo "VP4_FAIL: west in_complement apply hook missing from exercise" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "straddle_transport_clash_from_connected" "$SCRATCH/c3e-lemma.log"; then
  echo "VP4_FAIL: HBridge straddle_transport_clash_from_connected missing from exercise" \
    | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "c3e_ring_west_straddle_complement_via_connected" "$SCRATCH/c3e-lemma.log"; then
  echo "VP4_FAIL: C-3e→HBridge west complement discharge missing from exercise" \
    | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -qE "In d \(.*ring_edges r\)" "$SCRATCH/c3e-lemma.log"; then
  echo "VP4_FAIL: In d (ring_edges r) missing from Check/Print output" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
echo "VP4_LEMMA_OK" | tee -a "$SCRATCH/verification-plan.log"

{
  echo "=== VP5: downstream apply chain (BaseToTipHeadline + siblings) ==="
  grep -n "apply.*corridor_safe_for_ef\|destruct (corridor_safe_for_ef" theories/BaseToTipHeadline.v
  grep -n "face_transport_premise_ring_dart_west_straddle_connected\|face_transport_premise_ring_dart_east_straddle_connected\|face_transport_premise_ring_dart_straddle_pair_connected\|face_transport_premise_ring_dart_.*_in_complement\|face_transport_premise" \
    theories/BaseToTipHeadline.v
  grep -n "apply.*face_transport_premise_ring_dart\|apply face_transport_straddle_target_in_complement\|destruct (corridor_safe_for_ef" \
    theories/BaseToTipHeadline.v
  grep -n "face_transport_straddle_target_in_complement\|face_transport_straddle_complements_of_connected\|straddle_transport_clash_from_connected\|straddle_transport_clash_from_complements" \
    theories/HBridgeCoreSlice.v
  grep -n "c3e_ring_west_straddle_complement_via_connected\|c3e_ring_east_straddle_complement_via_connected" \
    theories/BaseToTipHeadline.v
  grep -n "In d (ring_edges r)" theories/BaseToTipHeadline.v
} | tee "$SCRATCH/vp5-wiring.log"

if ! grep -qE "apply.*corridor_safe_for_ef|destruct \(corridor_safe_for_ef" "$SCRATCH/vp5-wiring.log"; then
  echo "VP5_FAIL: no corridor_safe_for_ef apply/destruct in BaseToTipHeadline" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "face_transport_premise_ring_dart_straddle_pair_connected" "$SCRATCH/vp5-wiring.log"; then
  echo "VP5_FAIL: ring-dart straddle pair discharge missing from VP5 grep" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "face_transport_premise_ring_dart_west_straddle_in_complement" "$SCRATCH/vp5-wiring.log"; then
  echo "VP5_FAIL: premise-layer in_complement apply hooks missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "face_transport_straddle_target_in_complement" "$SCRATCH/vp5-wiring.log"; then
  echo "VP5_FAIL: HBridge premise-site apply hook missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "straddle_transport_clash_from_connected" "$SCRATCH/vp5-wiring.log"; then
  echo "VP5_FAIL: HBridge straddle_transport_clash_from_connected apply hook missing" \
    | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
if ! grep -q "c3e_ring_west_straddle_complement_via_connected" "$SCRATCH/vp5-wiring.log"; then
  echo "VP5_FAIL: C-3e→HBridge west complement discharge missing" | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
echo "VP5_WIRING_OK" | tee -a "$SCRATCH/vp5-wiring.log"

{
  echo "=== VP5b: straddle_eq_corridor + corridor_safe_for_ef headline ==="
  grep -n "face_transport_straddle_pair_eq\|straddle_west_eq_corridor\|straddle_east_eq_corridor" \
    theories/BaseToTipHeadline.v theories/C3eEfCorridorAssumption.v | head -12
  grep -n "destruct (face_transport_straddle_pair_eq\|destruct (corridor_safe_for_ef" \
    theories/BaseToTipHeadline.v
} | tee -a "$SCRATCH/vp5-wiring.log"

if ! grep -q "face_transport_straddle_pair_eq" "$SCRATCH/vp5-wiring.log"; then
  echo "VP5_FAIL: face_transport_straddle_pair_eq missing from headline wiring" \
    | tee -a "$SCRATCH/verification-plan.log"
  exit 1
fi
echo "C3E_EVIDENCE_CAPTURE_OK" | tee -a "$SCRATCH/verification-plan.log"