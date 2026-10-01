#!/usr/bin/env bash
# Development panel over ALL gated from-scratch actors (s0..s4; PROTOCOL_E3_SCRATCH per-seed gate, all five PASS),
# run AFTER each actor's protocol chain and registered ablation are complete (RUN_marl_e3_resume_v4.sh for the
# replicas in e3_scratch_rs_20260928; s3 in e3_scratch_seeds34_20260928).  Per actor, skipped when complete:
#   * the legal-vs-privileged evaluator diagnostic (selector v3 training + diagnostic v3: RUN_marl_e3_priv_diag_dv3.sh);
#   * selector diagnostic v3 (tie-half pair accuracy) on selectors_v2 (RUN_marl_e3_diag_v3.sh);
#   * the SUPPORT-GUARD rerun of the ablation closed loop (PROTOCOL_E3_CLOSED_LOOP_GUARD_20260928, ledger L-65):
#     cl_v3_direct_v6g next to the original cl_v3_direct.
# Then the statistical reporter (scripts/MARL_e3_panel_report.py: actor seeds as the replication unit, selector inits
# averaged within an actor, traffic-seed clusters, assertions) on BOTH the original and the guarded panels, and the
# paired guarded-vs-original comparison (MARL_e3_guard_compare.py).
# (28/09 23:4x, never run before this version: the old priv_diag runner now stops at its retired strict diagnostic,
#  and the old mean/range summary is replaced by the reporter; handoff 19:10 W1/W2.)
# Refuses an actor whose ablation closed loop is missing, or whose directory has a live writer (e3_writers_check.sh).
# Usage: bash scripts/RUN_marl_e3_scratch_panel.sh
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1; PY=external_envs/runtime/bin/python; M=research/marl_budget
ACTORS=($M/e3_scratch_rs_20260928/actor_s0 $M/e3_scratch_rs_20260928/actor_s1 $M/e3_scratch_rs_20260928/actor_s2 $M/e3_scratch_seeds34_20260928/actor_s3 $M/e3_scratch_rs_20260928/actor_s4)
for A in "${ACTORS[@]}"; do
  [ -f "$A/cl_v3_direct/manifest.json" ] || { echo "refusing: $A has no completed ablation closed loop (cl_v3_direct)"; exit 2; }
  bash scripts/e3_writers_check.sh "$A/labels_" "$A/selectors" "$A/cl_" > /dev/null || { echo "refusing: live writer in $A"; bash scripts/e3_writers_check.sh "$A/labels_" "$A/selectors" "$A/cl_"; exit 3; }
done
PIDS=""
for A in "${ACTORS[@]}"; do
  ( [ -f "$A/selectors_v3_diag_v3.json" ] || bash scripts/RUN_marl_e3_priv_diag_dv3.sh "$A" > "$A/priv_diag_dv3.log" 2>&1
    bash scripts/RUN_marl_e3_diag_v3.sh "$A" selectors_v2 > /dev/null ) & PIDS="$PIDS $!"
done
rc=0; for p in $PIDS; do wait $p || rc=$?; done; [ $rc = 0 ] || { echo "a diagnostic stage failed ($rc)"; exit $rc; }
bash scripts/RUN_marl_e3_guard_rerun.sh cl_v3_direct "${ACTORS[@]}"
ARGS=(); for A in "${ACTORS[@]}"; do ARGS+=(--actor "scratch:claim:$A"); done
for CL in cl_v3_direct cl_v3_direct_v6g; do
  "$PY" scripts/MARL_e3_panel_report.py "${ARGS[@]}" --cl $CL --diag selectors_v2_diag_v3.json --diag selectors_v3_diag_v3.json \
      --out "$M/e3_panel_reports/scratch5_${CL}.json" --out-txt "$M/e3_panel_reports/scratch5_${CL}.txt" > /dev/null || echo "reporter FAIL on $CL (see its txt)"
done
"$PY" scripts/MARL_e3_guard_compare.py --panel cl_v3_direct --actor "${ACTORS[@]}" --out "$M/e3_panel_reports/scratch5_guard_compare.json" | tee "$M/e3_panel_reports/scratch5_guard_compare.txt"
grep -E "^ACROSS|^STATUS" "$M/e3_panel_reports/scratch5_cl_v3_direct.txt" "$M/e3_panel_reports/scratch5_cl_v3_direct_v6g.txt"
echo "scratch panel done $(date)"
