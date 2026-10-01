#!/usr/bin/env bash
# Auditor's test 1 (29/09): fix the normalisation (selector v8 = v6 --loss mse with the safe normaliser; ledger L-65)
# and re-establish a clean closed-loop baseline.  Per actor: legal bid+head selector (v3 recipe: --bid --resp, lr 1e-3,
# 40 epochs), seeds 0-2, into <actor>/selectors_v8; then closed loop v6 --guard none with the ORIGINAL cl_v3_direct
# arguments (actor, panel 901-916 x headways 8/16, cap +84, iid capacities, MP2 reference) and --names legal_bid_resp,
# into <actor>/cl_v8_direct.  Skipped when complete.  Usage: bash scripts/RUN_marl_e3_test1_clean.sh <actor dir>...
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
one() {
  local A="$1" O="$1/selectors_v8" s PIDS=""
  mkdir -p "$O"
  for s in 0 1 2; do
    [ -f "$O/job_legal_bid_resp_s$s.json" ] || { "$PY" -u scripts/MARL_e3_selector_train_v8.py --train "$A/labels_train_*" --select "$A/labels_select" \
        --dev "$A/labels_dev" --out "$O" --name legal_bid_resp --bid --resp --loss mse --lrs 0.001 --seed $s --epochs 40 --threads 2 > "$A/v8_legal_bid_resp_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
  done
  for p in $PIDS; do wait $p || { echo "FAIL v8 training $A"; return 1; }; done
  [ -f "$A/cl_v8_direct/manifest.json" ] && { echo "done $A"; return 0; }
  [ -e "$A/cl_v8_direct" ] && mv "$A/cl_v8_direct" "legacy/$(echo "$A/cl_v8_direct" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  local ARGS; ARGS=$(python3 - "$A/cl_v3_direct/manifest.json" <<'PYEOF'
import json, sys, shlex
a = json.load(open(sys.argv[1]))['args']
out = ['--actor', a['actor'], '--policy', a['policy'], '--cap', str(a['cap']), '--capacity', a.get('capacity', 'iid'),
       '--headways', *[str(h) for h in a.get('headways', [8.0, 16.0])], '--traffic-seeds', *[str(s) for s in a['traffic_seeds']]]
if a.get('mp2'):
    out.append('--mp2')
print(' '.join(shlex.quote(x) for x in out))
PYEOF
)
  echo "launch $A/cl_v8_direct: $ARGS $(date)"
  eval "$PY scripts/run_with_watchdog.py --log '$A/cl_v8_direct.log' --out '$A/cl_v8_direct' --stall 600 --retries 2 -- $PY -u scripts/MARL_e3_closed_loop_v6.py $ARGS --selectors '$O' --names legal_bid_resp --guard none --out '$A/cl_v8_direct'"
  echo "closed loop $A rc=$? $(date)"
}
for A in "$@"; do one "$A" & done
wait; echo "test 1 clean baseline done $(date)"
