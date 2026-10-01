#!/usr/bin/env bash
# Resume RUN_marl_e3_schednet.sh after hung CityFlow processes (28/09/2026): keeps every finished (train, eval) pair,
# parks partial outputs in legacy/, reruns the rest under scripts/run_with_watchdog.py.
# Usage: bash scripts/RUN_marl_e3_schednet_resume.sh <run dir> <actor ckpt>...   (same actor order as the original run)
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
RUN="${1:?run dir}"; shift
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY=external_envs/runtime/bin/python; WD="$PY scripts/run_with_watchdog.py"; TS=$(date +%Y%m%d_%H%M%S)
if [ "${SKIP_HANG_GUARD:-0}" != 1 ] && pgrep -f "python.*scripts/MARL_e3_" > /dev/null; then echo "refusing: MARL_e3 processes are still running"; exit 2; fi
park() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$TS"; return 0; }
n=0
for A in "$@"; do
  mkdir -p "$RUN/actor$n"; echo "$A" > "$RUN/actor$n/ACTOR"
  for s in 0 1 2; do
    D="$RUN/actor$n/sched_s$s"
    [ -f "${D}_eval/manifest.json" ] && continue
    if [ ! -f "$D/manifest.json" ]; then park "$D"; $WD --log "$D.log" --out "$D" --stall 900 -- "$PY" -u scripts/MARL_e3_schednet_train_v2.py --actor "$A" --out "$D" --seed $s --iters 300; fi
    park "${D}_eval"; $WD --log "${D}_eval.log" --out "${D}_eval" --stall 900 -- "$PY" -u scripts/MARL_e3_schednet_train_v2.py --mode eval --actor "$A" --ckpt "$D/ckpt_best.pt" --out "${D}_eval"
    python3 scripts/MARL_hetero_closed_loop_report.py "${D}_eval" --control prefix > "${D}_eval/full_endpoints.txt"
    grep -A1 "== schednet" "${D}_eval/full_endpoints.txt" | tee -a "$RUN/chain.log"
  done
  n=$((n + 1))
done
echo "RESUME COMPLETE $(date)" | tee -a "$RUN/chain.log"
