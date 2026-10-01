#!/usr/bin/env bash
# Seed-1 fresh-only student (29/09 23:4x; ledger L-137), same recipe as distill_fo_prefix_s0 with teacher set_full_s1.
# (RUN_marl_e3_distill_v2.sh is running and is not edited.)  Watchdog; v1/v2 have no resume, so a stall restarts the run.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; tag=distill_fo_prefix_s1
[ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
echo "distill $tag $(date)"
"$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- \
  "$PY" -u scripts/MARL_e3_actor_distill_v2.py --teacher "$D/set_full_s1/ckpt_best.pt" --student-delivery prefix --student-adapter freshonly \
  --seed 1 --out "$D/$tag" --iters 500
echo "exit $? $tag $(date)"
