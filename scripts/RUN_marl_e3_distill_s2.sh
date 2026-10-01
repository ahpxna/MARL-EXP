#!/usr/bin/env bash
# Seed-2 0-byte student (30/09 02:4x; ledger L-149): distill v3 with defaults (= the v1 recipe of distill_none_s0/s1),
# teacher set_full_s2.  Watchdog (no resume in the distiller: a stall restarts the run).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; tag=distill_none_s2
[ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
"$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v3.py \
  --teacher "$D/set_full_s2/ckpt_best.pt" --student-delivery none --seed 2 --out "$D/$tag" --iters 500
echo "exit $? $tag $(date)"
