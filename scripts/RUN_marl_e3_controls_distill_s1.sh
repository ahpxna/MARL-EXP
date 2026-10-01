#!/usr/bin/env bash
# Seed-1 replicates of the distillation controls C1 / C3 (30/09 02:4x; ledger L-149); same recipe as the seed-0 controls
# (scripts/RUN_marl_e3_controls_distill.sh, not edited).  Usage: distill_none_fromnone_s1 | distill_none_fromprefix_s1
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; tag="$1"
[ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
case "$tag" in
  distill_none_fromnone_s1)   A=(--teacher "$D/set_none_s1/ckpt_best.pt" --teacher-view own --student-delivery none);;
  distill_none_fromprefix_s1) A=(--teacher "$D/set_prefix_s1/ckpt_best.pt" --teacher-view own --student-delivery prefix --student-view none);;
  *) echo "unknown $tag"; exit 2;;
esac
"$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v3.py \
  "${A[@]}" --seed 1 --out "$D/$tag" --iters 500
echo "exit $? $tag $(date)"
