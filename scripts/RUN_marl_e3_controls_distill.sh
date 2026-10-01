#!/usr/bin/env bash
# Controls for "is the 0-byte distilled student's gain about COMMUNICATION?" (30/09 00:4x; ledger L-147).  Usage: <tag>
#  distill_none_fromnone_s0   C1: the same DAgger recipe, teacher = set_none_s0 (a NO-communication teacher acting on its own
#                             no-message view), 0-byte student.  Same gain => the gain is distillation, not information.
#  distill_none_fromprefix_s0 C3: teacher = set_prefix_s0 acting on its own prefix deliveries (partial information); the env
#                             delivers the prefix for the teacher, the student's input has every message removed (0 B).
#                             With C1 and distill_none_s0 (full teacher): a dose-response in teacher information.
#  set_none_s0_cont2500       C2: set_none_s0 continued 500 PPO iterations (declared deviation: Adam/RNG restart), about
#                             the student's extra 500 x 8 episodes: compute-matched no-communication training.
# distill v3 identity passed (defaults reproduce v1: it 1-2 loss 1.973 / 1.665, agree 0.300 / 0.465).  Watchdog on every run.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; tag="$1"
[ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
echo "run $tag $(date)"
case "$tag" in
  distill_none_fromnone_s0)
    "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v3.py \
      --teacher "$D/set_none_s0/ckpt_best.pt" --teacher-view own --student-delivery none --seed 0 --out "$D/$tag" --iters 500;;
  distill_none_fromprefix_s0)
    "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v3.py \
      --teacher "$D/set_prefix_s0/ckpt_best.pt" --teacher-view own --student-delivery prefix --student-view none --seed 0 --out "$D/$tag" --iters 500;;
  set_none_s0_cont2500)
    "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_train_delivery_v9.py \
      --out "$D/$tag" --seed 0 --iters 2500 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 --eval-every 20 \
      --threads 2 --audit-every 5 --delivery none --set-actor --init-from "$D/set_none_s0/ckpt_last.pt";;
  *) echo "unknown $tag"; exit 2;;
esac
echo "exit $? $tag $(date)"
