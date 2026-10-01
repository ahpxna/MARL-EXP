#!/usr/bin/env bash
# RELAY-COMPRESSED METHOD inside PROTOCOL_HETERO_v0 (30/09 11:2x; ledger L-162).  The packet channel is unchanged; each 25 B packet
# carries 3 B summaries (TRAIN codebook, L = 4) of its sender and of every agent the sender knew (multi-hop relays, true ages).
# Identity checks passed 11:2x: trainer v10 --relay none == v9 (it 4: 2569 / 3831); distill v4 defaults == v3 (1.973 / 1.665).
# Usage: <tag>.  Watchdog on every run.
#  relay_st_sN  DAgger student (teacher set_full_sN, full information) whose inputs are the relay-merged prefix deliveries
#  relay_ppo_sN set actor trained from scratch (MAPPO) on the relay-merged prefix deliveries
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; tag="$1"; N="${tag##*_s}"
[ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; exit 0; }
echo "run $tag $(date)"
case "$tag" in
  relay_st_s*)  "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v4.py \
                  --teacher "$D/set_full_s$N/ckpt_best.pt" --student-delivery prefix --relay age --quant 4 --seed "$N" --out "$D/$tag" --iters 500;;
  relay_ppo_s*) "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_train_delivery_v10.py \
                  --out "$D/$tag" --seed "$N" --iters 2000 --eps-per-iter 8 --epochs 4 --minibatch 64 --lr 0.0003 --ent 0.01 --hidden 128 \
                  --eval-every 20 --threads 2 --audit-every 5 --delivery prefix --set-actor --relay age --quant 4;;
  *) echo "unknown $tag"; exit 2;;
esac
echo "exit $? $tag $(date)"
