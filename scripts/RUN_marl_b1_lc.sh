#!/usr/bin/env bash
# B1 learning curve (research/marl_budget/PROTOCOL_B1_LEARNING_CURVE_20260927.md).
# 4 collector shards -> 4 mirror replays -> sealed-test training.  Refuses to overwrite a run.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
RUN="${1:?run dir}"
if [ -e "$RUN" ]; then printf 'Refusing to overwrite existing run: %s\n' "$RUN" >&2; exit 2; fi
mkdir -p "$RUN"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY="external_envs/runtime/bin/python"
NS=4
pids=()
for i in $(seq 0 $((NS-1))); do
  "$PY" -u scripts/MARL_hetero_lc_collect.py --shard "$i" --nshards "$NS" --out "$RUN/labels_$i" > "$RUN/collect_$i.log" 2>&1 &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
echo "collection done $(date)"
pids=()
for i in $(seq 0 $((NS-1))); do
  "$PY" -u scripts/MARL_hetero_mirror_replay.py --labels "$RUN/labels_$i" --out "$RUN/mirror_$i" > "$RUN/replay_$i.log" 2>&1 &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
echo "replay done $(date)"
SH=()
for i in $(seq 0 $((NS-1))); do SH+=("$RUN/labels_$i:$RUN/mirror_$i"); done
"$PY" -u scripts/MARL_hetero_lc_train.py --shards "${SH[@]}" --out "$RUN/train" --workers 4 > "$RUN/train.log" 2>&1
echo "training done $(date)"
tail -5 "$RUN/train.log"
