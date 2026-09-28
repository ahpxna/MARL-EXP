#!/usr/bin/env bash
# B2 confirmation (research/marl_budget/PROTOCOL_B2_FRESH_BID_20260927.md §4-§6).
# Refuses to run unless the protocol already carries the appended "§5 FROZEN DESIGN" and the
# freeze file exists.  4 collector shards -> mirror + response replays -> frozen-model evaluation.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
RUN="${1:?run dir}"; DEV="${2:?development dir}"; FREEZE="${3:?freeze json}"
PROTO=research/marl_budget/PROTOCOL_B2_FRESH_BID_20260927.md
grep -q '^## §5 FROZEN DESIGN' "$PROTO" || { echo "design not frozen in $PROTO" >&2; exit 2; }
[ -f "$FREEZE" ] || { echo "missing freeze file $FREEZE" >&2; exit 2; }
if [ -e "$RUN" ]; then printf 'Refusing to overwrite existing run: %s\n' "$RUN" >&2; exit 2; fi
mkdir -p "$RUN"; cp "$FREEZE" "$RUN/freeze.json"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY="external_envs/runtime/bin/python"
NS=4; pids=()
for i in $(seq 0 $((NS-1))); do
  "$PY" -u scripts/MARL_hetero_b2_collect.py --shard "$i" --nshards "$NS" --out "$RUN/labels_c$i" > "$RUN/collect_$i.log" 2>&1 &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
echo "collection done $(date)"
pids=()
for i in $(seq 0 $((NS-1))); do
  ( "$PY" -u scripts/MARL_hetero_mirror_replay.py --labels "$RUN/labels_c$i" --out "$RUN/mirror_c$i" > "$RUN/replay_$i.log" 2>&1 &&
    "$PY" -u scripts/MARL_hetero_response_replay.py --labels "$RUN/labels_c$i" --out "$RUN/response_c$i" > "$RUN/response_$i.log" 2>&1 ) &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
echo "replays done $(date)"
"$PY" -u scripts/MARL_hetero_b2_confirm.py --dev "$DEV" --confirm-run "$RUN" --freeze "$RUN/freeze.json" --out "$RUN/confirm" > "$RUN/confirm.log" 2>&1
echo "confirmation done $(date)"
tail -30 "$RUN/confirm.log"
