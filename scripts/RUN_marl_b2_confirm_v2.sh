#!/usr/bin/env bash
# B2 confirmation v2 (PROTOCOL_B2_FRESH_BID_20260927.md, Amendment 1 and §5 FROZEN DESIGN).
# Refuses unless the protocol carries both, and the freeze + dev-map files exist.
# 4 collector shards -> mirror, response, request-bid and top-2-bid replays -> frozen evaluation.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
RUN="${1:?run dir}"; DEVMAP="${2:?dev-map json}"; FREEZE="${3:?freeze json}"
PROTO=research/marl_budget/PROTOCOL_B2_FRESH_BID_20260927.md
grep -q '^## Amendment 1' "$PROTO" || { echo "Amendment 1 missing in $PROTO" >&2; exit 2; }
grep -q '^## §5 FROZEN DESIGN' "$PROTO" || { echo "design not frozen in $PROTO" >&2; exit 2; }
[ -f "$FREEZE" ] && [ -f "$DEVMAP" ] || { echo "missing freeze or dev-map" >&2; exit 2; }
if [ -e "$RUN" ]; then printf 'Refusing to overwrite existing run: %s\n' "$RUN" >&2; exit 2; fi
mkdir -p "$RUN"; cp "$FREEZE" "$RUN/freeze.json"; cp "$DEVMAP" "$RUN/dev_map.json"
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
    "$PY" -u scripts/MARL_hetero_response_replay.py --labels "$RUN/labels_c$i" --out "$RUN/response_c$i" > "$RUN/response_$i.log" 2>&1 &&
    "$PY" -u scripts/MARL_hetero_bid_replay.py --labels "$RUN/labels_c$i" --out "$RUN/bid2_c$i" > "$RUN/bid2_$i.log" 2>&1 &&
    "$PY" -u scripts/MARL_hetero_bid_replay_v2.py --labels "$RUN/labels_c$i" --out "$RUN/bid3_c$i" > "$RUN/bid3_$i.log" 2>&1 ) &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
echo "replays done $(date)"
"$PY" -u scripts/MARL_hetero_b2_confirm_v2.py --dev-map "$RUN/dev_map.json" --confirm-run "$RUN" --freeze "$RUN/freeze.json" --out "$RUN/confirm" > "$RUN/confirm.log" 2>&1
echo "confirmation done $(date)"
tail -30 "$RUN/confirm.log"
