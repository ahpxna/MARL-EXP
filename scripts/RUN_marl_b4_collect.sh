#!/usr/bin/env bash
# B4 on-policy collection (PROTOCOL_B4_DAGGER_20260927.md §1): 4 shards in parallel into RUN.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
RUN="${1:?run dir}"; DEVMAP="${2:?dev map}"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY="external_envs/runtime/bin/python"
pids=()
for i in 0 1 2 3; do
  "$PY" -u scripts/MARL_hetero_onpolicy_collect.py --out "$RUN/o$i" --dev-map "$DEVMAP" --beta 0.5 --shard "$i" --nshards 4 > "$RUN/onpolicy_$i.log" 2>&1 &
  pids+=($!)
done
for p in "${pids[@]}"; do wait "$p"; done
echo "on-policy collection done $(date)"
for i in 0 1 2 3; do tail -1 "$RUN/onpolicy_$i.log"; done
