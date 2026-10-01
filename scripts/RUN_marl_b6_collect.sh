#!/usr/bin/env bash
# B6 robustness panels (PROTOCOL_B6_ROBUSTNESS_20260927.md): all panels in parallel, 2 shards each.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
RUN="${1:?run dir}"; mkdir -p "$RUN"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY="external_envs/runtime/bin/python"
pids=()
launch() {  # name capacity headways seeds...
  local name=$1 cap=$2 hw=$3; shift 3
  for i in 0 1; do
    "$PY" -u scripts/MARL_hetero_panel_collect.py --out "$RUN/$name/p$i" --split rob --tag "$name" --capacity "$cap" \
      --headways $hw --seeds "$@" --shard "$i" --nshards 2 > "$RUN/${name}_$i.log" 2>&1 &
    pids+=($!)
  done
}
launch cap_fixed fixed "8 16" $(seq 1001 1008)
launch cap_bursty bursty "8 16" $(seq 1011 1018)
launch cap_low low "8 16" $(seq 1021 1028)
launch cap_high high "8 16" $(seq 1031 1038)
launch load_12 iid "12" $(seq 1041 1048)
launch load_24 iid "24" $(seq 1051 1058)
launch load_5 iid "5" $(seq 1061 1068)
for p in "${pids[@]}"; do wait "$p"; done
echo "B6 collection done $(date)"
for f in "$RUN"/*_[01].log; do tail -1 "$f"; done
