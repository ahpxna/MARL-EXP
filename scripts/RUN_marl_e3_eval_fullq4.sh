#!/usr/bin/env bash
# Eval of the TRAINED compressed-payload actor set_fullq4_s0 (ledger L-143), development panel 901-964 x 8/16, eval v7 with the
# SAME codebook and L = 4 as in training: (a) the byte-budget variant (bpp 3, fresh-only, prefix); (b) full delivery with 3 B
# payloads; (c) no messages; (d) the PACKET protocol with 3 B payloads (K_i packets, fresh-only).  Watchdog.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929; A="set_fullq4_s0=$D/set_fullq4_s0/ckpt_best.pt"
JOBS=("q4t_bc3_fo|prefix|3|freshonly" "q4t_full|full none|0|default" "q4t_packet_fo|prefix|0|freshonly")
for j in "${JOBS[@]}"; do
  IFS='|' read -r tag dels bpp ov <<< "$j"
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v7.py --actors "$A" --deliveries $dels --capacity iid --adapter-override "$ov" --quant 4 \
    --byte-capacity "$bpp" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
echo "fullq4 evals done $(date)"
