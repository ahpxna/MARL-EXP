#!/usr/bin/env bash
# D5 (29/09 22:5x), direction 2 diagnostic (ledger L-128): SENDER-side payload compression (codebook fitted on TRAIN traffic,
# research/marl_budget/e3_payload_codebook_20260929.json) for the set_full_s0 actor, eval-only, development panel 901-964.
#  (i)  full delivery with payloads quantised to L = 2/4/8/16 levels (13/21/29/37 bits = 2/3/4/5 B per packet);
#  (ii) the BYTES-limited protocol variant: the broadcast prefix stream, a receiver with raw capacity K decodes
#       floor(25 K / bpp) compressed packets (capped at 8), fresh-only receiver.  Smoke parity (seed 901 h8): bpp 3 + L 4 +
#       prefix == full + L 4 (1750.0), and --quant 0 reproduces v6 (1803.0).
# Watchdog on every eval (stall 300 s, --out, 3 retries).
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
A=set_full_s0=research/marl_budget/e3_delivery_actors_20260929/set_full_s0/ckpt_best.pt; E=research/marl_budget/e3_codesign_eval_20260929
JOBS=("d5_q2_full|full|2|0|default" "d5_q4_full|full|4|0|default" "d5_q8_full|full|8|0|default" "d5_q16_full|full|16|0|default"
      "d5_q2_bc2_fo|prefix|2|2|freshonly" "d5_q4_bc3_fo|prefix|4|3|freshonly" "d5_q8_bc4_fo|prefix|8|4|freshonly" "d5_q16_bc5_fo|prefix|16|5|freshonly")
for j in "${JOBS[@]}"; do
  IFS='|' read -r tag dels q bpp ov <<< "$j"
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; continue; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v7.py --actors "$A" --deliveries $dels --capacity iid --adapter-override "$ov" \
    --quant "$q" --byte-capacity "$bpp" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
done
echo "D5 done $(date)"
