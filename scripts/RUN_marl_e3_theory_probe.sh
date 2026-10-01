#!/usr/bin/env bash
# THEORY PROBE runs (ledger L-176), development panel 901-964 x 8/16, parity against the satrot evaluator rows.
# Usage: bash scripts/RUN_marl_e3_theory_probe.sh <seed>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_theory_probe_20260930; P=research/marl_budget/e3_satrot_eval_20260930
mkdir -p "$E"
pr() {  # tag order rule capacity parity-dir
  local tag=$1 order=$2 rule=$3 cap=$4 par=$5
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "probe $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 5 -- "$PY" -u scripts/MARL_e3_theory_probe.py \
    --relay "$D/relay_st_s$s/ckpt_best.pt" --teacher "$D/set_full_s$s/ckpt_best.pt" --zero "$D/distill_none_s$s/ckpt_best.pt" \
    --order "$order" --rule "$rule" --capacity "$cap" --traffic-seeds $(seq 901 964) --headways 8 16 --parity "$P/$par/rows.json" --out "$E/$tag" || echo "FAIL $tag"
}
for o in agefirst prefix; do
  pr s${s}_${o}_iid $o prefix iid relay_st_s${s}_${o}_iid
  pr s${s}_${o}_cap4 $o cap4 iid relay_st_s${s}_${o}_iid
  pr s${s}_${o}_low $o prefix low relay_st_s${s}_${o}_low
done
echo "theory probe lane $s done $(date)"
