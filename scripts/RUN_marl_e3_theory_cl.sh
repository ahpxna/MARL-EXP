#!/usr/bin/env bash
# Closed-loop theory checks (ledger L-176), development panel 901-964 x 8/16, eval v4 (saturated ages), watchdog.
# Usage: bash scripts/RUN_marl_e3_theory_cl.sh VA <seed>     Paper-A repair mixture, beta grid, iid (prefix, cap4) and low
#        bash scripts/RUN_marl_e3_theory_cl.sh VS <seed>     STRUCTURAL budget frontier, const K = 1..7, four actor configs
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
what=$1; s=$2; D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_theory_cl_20260930; mkdir -p "$E"
ev() {  # tag actor-tag checkpoint args...
  local tag=$1 atag=$2 ck=$3; shift 3
  [ -f "$D/$ck/manifest.json" ] || { echo "skip $tag (no actor)"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 5 -- "$PY" -u scripts/MARL_e3_delivery_eval_relay_v4.py \
    --actors "$atag=$D/$ck/ckpt_best.pt" "$@" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
case "$what" in
  VA) for b in 0.05 0.1 0.25 0.5; do
        ev VA_s${s}_mix${b}_iid relay_st_s$s relay_st_s$s --relay age --quant 4 --order mix$b --capacity iid --deliveries prefix cap4
        ev VA_s${s}_mix${b}_low relay_st_s$s relay_st_s$s --relay age --quant 4 --order mix$b --capacity low --deliveries prefix
      done;;
  VS) for k in 1 2 3 4 5 6 7; do
        ev VS_s${s}_relay_agefirst_K$k relay_st_s$s relay_st_s$s --relay age --quant 4 --order agefirst --capacity const$k --deliveries prefix
        ev VS_s${s}_relay_prefix_K$k relay_st_s$s relay_st_s$s --relay age --quant 4 --order prefix --capacity const$k --deliveries prefix
        ev VS_s${s}_setprefix_K$k set_prefix_s$s set_prefix_s$s --order prefix --capacity const$k --deliveries prefix
        ev VS_s${s}_FO_K$k set_full_s$s set_full_s$s --adapter-override freshonly --order prefix --capacity const$k --deliveries prefix
      done;;
  *) echo "usage: VA|VS seed"; exit 2;;
esac
echo "theory cl $what lane $s done $(date)"
