#!/usr/bin/env bash
# DECISION-DEPTH PROBE v2 (both bases: direct cache / empty), ledger L-194.  Usage:
#   bash scripts/RUN_marl_e3_decision_depth_v2.sh pair <seed>     relay_st_s<seed> x agefirst/prefix x low/iid
#   bash scripts/RUN_marl_e3_decision_depth_v2.sh ten <s> [<s> ...]  relay6Cage_st_s<s>, agefirst, low (V-D10)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_decision_depth_v2_20261001; P=research/marl_budget/e3_satrot_eval_20260930
mkdir -p "$E"
pr() {  # tag relay order rule capacity parity-dir
  local tag=$1 relay=$2 teacher=$3 order=$4 rule=$5 cap=$6 par=$7
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "probe $tag $(date)"
  nice -n 5 "$PY" -u scripts/MARL_e3_decision_depth_probe_v2.py --relay "$D/$relay/ckpt_best.pt" --teacher "$D/$teacher/ckpt_best.pt" \
    --order "$order" --rule "$rule" --capacity "$cap" --traffic-seeds $(seq 901 964) --headways 8 16 --parity "$P/$par/rows.json" --out "$E/$tag" > "$E/$tag.log" 2>&1 || echo "FAIL $tag"
  tail -1 "$E/$tag.log"
}
mode=$1; shift
if [ "$mode" = pair ]; then
  s=$1
  for o in agefirst prefix; do for c in low iid; do
    pr s${s}_${o}_${c} relay_st_s$s set_full_s$s $o prefix $c relay_st_s${s}_${o}_${c}
  done; done
else
  for s in "$@"; do pr cage_s${s}_agefirst_low relay6Cage_st_s$s set_full_s$s agefirst prefix low relay6Cage_st_s${s}_agefirst_low; done
fi
echo "ALL DONE $mode $* $(date)"
