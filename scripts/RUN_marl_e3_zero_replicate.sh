#!/usr/bin/env bash
# V-U NULL (ledger L-178): a SECOND zero-byte student per teacher, identical command to distill_none_s<s>
# (scripts/MARL_e3_actor_distill.py, same teacher, --student-delivery none, 500 iterations) except the seed (100 + s).
# Why: the V-U split "zero-byte student disagrees with the teacher" makes "relay's gain sits in that split" true by
# construction.  The informative quantity is relay's recovery rate there MINUS the recovery rate of another imitator with
# the same (local) information.  After training, the probe is re-run with --zero = the replicate on the same states.
# Usage: bash scripts/RUN_marl_e3_zero_replicate.sh <seed>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_theory_probe_rep_20260930; P=research/marl_budget/e3_satrot_eval_20260930
tag=distill_none_rep_s$s; mkdir -p "$E"
if [ ! -f "$D/$tag/manifest.json" ]; then
  [ -e "$D/$tag" ] && mv "$D/$tag" "legacy/${tag}_partial_$(date +%Y%m%d_%H%M%S)"
  echo "train $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill.py \
    --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery none --out "$D/$tag" --seed $((100 + s)) --iters 500 --threads 2 || { echo "FAIL $tag"; exit 1; }
fi
pr() {  # tag order rule capacity parity-dir
  local t=$1 order=$2 rule=$3 cap=$4 par=$5
  [ -f "$E/$t/manifest.json" ] && { echo "done $t"; return 0; }
  [ -e "$E/$t" ] && mv "$E/$t" "legacy/$(echo "$E/$t" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "probe $t $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$t.log" --out "$E/$t" --stall 300 --retries 5 -- "$PY" -u scripts/MARL_e3_theory_probe.py \
    --relay "$D/relay_st_s$s/ckpt_best.pt" --teacher "$D/set_full_s$s/ckpt_best.pt" --zero "$D/$tag/ckpt_best.pt" \
    --order "$order" --rule "$rule" --capacity "$cap" --traffic-seeds $(seq 901 964) --headways 8 16 --parity "$P/$par/rows.json" --out "$E/$t" || echo "FAIL $t"
}
for o in agefirst prefix; do
  pr s${s}_${o}_iid $o prefix iid relay_st_s${s}_${o}_iid
  pr s${s}_${o}_cap4 $o cap4 iid relay_st_s${s}_${o}_iid
  pr s${s}_${o}_low $o prefix low relay_st_s${s}_${o}_low
done
echo "zero replicate lane $s done $(date)"
