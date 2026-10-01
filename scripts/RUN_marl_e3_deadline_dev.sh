#!/usr/bin/env bash
# LIFETIME-DEADLINE head, development panel 901-964 x 8/16 (ledger L-178), eval v5 (scripts/MARL_e3_delivery_eval_relay_v5.py).
# Actor relay_st_s<seed> (the pre-registered students), relay age, quant 4.  Orders deadline<D>, D in {2, 3, 4, 6} decision steps;
# D = inf reproduces the prefix order row for row (smoke 16:2x, 8/8), so beta-0 / agefirst references are the satrot rows.
# Reading rule, written BEFORE the result: the deadline head DOMINATES if, for some single D chosen on this panel, on BOTH seeds it
# is (i) within +0.3 % of the prefix order at iid, and (ii) no worse than agefirst by more than 0.3 % at cap4 and low, and
# (iii) better than the better of the two in at least 3 of the 6 cells.  Only then is a pre-registered panel written.
# Usage: bash scripts/RUN_marl_e3_deadline_dev.sh <seed>
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
s=$1; D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_deadline_dev_20260930; mkdir -p "$E"
ev() {  # tag args...
  local tag=$1; shift
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 5 -- "$PY" -u scripts/MARL_e3_delivery_eval_relay_v5.py \
    --actors "relay_st_s$s=$D/relay_st_s$s/ckpt_best.pt" --relay age --quant 4 "$@" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
for d in 3 2 4 6; do
  ev DL_s${s}_D${d}_iid --order deadline$d --capacity iid --deliveries prefix cap4
  ev DL_s${s}_D${d}_low --order deadline$d --capacity low --deliveries prefix
done
echo "deadline dev lane $s done $(date)"
