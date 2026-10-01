#!/usr/bin/env bash
# D7 (29/09 23:3x), cheap eval-only checks still missing (ledger L-137):
#  (a) maxq (0 B heuristic) on the two new panels, the protocols' secondary comparator;
#  (b) FLAT full actors under the byte-budget variant (3 B packets, every receiver decodes all 8): does complete presence
#      fix even the flat actor (L-135's second fix)?  development panel;
#  (c) the byte-budget FRONTIER for set_full_s0 (3 B payloads, fresh-only): byte capacity 25 K_i spent on X-byte slots,
#      X = 6 / 12 / 25 (X = 25 is the packet protocol with compressed payloads), development panel.
# Watchdog on every eval.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929
run() {  # out log cmd...
  local out="$1"; shift
  [ -f "$out/manifest.json" ] && { echo "done $out"; return 0; }
  [ -e "$out" ] && mv "$out" "legacy/$(echo "$out" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "run $out $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$out.log" --out "$out" --stall 300 --retries 3 -- "$@" --out "$out" || echo "FAIL $out"
}
run research/marl_budget/e3_freshonly_newpanel_20260929/ref_maxq "$PY" -u scripts/MARL_e3_mp2_message_check.py --kinds maxq --deliveries none --traffic-seeds $(seq 2001 2064) --headways 8 16
run research/marl_budget/e3_bytebudget_panel_20260929/ref_maxq "$PY" -u scripts/MARL_e3_mp2_message_check.py --kinds maxq --deliveries none --traffic-seeds $(seq 2101 2164) --headways 8 16
run "$E/d7_flatfull_q4_bc3_fo" "$PY" -u scripts/MARL_e3_delivery_eval_v7.py --actors "full_s0=$D/full_s0/ckpt_best.pt" "full_s1=$D/full_s1/ckpt_best.pt" --deliveries prefix --capacity iid --adapter-override freshonly --quant 4 --byte-capacity 3 --traffic-seeds $(seq 901 964) --headways 8 16
for X in 6 12 25; do
  run "$E/d7_setfull_q4_bc${X}_fo" "$PY" -u scripts/MARL_e3_delivery_eval_v7.py --actors "set_full_s0=$D/set_full_s0/ckpt_best.pt" --deliveries prefix --capacity iid --adapter-override freshonly --quant 4 --byte-capacity "$X" --traffic-seeds $(seq 901 964) --headways 8 16
done
echo "D7 done $(date)"
