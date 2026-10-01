#!/usr/bin/env bash
# Papers A / B / C experiments on the RELAY method (30/09 13:1x; ledger L-164).  PREPARED; each stage is run by hand.
# All inside PROTOCOL_HETERO_v0 (packet channel unchanged).  Development panel first; a pre-registration is written BEFORE any
# new-panel run.  Watchdog on every run.  Smoke tests passed 13:0x-13:1x (see L-164).
#
#   bash scripts/RUN_marl_e3_ABC.sh A-fit      codebook v2: refit on the relay student's own states (+ beta = 0.5 mixture)
#   bash scripts/RUN_marl_e3_ABC.sh A-train    relay students s0/s1 with codebook v2 key 4 and key 50004
#   bash scripts/RUN_marl_e3_ABC.sh B-fit      decision-focused codebook: field sensitivity + bit allocation (keys 9008/9012/9016)
#   bash scripts/RUN_marl_e3_ABC.sh B-train    relay students s0/s1 with keys 9008 (2 B) and 9016 (3 B, decision-focused)
#   bash scripts/RUN_marl_e3_ABC.sh C-diag     coverage and age of relay views: prefix vs agefirst, iid / cap4 / cap2 / low
#   bash scripts/RUN_marl_e3_ABC.sh C-train    relay students s0/s1 with the agefirst order, and with the low capacity process
#   bash scripts/RUN_marl_e3_ABC.sh eval       development-panel evals of every finished A/B/C student (skips unfinished)
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=2; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929; M=research/marl_budget
SCR=/private/tmp/claude-502/-Users-phanan-cig-amf-main/f9537975-549f-4276-ad79-40f2fa3240e3/scratchpad
CBA=$M/e3_payload_codebook_20260929.json; CBR=$M/e3_payload_codebook_relay_20260930.json; CBS=$M/e3_field_sensitivity_20260930.json
student() {  # tag seed extra-args...   (DAgger relay student from set_full_s<seed>, distill v5)
  local tag=$1 s=$2; shift 2
  [ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  echo "train $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v5.py \
    --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed "$s" --out "$D/$tag" --iters 500 "$@"
}
ev() {  # tag actor deliveries capacity extra-args...   (relay eval v2)
  local tag=$1 actor=$2 dels=$3 cap=$4; shift 4
  [ -f "$D/$actor/manifest.json" ] || { echo "skip $tag"; return 0; }
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  OMP_NUM_THREADS=1 "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_relay_v2.py --actors "$actor=$D/$actor/ckpt_best.pt" --deliveries $dels --capacity "$cap" \
    --relay age "$@" --traffic-seeds $(seq 901 964) --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
case "${1:-}" in
  A-fit) [ -f "$CBR" ] || "$PY" -u scripts/MARL_e3_payload_codebook_v2.py --relay-actor "$D/relay_st_s0/ckpt_best.pt" --seeds 309 310 311 312 \
           --levels 4 --betas 0.5 --scratch "$SCR/cbR_scen" --out "$CBR";;
  A-train) for s in 0 1; do student relayA4_st_s$s $s --quant 4 --codebook "$CBR" & student relayA504_st_s$s $s --quant 50004 --codebook "$CBR" & done; wait;;
  B-fit) [ -f "$CBS" ] || "$PY" -u scripts/MARL_e3_field_sensitivity.py --actor "$D/relay_st_s0/ckpt_best.pt" --seeds 313 314 315 316 \
           --budgets 8 12 16 --scratch "$SCR/fs_scen_full" --out "$CBS";;
  B-train) for s in 0 1; do student relayB8_st_s$s $s --quant 9008 --codebook "$CBS" & student relayB16_st_s$s $s --quant 9016 --codebook "$CBS" & done; wait;;
  C-diag) for o in prefix agefirst; do f=$M/e3_relay_age_diag_${o}_20260930.json; [ -f "$f" ] || "$PY" -u scripts/MARL_e3_relay_age_diag.py \
            --actor "$D/relay_st_s0/ckpt_best.pt" --seeds $(seq 901 916) --conditions $([ "$o" = agefirst ] && echo "prefix:iid prefix:low" || echo "prefix:iid cap4:iid cap2:iid prefix:low") --order "$o" \
            --scratch "$SCR/age_scen_$o" --out "$f"; done;;
  C-train) for s in 0 1; do student relayCage_st_s$s $s --quant 4 --order agefirst & student relayClow_st_s$s $s --quant 4 --capacity low & done; wait;;
  eval) for s in 0 1; do
          ev relayA4_st_s${s}_eval relayA4_st_s$s "prefix cap4" iid --quant 4 --codebook "$CBR"
          ev relayA504_st_s${s}_eval relayA504_st_s$s "prefix cap4" iid --quant 50004 --codebook "$CBR"
          ev relayB8_st_s${s}_eval relayB8_st_s$s "prefix cap4" iid --quant 9008 --codebook "$CBS"
          ev relayB16_st_s${s}_eval relayB16_st_s$s "prefix cap4" iid --quant 9016 --codebook "$CBS"
          ev relayCage_st_s${s}_eval relayCage_st_s$s "prefix" iid --quant 4 --order agefirst   # cap<c> + agefirst is UNCAPPED in deliver_agefirst (bug found by the parallel session, ledger L-168 13:2x); cap-correct orders: models/marl_delivery_music.py
          ev relayClow_st_s${s}_eval relayClow_st_s$s "prefix cap4" iid --quant 4
          ev relayClow_st_s${s}_evlow relayClow_st_s$s "prefix" low --quant 4
          ev relay_st_s${s}_evlow relay_st_s$s "prefix" low --quant 4
          ev relay_st_s${s}_evage relay_st_s$s "prefix" iid --quant 4 --order agefirst
        done;;
  *) echo "usage: $0 A-fit|A-train|B-fit|B-train|C-diag|C-train|eval"; exit 2;;
esac
echo "$1 done $(date)"
