#!/usr/bin/env bash
# P3/P4 diagnostics (30/09 09:3x; ledger L-155), development panel 901-964 x 8/16, watchdog on every eval.
#  P3: codebook REFIT on other TRAIN traffic (seeds 305-308) with another behaviour actor (set_full_s1); eval-only
#      byte-budget variant of set_full_s0 / set_full_s1 with codebook B.  Codebook A results: d5_q4_bc3_fo (s0), L-144.
#  P4: packet loss p = 0.1 / 0.25 / 0.5 of this step's deliveries (eval v8 --loss), for the TRAINED compressed set actors
#      set_fullq4_s0 / s1 and for the FLAT full actor full_s1 under the same byte-budget variant.  Does the set receiver
#      degrade gracefully where the flat one breaks (the sparse-presence mechanism, L-135)?
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; E=research/marl_budget/e3_codesign_eval_20260929; SEEDS=$(seq 901 964)
CBB=research/marl_budget/e3_payload_codebook_B_20260930.json
if [ ! -f "$CBB" ]; then
  "$PY" -u scripts/MARL_e3_payload_codebook.py --actor research/marl_budget/e3_delivery_actors_20260929/set_full_s1/ckpt_best.pt \
    --seeds 305 306 307 308 --scratch /private/tmp/claude-502/-Users-phanan-cig-amf-main/f9537975-549f-4276-ad79-40f2fa3240e3/scratchpad/codebookB_scen --out "$CBB" || echo "FAIL codebook B"
fi
ev() {  # tag actors deliveries quant bpp override loss codebook
  local tag=$1 actors=$2 dels=$3 q=$4 bpp=$5 ov=$6 loss=$7 cb=$8
  [ -f "$E/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  [ -e "$E/$tag" ] && mv "$E/$tag" "legacy/$(echo "$E/$tag" | tr '/' '_')_partial_$(date +%Y%m%d_%H%M%S)"
  echo "eval $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$E/$tag.log" --out "$E/$tag" --stall 300 --retries 3 -- \
    "$PY" -u scripts/MARL_e3_delivery_eval_v8.py --actors $actors --deliveries $dels --capacity iid --adapter-override "$ov" \
    --quant "$q" --byte-capacity "$bpp" --loss "$loss" --codebook "$cb" --traffic-seeds $SEEDS --headways 8 16 --out "$E/$tag" || echo "FAIL $tag"
}
CBA=research/marl_budget/e3_payload_codebook_20260929.json
ev p3_cbB_setfull "set_full_s0=$D/set_full_s0/ckpt_best.pt set_full_s1=$D/set_full_s1/ckpt_best.pt" prefix 4 3 freshonly 0 "$CBB"
for L in 0.1 0.25 0.5; do
  ev "p4_loss${L}_q4t" "set_fullq4_s0=$D/set_fullq4_s0/ckpt_best.pt set_fullq4_s1=$D/set_fullq4_s1/ckpt_best.pt" prefix 4 3 freshonly "$L" "$CBA"
  ev "p4_loss${L}_flat" "full_s1=$D/full_s1/ckpt_best.pt" prefix 4 3 freshonly "$L" "$CBA"
done
echo "P3/P4 done $(date)"
