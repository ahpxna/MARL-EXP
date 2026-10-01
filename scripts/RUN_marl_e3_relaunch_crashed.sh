#!/usr/bin/env bash
# Re-run the relay students that crashed on the full disk at 15:36-15:40 on 30/09 (ledger L-177), with the SAME commands as
# the stopped session's launchers (scripts/RUN_marl_e3_ABC_v2.sh student(), scripts/RUN_marl_e3_ABC_v2b.sh seeds()).
# Partial directories and logs are moved to legacy/ first (never deleted).
# Usage: bash scripts/RUN_marl_e3_relaunch_crashed.sh A      relay6A4_st_s0, relay6A504_st_s1 (Paper-A codebook students)
#        bash scripts/RUN_marl_e3_relaunch_crashed.sh seeds  relay6Cage_st_s4..s9, two at a time
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1 OMP_NUM_THREADS=1; PY=external_envs/runtime/bin/python
D=research/marl_budget/e3_delivery_actors_20260929; M=research/marl_budget; CBR=$M/e3_payload_codebook_relay_20260930.json
student() {  # tag seed extra-args...
  local tag=$1 s=$2; shift 2
  [ -f "$D/$tag/manifest.json" ] && { echo "done $tag"; return 0; }
  if pgrep -f -- "--out $D/$tag " > /dev/null; then echo "in progress elsewhere: $tag"; return 0; fi
  local stamp; stamp=$(date +%Y%m%d_%H%M%S)
  [ -e "$D/$tag" ] && mv "$D/$tag" "legacy/${tag}_diskfull_crash_$stamp"
  [ -e "$D/$tag.log" ] && mv "$D/$tag.log" "legacy/${tag}_diskfull_crash_$stamp.log"
  echo "train $tag $(date)"
  "$PY" scripts/run_with_watchdog.py --log "$D/$tag.log" --out "$D/$tag" --stall 900 --retries 3 -- "$PY" -u scripts/MARL_e3_actor_distill_v6.py \
    --teacher "$D/set_full_s$s/ckpt_best.pt" --student-delivery prefix --relay age --seed "$s" --out "$D/$tag" --iters 500 "$@" || echo "FAIL $tag"
}
case "${1:-}" in
  A) student relay6A4_st_s0 0 --quant 4 --codebook "$CBR" & student relay6A504_st_s1 1 --quant 50004 --codebook "$CBR" & wait;;
  seeds) for pair in "4 5" "6 7" "8 9"; do
           for s in $pair; do student relay6Cage_st_s$s $s --quant 4 --order agefirst & done; wait
         done;;
  *) echo "usage: A|seeds"; exit 2;;
esac
echo "relaunch $1 done $(date)"
