#!/usr/bin/env bash
# v2 of RUN_marl_e3_resume.sh (28/09 10:25): the shard count no longer exits the script under pipefail when a
# freshly trained actor has no label dirs yet (v1 stopped silently after training seeds 1, 2, 4).
# Resume an E3 chain (RUN_marl_e3_long.sh / RUN_marl_e3_long_scratch.sh) after hung CityFlow processes, 28/09/2026.
# Every stage whose output has a manifest is kept; any partial output is moved to legacy/ (never deleted) and the
# stage is rerun under scripts/run_with_watchdog.py (labels: v2 producer, resumed IN PLACE, 28/09 11:40) (kill + retry when its log is silent for STALL seconds).
# The label shard partition is the ORIGINAL one (NSHARDS is read from the existing shard dirs).
# Usage: bash scripts/RUN_marl_e3_resume.sh <run dir> <bc|scratch> "<actor seeds>"
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
RUN="${1:?run dir}"; KIND="${2:?bc|scratch}"; SEEDS="${3:?seeds}"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY=external_envs/runtime/bin/python; WD="$PY scripts/run_with_watchdog.py"; STALL=${STALL:-1800}
if [ "${SKIP_HANG_GUARD:-0}" != 1 ] && pgrep -f "python.*scripts/MARL_e3_" > /dev/null; then echo "refusing: MARL_e3 processes are still running (stop the hung runs first)"; exit 2; fi
if [ "$KIND" = bc ]; then PROTO=research/marl_budget/PROTOCOL_E3_PILOT_20260928.md; else PROTO=research/marl_budget/PROTOCOL_E3_SCRATCH_20260928.md; fi
echo "resume ($KIND) protocol sha256 $(shasum -a 256 $PROTO | cut -d' ' -f1) $(date)" | tee -a "$RUN/chain.log"
TS=$(date +%Y%m%d_%H%M%S)
park() { [ -e "$1" ] && mv "$1" "legacy/$(echo "$1" | tr '/' '_')_partial_$TS"; return 0; }
waitall() { local rc=0; for p in "$@"; do wait "$p" || rc=$?; done; [ "$rc" = 0 ] || { echo "a stage failed (rc $rc)" | tee -a "$RUN/chain.log"; exit "$rc"; }; }
for S in $SEEDS; do
  D="$RUN/actor_s$S"
  if [ ! -f "$D/manifest.json" ]; then
    park "$D"; echo "== s$S actor (re)train $(date)" | tee -a "$RUN/chain.log"
    if [ "$KIND" = bc ]; then
      $WD --log "$D.train.log" --out "$D" --stall 900 -- "$PY" -u scripts/MARL_e3_actor_train_v2.py --out "$D" --seed "$S" --bc-epochs 30 --warmup 20 --iters 300 --eval-every 10
    else
      $WD --log "$D.train.log" --out "$D" --stall 900 -- "$PY" -u scripts/MARL_e3_actor_train.py --out "$D" --seed "$S" --iters 2000 --eps-per-iter 8 --eval-every 20
    fi
  fi
  CK="$D/ckpt_best.pt"
  if [ ! -f "$D/msguse/manifest.json" ]; then
    park "$D/msguse"; $WD --log "$D/msguse.log" --out "$D/msguse" --stall $STALL -- "$PY" -u scripts/MARL_e3_message_use.py --ckpt "$CK" --out "$D/msguse" --seeds $(seq -s ' ' 501 508)
  fi
  N=$( (ls -d "$D"/labels_train_[0-9]* 2>/dev/null || true) | (grep -v '\.log$' || true) | wc -l | tr -d ' ')   # v2: no pipefail exit on a fresh actor
  [ "$N" -gt 0 ] || N=${NSHARDS:-3}
  echo "== s$S labels (shards $N) $(date)" | tee -a "$RUN/chain.log"; PIDS=""
  for k in $(seq 0 $((N - 1))); do
    L="$D/labels_train_$k"
    if [ ! -f "$L/manifest.json" ]; then
      $WD --log "$L.log" --stall $STALL -- "$PY" -u scripts/MARL_e3_continuation_labels_v2.py --ckpt "$CK" --out "$L" --split train --snaps 7 10 13 16 19 22 --limit 0 --shard $k --nshards $N & PIDS="$PIDS $!"
    fi
  done
  for sp in select dev; do
    L="$D/labels_$sp"
    if [ ! -f "$L/manifest.json" ]; then
      $WD --log "$L.log" --stall $STALL -- "$PY" -u scripts/MARL_e3_continuation_labels_v2.py --ckpt "$CK" --out "$L" --split $sp --snaps 10 16 22 --limit 0 & PIDS="$PIDS $!"
    fi
  done
  [ -z "$PIDS" ] || waitall $PIDS
  for f in "$D"/labels_*/manifest.json; do python3 -c "import json,sys; m=json.load(open(sys.argv[1])); assert m['self_check']=='PASS', sys.argv[1]" "$f"; done
  echo "== s$S selectors $(date)" | tee -a "$RUN/chain.log"; PIDS=""
  for s in 0 1 2; do
    [ -f "$D/selectors/job_sel_nobid_s$s.json" ] || { "$PY" -u scripts/MARL_e3_selector_train.py --train "$D/labels_train_*" --select "$D/labels_select" --dev "$D/labels_dev" --out "$D/selectors" --name sel_nobid --seed $s --epochs 40 > "$D/sel_nobid_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
    [ -f "$D/selectors/job_sel_bid_s$s.json" ] || { "$PY" -u scripts/MARL_e3_selector_train.py --train "$D/labels_train_*" --select "$D/labels_select" --dev "$D/labels_dev" --out "$D/selectors" --name sel_bid --bid --seed $s --epochs 40 > "$D/sel_bid_s$s.log" 2>&1 & PIDS="$PIDS $!"; }
  done
  [ -z "$PIDS" ] || waitall $PIDS
  echo "== s$S closed loop $(date)" | tee -a "$RUN/chain.log"; PIDS=""
  for P in direct R1; do
    C="$D/cl_$P"; EXTRA=""; [ "$P" = direct ] && EXTRA="--mp2"
    if [ ! -f "$C/manifest.json" ]; then park "$C"
      $WD --log "$C.log" --out "$C" --stall $STALL -- "$PY" -u scripts/MARL_e3_closed_loop.py --actor "$CK" --selectors "$D/selectors" --names sel_nobid sel_bid --policy $P $EXTRA --out "$C" --traffic-seeds $(seq -s ' ' 901 916) & PIDS="$PIDS $!"
    fi
  done
  [ -z "$PIDS" ] || waitall $PIDS
  for P in cl_direct cl_R1; do
    python3 scripts/MARL_hetero_closed_loop_report.py "$D/$P" --control sel_nobid > "$D/$P/full_endpoints.txt"
    "$PY" scripts/MARL_make_fig3_v4.py --run "$D/$P" --out "$D/figures" --stem "fig3_e3_s${S}_$P" --title "E3 $KIND actor seed $S, $P (pilot panel)" >> "$D/figures.log" 2>&1
  done
  echo "== s$S done $(date)" | tee -a "$RUN/chain.log"
done
echo "RESUME COMPLETE $(date)" | tee -a "$RUN/chain.log"
