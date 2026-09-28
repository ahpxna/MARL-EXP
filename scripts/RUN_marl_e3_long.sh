#!/usr/bin/env bash
# E3 long chain (research/marl_budget/PROTOCOL_E3_PILOT_20260928.md), per actor seed:
#   actor (BC + MAPPO) -> message-use check (dev) -> continuation labels (train/select/dev, sharded)
#   -> selectors (no bid / bid, 3 init seeds) -> closed loop (direct and R1) -> reports + fig3.
# Usage: bash scripts/RUN_marl_e3_long.sh <run dir> "<actor seeds>"
# Smoke: SMOKE=1 bash scripts/RUN_marl_e3_long.sh <dir> 0   (tiny settings, same code path)
set -euo pipefail
waitall() { local rc=0; for p in "$@"; do wait "$p" || rc=$?; done; [ "$rc" = 0 ] || { echo "a background job failed (rc $rc)" | tee -a "$RUN/chain.log"; exit "$rc"; }; }
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
RUN="${1:?run dir}"; SEEDS="${2:-0 1 2}"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY=external_envs/runtime/bin/python
PROTO=research/marl_budget/PROTOCOL_E3_PILOT_20260928.md
if [ "${SMOKE:-0}" = "1" ]; then
  BC_EPOCHS=2; WARMUP=1; ITERS=2; EVAL_EVERY=1; LIMIT=2; SNAPS_TRAIN="4 7"; SNAPS_EVAL="4"; NSHARDS=2
  SEL_EPOCHS=4; CL_SEEDS="901"; MSG_SEEDS="501"; EVAL_LIMIT=1
else
  BC_EPOCHS=${BC_EPOCHS:-30}; WARMUP=${WARMUP:-20}; ITERS=${ITERS:-300}; EVAL_EVERY=${EVAL_EVERY:-10}; LIMIT=0
  SNAPS_TRAIN="7 10 13 16 19 22"; SNAPS_EVAL="10 16 22"; NSHARDS=${NSHARDS:-6}; SEL_EPOCHS=40
  CL_SEEDS="$(seq -s ' ' 901 916)"; MSG_SEEDS="$(seq -s ' ' 501 508)"; EVAL_LIMIT=0
fi
mkdir -p "$RUN"
H0=$(shasum -a 256 "$PROTO" | cut -d' ' -f1); echo "protocol sha256 $H0 $(date)" | tee -a "$RUN/chain.log"
for S in $SEEDS; do
  D="$RUN/actor_s$S"
  echo "== actor seed $S: training $(date)" | tee -a "$RUN/chain.log"
  "$PY" -u scripts/MARL_e3_actor_train_v2.py --out "$D" --seed "$S" --bc-epochs $BC_EPOCHS --warmup $WARMUP --iters $ITERS \
      --eval-every $EVAL_EVERY > "$D.train.log" 2>&1
  CK="$D/ckpt_best.pt"; tail -1 "$D.train.log" | tee -a "$RUN/chain.log"
  echo "== actor seed $S: message use $(date)" | tee -a "$RUN/chain.log"
  "$PY" -u scripts/MARL_e3_message_use.py --ckpt "$CK" --out "$D/msguse" --seeds $MSG_SEEDS > "$D/msguse.log" 2>&1
  echo "== actor seed $S: continuation labels $(date)" | tee -a "$RUN/chain.log"
  PIDS=""
  for k in $(seq 0 $((NSHARDS - 1))); do
    "$PY" -u scripts/MARL_e3_continuation_labels.py --ckpt "$CK" --out "$D/labels_train_$k" --split train --snaps $SNAPS_TRAIN \
        --limit $LIMIT --shard $k --nshards $NSHARDS > "$D/labels_train_$k.log" 2>&1 & PIDS="$PIDS $!"
  done
  "$PY" -u scripts/MARL_e3_continuation_labels.py --ckpt "$CK" --out "$D/labels_select" --split select --snaps $SNAPS_EVAL --limit $EVAL_LIMIT > "$D/labels_select.log" 2>&1 & PIDS="$PIDS $!"
  "$PY" -u scripts/MARL_e3_continuation_labels.py --ckpt "$CK" --out "$D/labels_dev" --split dev --snaps $SNAPS_EVAL --limit $EVAL_LIMIT > "$D/labels_dev.log" 2>&1 & PIDS="$PIDS $!"
  waitall $PIDS
  for f in "$D"/labels_*/manifest.json; do python3 -c "import json,sys; m=json.load(open(sys.argv[1])); assert m['self_check']=='PASS', sys.argv[1]" "$f"; done
  echo "== actor seed $S: selectors $(date)" | tee -a "$RUN/chain.log"
  PIDS=""
  for s in 0 1 2; do
    "$PY" -u scripts/MARL_e3_selector_train.py --train "$D/labels_train_*" --select "$D/labels_select" --dev "$D/labels_dev" \
        --out "$D/selectors" --name sel_nobid --seed $s --epochs $SEL_EPOCHS > "$D/sel_nobid_s$s.log" 2>&1 & PIDS="$PIDS $!"
    "$PY" -u scripts/MARL_e3_selector_train.py --train "$D/labels_train_*" --select "$D/labels_select" --dev "$D/labels_dev" \
        --out "$D/selectors" --name sel_bid --bid --seed $s --epochs $SEL_EPOCHS > "$D/sel_bid_s$s.log" 2>&1 & PIDS="$PIDS $!"
  done
  waitall $PIDS
  echo "== actor seed $S: closed loop $(date)" | tee -a "$RUN/chain.log"
  "$PY" -u scripts/MARL_e3_closed_loop.py --actor "$CK" --selectors "$D/selectors" --names sel_nobid sel_bid --policy direct --mp2 \
      --out "$D/cl_direct" --traffic-seeds $CL_SEEDS > "$D/cl_direct.log" 2>&1 & PIDS="$!"
  "$PY" -u scripts/MARL_e3_closed_loop.py --actor "$CK" --selectors "$D/selectors" --names sel_nobid sel_bid --policy R1 \
      --out "$D/cl_R1" --traffic-seeds $CL_SEEDS > "$D/cl_R1.log" 2>&1 & PIDS="$PIDS $!"
  waitall $PIDS
  for P in cl_direct cl_R1; do
    python3 scripts/MARL_hetero_closed_loop_report.py "$D/$P" --control sel_nobid > "$D/$P/full_endpoints.txt"
    "$PY" scripts/MARL_make_fig3_v4.py --run "$D/$P" --out "$D/figures" --stem "fig3_e3_s${S}_$P" \
        --title "E3 actor seed $S, $P (pilot panel)" >> "$D/figures.log" 2>&1
  done
  echo "== actor seed $S: done $(date)" | tee -a "$RUN/chain.log"
done
H1=$(shasum -a 256 "$PROTO" | cut -d' ' -f1)
[ "$H0" = "$H1" ] || { echo "PROTOCOL CHANGED DURING RUN" | tee -a "$RUN/chain.log"; exit 3; }
echo "CHAIN COMPLETE $(date)" | tee -a "$RUN/chain.log"
