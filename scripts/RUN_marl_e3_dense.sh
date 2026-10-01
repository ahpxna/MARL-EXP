#!/usr/bin/env bash
# PROTOCOL_E3_ABLATION Amendment 1: dense continuation labels (t = 4..22, every step) for one actor, then the same
# four-variant ablation.  Layout: <actor dir>/dense/{ckpt_best.pt -> ../ckpt_best.pt, labels_train_k, labels_select,
# labels_dev}, so RUN_marl_e3_ablation.sh runs on it unchanged.  All label jobs under the watchdog.
# Usage: bash scripts/RUN_marl_e3_dense.sh <actor dir> [nshards]
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$ROOT"
export CIG_EXTERNAL_RUNTIME_ACTIVE=1 PYTHONDONTWRITEBYTECODE=1
PY=external_envs/runtime/bin/python; WD="$PY scripts/run_with_watchdog.py"
A="${1:?actor dir}"; N="${2:-6}"; D="$A/dense"; mkdir -p "$D"; [ -e "$D/ckpt_best.pt" ] || ln -s ../ckpt_best.pt "$D/ckpt_best.pt"
CK="$A/ckpt_best.pt"; SN="$(seq -s ' ' 4 22)"; PIDS=""
for k in $(seq 0 $((N - 1))); do
  L="$D/labels_train_$k"; [ -f "$L/manifest.json" ] || { $WD --log "$L.log" --stall 1800 -- "$PY" -u scripts/MARL_e3_continuation_labels_v3.py \
      --ckpt "$CK" --out "$L" --split train --snaps $SN --limit 0 --shard $k --nshards $N & PIDS="$PIDS $!"; }
done
for sp in select dev; do
  L="$D/labels_$sp"; [ -f "$L/manifest.json" ] || { $WD --log "$L.log" --stall 1800 -- "$PY" -u scripts/MARL_e3_continuation_labels_v3.py \
      --ckpt "$CK" --out "$L" --split $sp --snaps $SN --limit 0 & PIDS="$PIDS $!"; }
done
rc=0; for p in $PIDS; do wait $p || rc=$?; done; [ $rc = 0 ] || { echo "a label job failed ($rc)"; exit $rc; }
bash scripts/RUN_marl_e3_ablation.sh "$D"
echo "dense ablation done $D $(date)"
