#!/usr/bin/env bash
cd /Users/phanan/cig-amf-main; D=research/city_sim/f1_20261004
i=0; while [ $i -lt 120 ] && [ ! -f $D/prov/locked.json ]; do sleep 15; i=$((i+1)); done
[ -f $D/prov/locked.json ] || { echo "no locked provider"; exit 1; }
cat $D/report_f1_provider.txt
/usr/bin/env PYTHONHASHSEED=0 OMP_NUM_THREADS=1 python3 -u scripts/RUN_f1_train_dev.py && /usr/bin/env PYTHONHASHSEED=0 OMP_NUM_THREADS=1 python3 -u scripts/RUN_f1_eval_dev.py
echo "chain done $(date)"
