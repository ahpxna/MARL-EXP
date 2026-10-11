#!/usr/bin/env bash
# MT-F (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010): SPaT forecasters for the grid lights t59-63 fitted on the FULL map (MT-E setting), then the
# interface-only test MTF_BGFar (grid lights x grid fleets, re-fitted forecast), days 0-4, 6 lanes, and the full-map report.
set -u; cd "$(dirname "$0")/.."
export MT_NET=midtown_full MT_BASE=actrest
R=research/city_sim/midtown_transfer_20261010/retrain/forecast_full_grid; E=research/city_sim/midtown_transfer_20261010/eval_full
scripts/RUN_mt_forecast.sh research/city_sim/w19_20261008/lights $R "59 60 61 62 63" 5 || { echo "forecasters failed"; exit 1; }
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3; PY=external_envs/city_runtime/bin/python; F3=research/city_sim/w15_20261007/fresh3/fleets
J=$E/jobs_bgfar.txt; : > $J
for k in 59 60 61 62 63; do for f in 1413 1513 1613 1713; do echo "MTF_BGFar_t${k}_s$f|$k|$f" >> $J; done; done
echo "MT-F tests start $(date): $(wc -l < $J) jobs"
cat $J | xargs -P 6 -S 8192 -I{} zsh -c 'IFS="|" read -r tag k f <<< "{}"; nice -n 5 '"$PY"' -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_eval_n4.py --n4 0.1:hyb:'"$R"'/prep/prov_rlh${k}_cl.json:'"$R"'/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:'"$F3"'/L11_s${f}_fleet.pt --seeds 0 1 2 3 4 --tag $tag --out '"$E"' > '"$E"'/$tag.log 2>&1 || echo "FAIL $tag"'
bad=0; while IFS='|' read -r tag _; do grep -q '"status": "COMPLETE"' $E/$tag.json 2>/dev/null || { echo "INCOMPLETE $tag"; bad=1; }; done < $J
MT_EVAL_DIR=$E MT_TAG_PREFIX=MTF $PY scripts/MT_report.py research/city_sim/midtown_transfer_20261010/report_mt_full.txt
echo "MT-F done $(date)"; exit $bad
