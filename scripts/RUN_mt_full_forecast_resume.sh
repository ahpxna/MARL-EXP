#!/usr/bin/env bash
# MT-F resume (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010, MT-F; 11/10/2026).  The first MT-F run (scripts/RUN_mt_full_forecast.sh) finished
# every upstream step (traces, open-loop table, closed-loop prep, 8 collection logs) for t59-t63, but all five N2 fits were SIGKILLed: the
# original CITY_n2_fit.py stores a 511-wide light one-hot per row (about 54 GB of training features on the full map; 80 GB peak measured).
# This resume fits the five forecasters with scripts/CITY_n2_fit_lowmem.py (same model, rows, features, seeds and checkpoint format; the
# one-hot product becomes a column lookup), ONE AT A TIME, then runs the unchanged interface-only test MTF_BGFar and the report.
# Gate: the KMT7 equivalence check (lowmem vs original on the grid W19 data) must say PASS.  Nothing is deleted or overwritten: the killed
# fits' logs stay in cmodel/fit_t<k>.log; the new logs are cmodel/fit_lowmem_t<k>.log.
set -u; cd "$(dirname "$0")/.."
export MT_NET=midtown_full MT_BASE=actrest PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3
R=research/city_sim/midtown_transfer_20261010/retrain/forecast_full_grid; E=research/city_sim/midtown_transfer_20261010/eval_full
PY=external_envs/city_runtime/bin/python; F3=research/city_sim/w15_20261007/fresh3/fleets
export W19_LIGHTS=$(cd research/city_sim/w19_20261008/lights && pwd) XPLAY_TMP=$(cd $R/check && pwd) W7_FPR_DIR=$(cd $R && pwd)
echo "MT-F resume start $(date)"
if pgrep -f "scripts/RUN_mt_full_forecast.sh" > /dev/null; then echo "the first MT-F run is still running: launch this after it exits"; exit 2; fi
grep -q '"PASS": true' $R/diag_fitkill/kmt7/KMT7.json 2>/dev/null || { echo "KMT7 has not passed: stop"; exit 1; }
for k in 59 60 61 62 63; do
  for f in traces/fit_RLH$k.json m2b/forecast_rlh$k.json prep/prov_rlh${k}_cl.json; do [ -f $R/$f ] || { echo "MISSING $R/$f"; exit 1; }; done
  for i in 0 1 2 3 4 5 6 7; do [ -e $R/cdata/c2_t${k}_fit/feat_s$i.npz ] || { echo "MISSING $R/cdata/c2_t${k}_fit/feat_s$i.npz"; exit 1; }; done
done
for k in 59 60 61 62 63; do
  [ -f $R/cmodel/n2_k$k.pt ] && continue
  echo "fit t$k start $(date)"
  nice -n 5 $PY -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_n2_fit_lowmem.py $k $R/cdata/c2_t${k}_fit $R/cmodel \
      > $R/cmodel/fit_lowmem_t$k.log 2>&1 || { echo "FAIL lowmem fit t$k"; tail -5 $R/cmodel/fit_lowmem_t$k.log; exit 1; }
  grep -h "rows train\|self-check\|saved" $R/cmodel/fit_lowmem_t$k.log
done
J=$E/jobs_bgfar.txt; : > $J
for k in 59 60 61 62 63; do for f in 1413 1513 1613 1713; do echo "MTF_BGFar_t${k}_s$f|$k|$f" >> $J; done; done
echo "MT-F tests start $(date): $(wc -l < $J) jobs"
cat $J | xargs -P 6 -S 8192 -I{} zsh -c 'IFS="|" read -r tag k f <<< "{}"; nice -n 5 '"$PY"' -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_eval_n4.py --n4 0.1:hyb:'"$R"'/prep/prov_rlh${k}_cl.json:'"$R"'/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:'"$F3"'/L11_s${f}_fleet.pt --seeds 0 1 2 3 4 --tag $tag --out '"$E"' > '"$E"'/$tag.log 2>&1 || echo "FAIL $tag"'
bad=0; while IFS='|' read -r tag _; do grep -q '"status": "COMPLETE"' $E/$tag.json 2>/dev/null || { echo "INCOMPLETE $tag"; bad=1; }; done < $J
MT_EVAL_DIR=$E MT_TAG_PREFIX=MTF $PY scripts/MT_report.py research/city_sim/midtown_transfer_20261010/report_mt_full.txt
echo "MT-F resume done $(date)"; exit $bad
