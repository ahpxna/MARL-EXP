#!/usr/bin/env bash
# N8 (PROTOCOL_CITY_N8_CDC_20261005): smoke + KN8-1 -> CEM m3 -> CEM city -> DEV 12 jobs (4 parallel) -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/n8_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; echo "N8 start $(date)"
$PY -u scripts/CITY_eval_n8.py --spat program --light CDC:20,1,-0.5,-0.5 --fleet PL:$P/L11_s13_fleet.pt --seeds 0 --smoke --tag SMK --out $D/check > $D/check/smoke.log 2>&1 || { echo "SMOKE FAIL"; tail -8 $D/check/smoke.log; exit 1; }
$PY -c "
import json; x=json.load(open('$D/check/SMK_n8.json')); print('KN8-1 smoke:', x['mism'], 'mismatches /', x['checked'], 'checked; greens', x['n_greens'], 'mean', x['dur_mean'])
raise SystemExit(0 if (x['checked'] > 50 and x['mism'] == 0) else 1)" || { echo "KN8-1 FAIL: stop"; exit 1; }
for v in m3 city; do [ -f $D/cem/$v/cem_$v.json ] || $PY -u scripts/CITY_n8_cem.py $v $D/cem/$v || { echo "CEM $v FAIL"; exit 1; }; done; echo "cem done $(date)"
TM=$($PY -c "import json;print(','.join(f'{v:.4f}' for v in json.load(open('$D/cem/m3/cem_m3.json'))['mean']))"); TC=$($PY -c "import json;print(','.join(f'{v:.4f}' for v in json.load(open('$D/cem/city/cem_city.json'))['mean']))")
echo "theta m3 $TM | theta city $TC"
J=$D/jobs.txt; : > $J
for fl in s13 s113; do F="--fleet PL:$P/L11_${fl}_fleet.pt"
  echo "CDCm3_${fl} --spat program --light CDC:$TM $F" >> $J; echo "CDCm3sig_${fl} --spat none --light CDC:$TM $F" >> $J
  echo "CDCcity_${fl} --spat program --light CDC:$TC $F" >> $J; echo "CDCcitysig_${fl} --spat none --light CDC:$TC $F" >> $J
  echo "FTp_${fl} --spat program --light FT $F" >> $J; echo "FTsig_${fl} --spat none --light FT $F" >> $J; done
export PY D; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/dev/$T.json ] || nice -n 5 $PY -u scripts/CITY_eval_n8.py "$@" --seeds 600 601 602 603 604 605 606 607 608 609 610 611 --tag $T --out $D/dev >> $D/dev/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; $PY scripts/CITY_n8_report.py; echo "N8 done $(date)"
