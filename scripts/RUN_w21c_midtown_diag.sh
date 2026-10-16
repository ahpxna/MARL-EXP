#!/usr/bin/env bash
# W21-C (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-C): where the Midtown time cost of the forecast comes from.  MT-E setting (as W21-B),
# fleet s1413, days 0-4, the W10 tooling unchanged under DEMO_midtown.py:
#   C0  KW21-C0: FT + the fleet's own program SPaT (plain logging, 600-s smoke, day 0) -> matcher exactness offsets
#   C1  SERVEg / SHADOWg (grid forecaster; AH t34-38, B2D t59-63), SERVEr / SHADOWr (forecaster refit on the full map; B2D t60-63), with
#       served-answer logs (W10_LOG) and phase traces (--record)
#   C3  SIG (sigma* replay) and ORC (exact future timing, CITY_m3_headroom) on each light's SHADOWg schedule; KH-1 (SIG = SHADOWg) on the first
#       light-day decides whether C3 runs
# then CITY_w21c_report.py.  A failed cell does not stop the others; the report refuses incomplete panels.  LANES (default 6).
# SMOKE=1: AH t34 and B2D t60 only, day 0, --smoke, into W21C_DIR (default .../w21_20261015/smoke_c).
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=actrest MT_NET=midtown_full
PY=external_envs/city_runtime/bin/python; W19=research/city_sim/w19_20261008; F3=research/city_sim/w15_20261007/fresh3/fleets
RF=research/city_sim/midtown_transfer_20261010/retrain/forecast_full_grid; LANES=${LANES:-6}; FL=$F3/L11_s1413_fleet.pt
if [ "${SMOKE:-0}" = 1 ]; then E=${W21C_DIR:-research/city_sim/w21_20261015/smoke_c}; LA="34"; LB="60"; LR="60"; DAYS="0"; SM="--smoke"
else E=${W21C_DIR:-research/city_sim/w21_20261015/midtown_diag}; LA="34 35 36 37 38"; LB="59 60 61 62 63"; LR="60 61 62 63"; DAYS="0 1 2 3 4"; SM=""; fi
mkdir -p $E/served $E/rec; export W10_LOG=$(cd $E/served && pwd)
M="$PY -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py"; echo "W21-C start $(date); dir $E; lanes $LANES"
echo "sources: $(shasum -a 256 scripts/DEMO_midtown.py scripts/CITY_w10_run.py scripts/CITY_w10_diag.py scripts/CITY_eval_n4.py scripts/CITY_eval_f1.py scripts/CITY_m3_headroom.py scripts/CITY_eval4.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
N4G() { echo "--n4 0.1:hyb:$W19/prep/prov_rlh$1_cl.json:$W19/cmodel/n2_k$1.pt"; }
N4R() { echo "--n4 0.1:hyb:$RF/prep/prov_rlh$1_cl.json:$RF/cmodel/n2_k$1.pt"; }
export PY E SM DAYS M
run() { xargs -P $LANES -L 1 bash -c 'T=$0; S=$1; shift; grep -qs "\"status\": \"COMPLETE\"" $E/$T.json && exit 0; mkdir -p $E/rec/$T
  nice -n 5 $M $S "$@" --seeds ${SEEDS:-$DAYS} $SM --tag $T --out $E > $E/$T.log 2>&1 || echo "FAIL $T"' < $1
  bad=0; while read -r T _; do grep -qs '"status": "COMPLETE"' $E/$T.json || { echo "INCOMPLETE $T"; bad=1; }; done < $1; return $bad; }
# C0 exactness under FT (600-s smoke run, day 0)
J=$E/jobs_c0.txt; echo "FTX scripts/CITY_w10_run.py plain scripts/CITY_eval6_v11.py --light FT --fleet PL:$FL --record $E/rec/FTX/phases_s{seed}.npz" > $J
SM0=$SM; export SEEDS=0 SM=--smoke; run $J || echo "C0 incomplete"; export SM=$SM0; unset SEEDS
# C1 served-answer accounting
J=$E/jobs_c1.txt; : > $J
for k in $LA $LB; do F="--light RL-H:$k --fleet PL:$FL"
  for md in serve shadow; do U=$(echo $md | tr a-z A-Z); echo "${U}g_t$k scripts/CITY_w10_run.py $md scripts/CITY_eval_n4.py $(N4G $k) $F --record $E/rec/${U}g_t$k/phases_s{seed}.npz" >> $J; done; done
for k in $LR; do F="--light RL-H:$k --fleet PL:$FL"
  for md in serve shadow; do U=$(echo $md | tr a-z A-Z); echo "${U}r_t$k scripts/CITY_w10_run.py $md scripts/CITY_eval_n4.py $(N4R $k) $F --record $E/rec/${U}r_t$k/phases_s{seed}.npz" >> $J; done; done
echo "C1: $(wc -l < $J) jobs x $(echo $DAYS | wc -w) days"; run $J || echo "C1 incomplete (listed above)"; echo "C1 done $(date)"
# C3 oracle on the fixed schedule: KH-1 first
K1=$(echo $LA | cut -d' ' -f1); J=$E/jobs_kh1.txt
echo "SIG_t$K1 scripts/CITY_eval_f1.py --spat-arm none --light RL-H:$K1 --fleet PL:$FL --replay-dir $E/rec/SHADOWg_t$K1" > $J; run $J
KH=$($PY - "$E" "$K1" <<'PY'
import json, sys
E, k = sys.argv[1], sys.argv[2]
try:
    a = {r['seed']: r for r in json.load(open(f'{E}/SIG_t{k}.json'))['rows']}; b = {r['seed']: r for r in json.load(open(f'{E}/SHADOWg_t{k}.json'))['rows']}
except FileNotFoundError:
    print('MISSING'); sys.exit()
F = ('timeloss', 'timeloss_agent', 'timeloss_human', 'fuel_agent', 'teleports', 'unfinished')
bad = [(s, f) for s in b for f in F if a[s][f] != b[s][f]]
print('PASS' if not bad else 'FAIL ' + str(bad[:6]))
PY
); echo "KH-1 (SIG replay of the SHADOWg schedule reproduces SHADOWg, t$K1): $KH" | tee $E/kh1.txt
if [ "${KH%% *}" = PASS ]; then J=$E/jobs_c3.txt; : > $J
  for k in $LA $LB; do F="--light RL-H:$k --fleet PL:$FL --replay-dir $E/rec/SHADOWg_t$k"
    [ $k = $K1 ] || echo "SIG_t$k scripts/CITY_eval_f1.py --spat-arm none $F" >> $J; echo "ORC_t$k scripts/CITY_m3_headroom.py $F" >> $J; done
  echo "C3: $(wc -l < $J) jobs"; run $J || echo "C3 incomplete (listed above)"; echo "C3 done $(date)"
else echo "C3 skipped: KH-1 not passed (registered)"; fi
W21_SMOKE=${SMOKE:-0} $PY scripts/CITY_w21c_report.py $E "$LA" "$LB" "$LR" || { echo "report FAIL"; exit 1; }
echo "W21-C done $(date)"
