#!/usr/bin/env bash
# W21-D (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-D): the W21-C SERVEg arm with the median published (q 0.5) instead of the 0.1 quantile;
# same lights (AH t34-38, B2D t59-63), fleet s1413, days 0-4, MT-E setting, served-answer logs and traces into the W21-C directory; then
# CITY_w21d_report.py.  LANES (default 6).
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=actrest MT_NET=midtown_full
PY=external_envs/city_runtime/bin/python; W19=research/city_sim/w19_20261008; FL=research/city_sim/w15_20261007/fresh3/fleets/L11_s1413_fleet.pt
E=research/city_sim/w21_20261015/midtown_diag; LANES=${LANES:-6}; export W10_LOG=$(cd $E/served && pwd) PY E
export M="$PY -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py"; echo "W21-D start $(date)"
J=$E/jobs_d.txt; : > $J
for k in 34 35 36 37 38 59 60 61 62 63; do echo "SERVEg50_t$k scripts/CITY_w10_run.py serve scripts/CITY_eval_n4.py --n4 0.5:hyb:$W19/prep/prov_rlh${k}_cl.json:$W19/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:$FL --record $E/rec/SERVEg50_t$k/phases_s{seed}.npz" >> $J; done
xargs -P $LANES -L 1 bash -c 'T=$0; S=$1; shift; grep -qs "\"status\": \"COMPLETE\"" $E/$T.json && exit 0; mkdir -p $E/rec/$T
  nice -n 5 $M $S "$@" --seeds 0 1 2 3 4 --tag $T --out $E > $E/$T.log 2>&1 || echo "FAIL $T"' < $J
$PY scripts/CITY_w21d_report.py $E || { echo "report FAIL"; exit 1; }
echo "W21-D done $(date)"
