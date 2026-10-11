#!/usr/bin/env bash
# TSI KT-1 (PROTOCOL_CITY_TSI_20261005 checks; requested by the user's review TSI_N3_REVIEW_20261005 §3): offline / runtime parity of the
# per-light forecaster on TRAIN seed 0 for lights t4 and t8 (KN2-1 / KN2-2 style), plus gate 'all' == N2 rows (KN4-1 style) on the same run.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/tsi_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; TB=research/city_sim/f1b_20261004/prep; RUN="$PY -u scripts/CITY_f1a1_run.py"; OUT=$D/check/kt1_report.txt; : > $OUT; ok=1
for t in 4 8; do K=$D/check/kt1_t$t; mkdir -p $K; M=$D/cmodel/c2/n2_k$t.pt
  $RUN scripts/CITY_eval_n2.py --n2 0.5:$M --featlog $K --light RL-H:$t --fleet PL:$P/L11_s213_fleet.pt --seeds 0 --smoke --tag KT1_n2 --out $K > $K/run.log 2>&1 || { echo "t$t n2 run FAIL" >> $OUT; ok=0; continue; }
  $PY scripts/CITY_n2_parity.py $K 0 $M >> $OUT 2>&1 || ok=0
  $RUN scripts/CITY_eval_n4.py --n4 0.5:all:$M --light RL-H:$t --fleet PL:$P/L11_s213_fleet.pt --seeds 0 --smoke --tag KT1_n4 --out $K >> $K/run.log 2>&1 || { echo "t$t n4 run FAIL" >> $OUT; ok=0; continue; }
  $PY -c "
import sys; sys.path.insert(0,'.')
from scripts.CITY_spatp_report import rows
C=rows('$K'); Q=('timeloss','timeloss_agent','timeloss_human','fuel_agent','fuel','teleports'); e=all(C['KT1_n4'][0][q]==C['KT1_n2'][0][q] for q in Q)
print('t$t KN4-1-style gate all == N2 rows:', e); raise SystemExit(0 if e else 1)" >> $OUT 2>&1 || ok=0; done
echo "KT-1 OVERALL: $([ $ok = 1 ] && echo PASS || echo FAIL)" >> $OUT; cat $OUT
