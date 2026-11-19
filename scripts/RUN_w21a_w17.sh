#!/usr/bin/env bash
# W21-A (PROTOCOL_CITY_WAVE21_20261015): the W20 pair R / SV in the W17 field-matched world (every car the W17-0 joint IDM, CITY_w17_world.py).
# Families AH (34-38, W19 trainer) and SRL / RDQ / RMP / RWV (84-103, W20 trainer), RL-H recipe, slot seeds, all trained in this world into
# $D/lights; W17 FRESH5 fleets s2213-s2513 (frozen); forecaster per light by the FRESH3 recipe in this world (development fleet L11_s13);
# fresh traffic 1420-1439.  Steps: training [KW21-T] -> KW20-1 -> forecasters (KF-3, KW20-P, KF-2) -> traffic -> gate rows -> R / SV rows
# (fuel-by-mode logger) -> world check (KW17-0 lines) -> CITY_w21_report.py a.  Copy of the W20 job (105_W20_BENCH.sh) with the world wrapper
# in front of every simulating command, AH trained anew, no TSI-G / PHEMlight5 arms.  LANES (default 6) parallel processes.
# SMOKE=1: slot 0, 15-episode smoke trainings, 300-s calibration, fleet s2213, seed 860, into W21A_DIR (default .../w21_20261015/smoke_a).
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
FAMS="AH SRL RDQ RMP RWV"; LANES=${LANES:-6}
if [ "${SMOKE:-0}" = 1 ]; then D=${W21A_DIR:-research/city_sim/w21_20261015/smoke_a}; else D=${W21A_DIR:-research/city_sim/w21_20261015/w17}; fi
mkdir -p $D/lights $D/traces $D/m2b $D/prep $D/cdata $D/cmodel $D/check $D/gate $D/conf
export XPLAY_TMP=$(cd $D/check && pwd) W7_FPR_DIR=$(cd $D && pwd) W20_LIGHTS=$(cd $D/lights && pwd) W19_LIGHTS=$(cd $D/lights && pwd)
G=research/city_sim/demand/grid4; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py
DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt; FD=research/city_sim/w17_20261008/fresh5/fleets
W17="$PY -u scripts/CITY_w17_world.py"; RUN="$W17 scripts/CITY_w20_run.py"; echo "W21-A start $(date); dir $D; lanes $LANES"
echo "sources: $(shasum -a 256 scripts/CITY_w17_world.py scripts/CITY_w20_bench.py scripts/CITY_w20_run.py scripts/CITY_w19_obs.py scripts/CITY_w19_run.py scripts/CITY_w19_train_light.py scripts/CITY_w20_train_light.py scripts/CITY_w19_prep.py scripts/CITY_eval_n4.py scripts/CITY_eval_f1.py scripts/CITY_w9_run.py scripts/CITY_w13_modes.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
k0() { case $1 in AH) echo 34;; SRL) echo 84;; RDQ) echo 89;; RMP) echo 94;; RWV) echo 99;; esac; }
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; SL="0"; FS="2213"; LEP=15; TS="0 1 2 3 4 5 6 7"; CS="860"; NF=1; export W7_PREP_N=1 W7_PREP_END=300
else SM=""; SL="0 1 2 3 4"; FS="2213 2313 2413 2513"; LEP=120; TS="0 1 2 3 4 5 6 7"; CS="$(seq -s ' ' 1420 1439)"; NF=8; fi
LT=""; FIRST=""; for f in $FAMS; do FIRST="$FIRST $(k0 $f)"; for j in $SL; do LT="$LT $(( $(k0 $f) + j ))"; done; done
echo "families $FAMS; lights$LT; fleets $FS; traffic $CS"
# 1. training in the field-matched world (AH: W19 trainer; SRL / RDQ / RMP / RWV: W20 trainer)
J=$D/train_jobs.txt; : > $J; for k in $LT; do echo $k >> $J; done
export PY D SM LEP W17 RUN TS DEV NF LANES
xargs -P $LANES -L 1 bash -c '[ -f $D/lights/RL-H_t$0.pt ] && exit 0; T=scripts/CITY_w20_train_light.py; [ $0 -lt 84 ] && T=scripts/CITY_w19_train_light.py
  nice -n 5 $W17 $T --out $D/lights --k $0 --episodes $LEP $SM > $D/lights/train_t$0.out 2>&1 || { echo "FAIL train $0"; exit 255; }' < $J || { echo "training failure: stop"; exit 1; }
$PY -c "
import sys, torch; sys.path.insert(0, '.'); import scripts.CITY_w20_bench as B; import scripts.CITY_w19_obs as W
for k in [int(x) for x in '$LT'.split()]:
    d = torch.load('$D/lights/RL-H_t%d.pt' % k, weights_only=False); f = W.fam_of(k)
    assert d['family'] == f and d['episodes'] == $LEP and d['dqn_seed'] == W.dqn_seed(k) and d['net'][0].in_features == W.DIM[W.FAMS[f][1]], (k, d['family'])
print('KW21-T PASS: families, episodes, seeds, input dims')" || { echo "KW21-T FAIL: stop"; exit 1; }
for k in $LT; do grep -q "KW17-0: type v_passenger tau" $D/lights/train_t$k.out || { echo "KW21-T FAIL: no KW17-0 line in train_t$k.out"; exit 1; }; done
echo "KW21-T PASS: the field-matched world was in force in every training (KW17-0)"; echo "training done $(date)"
# 2. KW20-1: the W20 families' observation equals an independent recomputation, in this world (first light of each W20 family)
for K1 in $FIRST; do [ $K1 -lt 84 ] && continue
  $RUN scripts/CITY_w20_check.py obs $K1 > $D/check/kw20_obs_t$K1.txt 2>&1; grep KW20 $D/check/kw20_obs_t$K1.txt | cut -c1-300
  grep -q "^PASS" $D/check/kw20_obs_t$K1.txt || { echo "KW20-1 FAIL t$K1: stop"; exit 1; }; done
# 3. forecasters (FRESH3 recipe, in this world)
J=$D/trace_jobs.txt; : > $J; for k in $LT; do echo $k >> $J; done
xargs -P $LANES -L 1 bash -c '[ -f $D/traces/fit_RLH$0.json ] || nice -n 5 $RUN scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$0 --fleet L-ACT:0 --guard always --seeds $TS $SM --record $D/traces/rlh$0_s{seed}.npz --tag fit_RLH$0 --out $D/traces >> $D/traces/run.log 2>&1 || { echo "FAIL trace $0"; exit 255; }' < $J || { echo "trace failure: stop"; exit 1; }
for k in $LT; do F=""; for s in $TS; do F="$F $D/traces/rlh${k}_s$s.npz"; done; [ -f $D/m2b/forecast_rlh$k.json ] || $RUN scripts/CITY_spat_forecast.py fit $k $D/m2b/forecast_rlh$k.json $F > $D/m2b/fit_t$k.log 2>&1 || { echo "open-loop fit FAIL t$k"; tail -3 $D/m2b/fit_t$k.log; exit 1; }; done
DEG=$($PY -c "
import json, sys; sys.path.insert(0, '.'); import scripts.CITY_w20_bench as B; import scripts.CITY_w19_obs as W
bad = sorted({W.fam_of(k) for k in [int(x) for x in '$LT'.split()] if len(json.load(open('$D/m2b/forecast_rlh%d.json' % k))['pooled']) < 2}); print(' '.join(bad))")
if [ -n "$DEG" ]; then echo "DEGENERATE (excluded with every light of the family; registered rule): $DEG"; F2=""; for f in $FAMS; do case " $DEG " in *" $f "*) ;; *) F2="$F2 $f";; esac; done; FAMS=$F2
  LT=""; FIRST=""; for f in $FAMS; do FIRST="$FIRST $(k0 $f)"; for j in $SL; do LT="$LT $(( $(k0 $f) + j ))"; done; done
  J=$D/trace_jobs.txt; : > $J; for k in $LT; do echo $k >> $J; done; echo "families kept: $FAMS"; fi
export W21_FAMS="$FAMS"
xargs -P $LANES -L 1 bash -c '[ -f $D/prep/prov_rlh$0_cl.json ] || nice -n 5 $RUN scripts/CITY_w19_prep.py $0 $D/prep > $D/prep/prep_k$0.out 2>&1 || { echo "FAIL prep $0"; exit 255; }' < $J || { echo "prep failure: stop"; exit 1; }
for k in $LT; do $PY -c "
import json; T = json.load(open('$D/prep/prov_rlh${k}_cl.json')); assert len(T['per']) == 16 and T['n_files'] == $NF, (len(T['per']), T['n_files']); print('KF-3 t$k ok')" || { echo "KF-3 FAIL t$k"; exit 1; }; done
$PY -c "
import sys, numpy as np, torch; sys.path.insert(0, '.'); import scripts.CITY_m3_core as M; import scripts.CITY_w20_bench as B; import scripts.CITY_w19_obs as W
for k in [int(x) for x in '$LT'.split()]:
    f = W.fam_of(k); assert ('W19 prep family in force %s obs %s' % (f, W.FAMS[f][1])) in open('$D/prep/prep_k%d.out' % k).read(), ('family not in force', k)
    assert 'KW17-0: type v_passenger tau' in open('$D/prep/prep_k%d.out' % k).read(), ('world not in force in prep', k)
    net = torch.load('$D/lights/RL-H_t%d.pt' % k, weights_only=False)['net']; w = M.widen(net); din = net[0].in_features
    rng = np.random.default_rng(k); O = rng.uniform(0, 3, (100000, din)).astype(np.float32); F = rng.uniform(0, 3, (100000, 5)).astype(np.float32)
    with torch.no_grad():
        a = net(torch.as_tensor(O)).argmax(1); b = w(torch.as_tensor(np.concatenate([O, F], 1))).argmax(1)
    assert int((a != b).sum()) == 0, (k, int((a != b).sum()))
print('KW20-P PASS: family and world in force in every prep; widened = family net on 100000 inputs per light')" || { echo "KW20-P FAIL: stop"; exit 1; }
J=$D/collect_jobs.txt; : > $J; for k in $LT; do for s in $TS; do echo "$k $s" >> $J; done; done
xargs -P $LANES -L 1 bash -c '[ -f $D/cdata/c2_t$0/feat_s$1.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $D/cdata/c2_t$0 --spat-arm fc2:0.1:$D/prep/prov_rlh$0_cl.json --light RL-H:$0 --fleet PL:$DEV --seeds $1 $SM --tag C_t$0_s$1 --out $D/cdata/c2_t$0 >> $D/cdata/run.log 2>&1 || { echo "FAIL collect $0 $1"; exit 255; }' < $J || { echo "collection failure: stop"; exit 1; }
for k in $LT; do [ -f $D/cmodel/n2_k$k.pt ] || $PY -u scripts/CITY_n2_fit.py $k $D/cdata/c2_t$k $D/cmodel > $D/cmodel/fit_t$k.log 2>&1 || { echo "FIT FAIL t$k"; exit 1; }; done
F1=$(echo $FS | cut -d' ' -f1)
for K1 in $FIRST; do K=$D/check/kf2_t$K1; mkdir -p $K
  $RUN scripts/CITY_eval_n2.py --n2 0.5:$D/cmodel/n2_k$K1.pt --featlog $K --light RL-H:$K1 --fleet PL:$FD/L11_s${F1}_fleet.pt --seeds 0 --smoke --tag KF2_n2 --out $K > $K/run.log 2>&1 || { echo "KF-2 run FAIL t$K1"; exit 1; }
  $PY scripts/CITY_n2_parity.py $K 0 $D/cmodel/n2_k$K1.pt | tee $D/check/kf2_t$K1.txt || { echo "KF-2 FAIL t$K1: stop"; exit 1; }; done
echo "forecasters done $(date)"
# 4. fresh traffic 1420-1439 (non-existence check; W17's randomTrips command); the wrapper writes the W17 copies on first use
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF1420_generated ]; then
  for s in $CS; do [ -f $G/rou_s$s.xml ] && { echo "KW21-2 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $CS; do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF1420_generated; echo "traffic 1420-1439 generated $(date)"; fi
# 5. rows (every command through the world wrapper; W9 runner in identity mode, as W20)
run_jobs() { export OUT=$2 SS="$3" CH="$4"
  xargs -P $LANES -L 1 bash -c 'T=$0; M=$1; shift; [ -f $OUT/$T.json ] || nice -n 5 $W17 scripts/CITY_w9_run.py $M scripts/CITY_w20_run.py $CH "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
J=$D/gate_jobs.txt; : > $J; echo "OFF_t0_h none scripts/CITY_eval6_v11.py --light FT --fleet L-ACT:0 --guard always" >> $J
for k in $LT; do echo "GATE_t${k}_h none scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always" >> $J; done
run_jobs $J $D/gate "$CS" "" || { echo "gate rows failure: stop"; exit 1; }; echo "gate rows done $(date)"
N4() { echo "--n4 0.1:hyb:$D/prep/prov_rlh$1_cl.json:$D/cmodel/n2_k$1.pt"; }
J=$D/conf_jobs.txt; : > $J
for k in $LT; do for s in $FS; do F="--light RL-H:$k --fleet PL:$FD/L11_s${s}_fleet.pt"
  echo "R_t${k}_s$s none scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
  echo "SV_t${k}_s$s none scripts/CITY_eval_n4.py $(N4 $k) $F" >> $J; done; done
echo "conf rows: $(wc -l < $J) jobs x $(echo $CS | wc -w) seeds"
run_jobs $J $D/conf "$CS" "scripts/CITY_w13_modes.py" || { echo "confirmation failure: stop"; exit 1; }
for x in gate conf; do n=$(grep -c "KW17-0: type v_passenger tau" $D/$x/run.log); j=$(wc -l < $D/${x}_jobs.txt); echo "KW17-0 lines in $x: $n (jobs $j)"
  grep -q "KW17-0 FAIL" $D/$x/run.log && { echo "KW17-0 FAIL in $x rows: stop"; exit 1; }; [ "$n" -ge "$j" ] || { echo "KW17-0 lines fewer than jobs in $x: stop"; exit 1; }; done
W21_SMOKE=${SMOKE:-0} W21_FAMS="$FAMS" $PY scripts/CITY_w21_report.py a $D || { echo "report FAIL"; exit 1; }
echo "W21-A done $(date)"
