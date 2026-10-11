#!/usr/bin/env bash
# W19 stage 3 (PROTOCOL_CITY_WAVE19_20261008): the SCALE constants (S05, S2 observation denominators; R1, R100 reward divisor); traffic 1400-1409; runs after 104b.
# Families S05 (h/5, n/10, tau/30), S2 (h/20, n/40, tau/120), R1 (reward -H/1), R100 (reward -H/100); AH rows come from 104a.
# Main world (grid4, Krauss).  5 lights per family (shared DQN seeds by slot), 120 episodes, the RL-H recipe (KW19-0: bit-identical to
# CITY_q7b_contract for AH).  Per light: the FRESH3 forecaster recipe (traces -> open-loop -> closed-loop c2 [KF-3, KW19-2] -> N2 logs ->
# fit [KF-2]).  Fleets: FRESH3 R10 s1413-s1713 (frozen, trained under FT).  Fresh traffic 1400-1419 (non-existence check).
# Rows: OFF / GATE (all SUMO drivers, H4) and R / SV (forecast q0.1, no adapter) / TG (forecast + adapter 1, 0.25; not B2) x HBEFA4 /
# PHEMlight5.  Report: CITY_w19_report.py 3.   SMOKE=1: slot 0 only, 3-episode smoke trainings, fleet s1413, seed 860, into W19_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
STAGE=3; FAMS="S05 S2 R1 R100"; NS=10
D=${W19_DIR:-research/city_sim/w19_20261008}; mkdir -p $D/lights $D/traces $D/m2b $D/prep $D/cdata $D/cmodel $D/check $D/gate $D/conf
export XPLAY_TMP=$(cd $D/check && pwd) W7_FPR_DIR=$(cd $D && pwd) W19_LIGHTS=$(cd $D/lights && pwd); G=research/city_sim/demand/grid4
RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt
FD=research/city_sim/w15_20261007/fresh3/fleets; RUN="$PY -u scripts/CITY_w19_run.py"; P5=em:PHEMlight5/PC_EU4_G; echo "W19-S$STAGE start $(date)"
k0() { case $1 in AH) echo 34;; B1H) echo 39;; B2H) echo 44;; AD) echo 49;; B1D) echo 54;; B2D) echo 59;; S05) echo 64;; S2) echo 69;; R1) echo 74;; R100) echo 79;; esac; }
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; SL="0"; FS="1413"; LEP=3; TS="0 1 2 3 4 5 6 7"; CS="860"; NF=1; export W7_PREP_N=1 W7_PREP_END=300
else SM=""; SL="0 1 2 3 4"; FS="1413 1513 1613 1713"; LEP=120; TS="0 1 2 3 4 5 6 7"; CS="$(seq -s ' ' 1400 $((1399 + NS)))"; NF=8; fi
LT=""; FIRST=""; for f in $FAMS; do FIRST="$FIRST $(k0 $f)"; for j in $SL; do LT="$LT $(( $(k0 $f) + j ))"; done; done; echo "families $FAMS lights$LT"
# 0. KW19-0: the W19 trainer (AH, DQN seed of t19) reproduces CITY_q7b_contract's RL-H t19 (3 smoke episodes) bit for bit
K0=$D/check/kw19_0; mkdir -p $K0/a $K0/b
[ -f $K0/a/REF.pt ] || $PY -u scripts/CITY_q7b_contract.py --out $K0/a --train-light REF --t 19 --episodes 3 --smoke > $K0/a.log 2>&1
[ -f $K0/b/NEW.pt ] || $PY -u scripts/CITY_w19_train_light.py --out $K0/b --k 34 --dqn-t 19 --name NEW --episodes 3 --smoke > $K0/b.log 2>&1
$PY -c "
import torch
a=torch.load('$K0/a/REF.pt',weights_only=False)['net'].state_dict(); b=torch.load('$K0/b/NEW.pt',weights_only=False)['net'].state_dict()
assert all(torch.equal(a[k],b[k]) for k in a); print('KW19-0 PASS')" || { echo "KW19-0 FAIL: stop"; exit 1; }
# 1. training (xargs -P 10)
J=$D/train_jobs_s$STAGE.txt; : > $J; for k in $LT; do echo $k >> $J; done
export PY D SM LEP RUN TS DEV NF; xargs -P 10 -L 1 bash -c '[ -f $D/lights/RL-H_t$0.pt ] || nice -n 5 $PY -u scripts/CITY_w19_train_light.py --out $D/lights --k $0 --episodes $LEP $SM > $D/lights/train_t$0.out 2>&1 || { echo "FAIL train $0"; exit 255; }' < $J || { echo "training failure: stop"; exit 1; }
$PY -c "
import sys, torch; sys.path.insert(0, '.'); import scripts.CITY_w19_obs as W
for k in [int(x) for x in '$LT'.split()]:
    d = torch.load('$D/lights/RL-H_t%d.pt' % k, weights_only=False); f = W.fam_of(k)
    assert d['family'] == f and d['episodes'] == $LEP and d['dqn_seed'] == W.dqn_seed(k) and d['net'][0].in_features == W.DIM[W.FAMS[f][1]], (k, d['family'], d['episodes'])
print('KW19-1 PASS: families, episodes, seeds, input dims')" || { echo "KW19-1 FAIL: stop"; exit 1; }; echo "training done $(date)"
for K1 in $FIRST; do $RUN scripts/CITY_w19_check_obs.py $K1 > $D/check/kw19_4_t$K1.txt 2>&1; grep "KW19-4 k" $D/check/kw19_4_t$K1.txt; grep -q "^KW19-4 PASS" $D/check/kw19_4_t$K1.txt || { echo "KW19-4 FAIL t$K1: stop"; tail -3 $D/check/kw19_4_t$K1.txt; exit 1; }; done
# 2. traces and open-loop tables
J=$D/trace_jobs_s$STAGE.txt; : > $J; for k in $LT; do echo $k >> $J; done
xargs -P 9 -L 1 bash -c '[ -f $D/traces/fit_RLH$0.json ] || nice -n 5 $RUN scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$0 --fleet L-ACT:0 --guard always --seeds $TS $SM --record $D/traces/rlh$0_s{seed}.npz --tag fit_RLH$0 --out $D/traces >> $D/traces/run.log 2>&1 || { echo "FAIL trace $0"; exit 255; }' < $J || { echo "trace failure: stop"; exit 1; }
for k in $LT; do F=""; for s in $TS; do F="$F $D/traces/rlh${k}_s$s.npz"; done; [ -f $D/m2b/forecast_rlh$k.json ] || $RUN scripts/CITY_spat_forecast.py fit $k $D/m2b/forecast_rlh$k.json $F > $D/m2b/fit_t$k.log 2>&1 || { echo "open-loop fit FAIL t$k"; tail -3 $D/m2b/fit_t$k.log; exit 1; }; done
# 3. closed-loop c2 prep + KF-3 + KW19-2 (family in force; widened net = family net on 100 000 random inputs)
xargs -P 9 -L 1 bash -c '[ -f $D/prep/prov_rlh$0_cl.json ] || nice -n 5 $RUN scripts/CITY_w19_prep.py $0 $D/prep > $D/prep/prep_k$0.out 2>&1 || { echo "FAIL prep $0"; exit 255; }' < $J || { echo "prep failure: stop"; exit 1; }
for k in $LT; do $PY -c "
import json; T = json.load(open('$D/prep/prov_rlh${k}_cl.json')); assert len(T['per']) == 16 and T['n_files'] == $NF, (len(T['per']), T['n_files']); print('KF-3 t$k ok')" || { echo "KF-3 FAIL t$k"; exit 1; }; done
$PY -c "
import sys, numpy as np, torch; sys.path.insert(0, '.'); import scripts.CITY_m3_core as M; import scripts.CITY_w19_obs as W
for k in [int(x) for x in '$LT'.split()]:
    f = W.fam_of(k); assert ('W19 prep family in force %s obs %s' % (f, W.FAMS[f][1])) in open('$D/prep/prep_k%d.out' % k).read(), ('family not in force', k)
    net = torch.load('$D/lights/RL-H_t%d.pt' % k, weights_only=False)['net']; w = M.widen(net); din = net[0].in_features
    rng = np.random.default_rng(k); O = rng.uniform(0, 3, (100000, din)).astype(np.float32); F = rng.uniform(0, 3, (100000, 5)).astype(np.float32)
    with torch.no_grad():
        a = net(torch.as_tensor(O)).argmax(1); b = w(torch.as_tensor(np.concatenate([O, F], 1))).argmax(1)
    assert int((a != b).sum()) == 0, (k, int((a != b).sum()))
print('KW19-2 PASS: family in force in every prep; widened = family net on 100000 inputs per light')" || { echo "KW19-2 FAIL: stop"; exit 1; }
# 4. N2 logs, fits, KF-2 (first light of each family)
J=$D/collect_jobs_s$STAGE.txt; : > $J; for k in $LT; do for s in $TS; do echo "$k $s" >> $J; done; done
xargs -P 9 -L 1 bash -c '[ -f $D/cdata/c2_t$0/feat_s$1.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $D/cdata/c2_t$0 --spat-arm fc2:0.1:$D/prep/prov_rlh$0_cl.json --light RL-H:$0 --fleet PL:$DEV --seeds $1 $SM --tag C_t$0_s$1 --out $D/cdata/c2_t$0 >> $D/cdata/run.log 2>&1 || { echo "FAIL collect $0 $1"; exit 255; }' < $J || { echo "collection failure: stop"; exit 1; }
for k in $LT; do [ -f $D/cmodel/n2_k$k.pt ] || $PY -u scripts/CITY_n2_fit.py $k $D/cdata/c2_t$k $D/cmodel > $D/cmodel/fit_t$k.log 2>&1 || { echo "FIT FAIL t$k"; exit 1; }; done
F1=$(echo $FS | cut -d' ' -f1)
for K1 in $FIRST; do K=$D/check/kf2_t$K1; mkdir -p $K
  $RUN scripts/CITY_eval_n2.py --n2 0.5:$D/cmodel/n2_k$K1.pt --featlog $K --light RL-H:$K1 --fleet PL:$FD/L11_s${F1}_fleet.pt --seeds 0 --smoke --tag KF2_n2 --out $K > $K/run.log 2>&1 || { echo "KF-2 run FAIL t$K1"; exit 1; }
  $PY scripts/CITY_n2_parity.py $K 0 $D/cmodel/n2_k$K1.pt | tee $D/check/kf2_t$K1.txt || { echo "KF-2 FAIL t$K1: stop"; exit 1; }; done
echo "forecasters done $(date)"
# 5. fresh traffic 1400-1419
if [ "${SMOKE:-0}" != 1 ] && [ ! -f $G/CONF1400_generated ]; then
  for s in $(seq 1400 1419); do [ -f $G/rou_s$s.xml ] && { echo "KW19-3 FAIL: rou_s$s existed"; exit 1; }; done
  for s in $(seq 1400 1419); do $PY $RT -n research/city_sim/net/grid4.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done
  date > $G/CONF1400_generated; echo "traffic 1400-1419 generated $(date)"; fi
# 6. rows
run_jobs() { export PY SM; export OUT=$2 SS="$3" CH="$4"
  xargs -P 9 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $OUT/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w19_run.py $CH "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
J=$D/gate_jobs_s$STAGE.txt; : > $J; echo "OFF_t0_h none scripts/CITY_eval6_v11.py --light FT --fleet L-ACT:0 --guard always" >> $J
for k in $LT; do echo "GATE_t${k}_h none scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always" >> $J; done
run_jobs $J $D/gate "$CS" "" || { echo "gate rows failure: stop"; exit 1; }; echo "gate rows done $(date)"
N4() { echo "--n4 $2:hyb:$D/prep/prov_rlh$1_cl.json:$D/cmodel/n2_k$1.pt"; }
J=$D/conf_jobs_s$STAGE.txt; : > $J
for f in $FAMS; do for j in $SL; do k=$(( $(k0 $f) + j ))
  for s in $FS; do F="--light RL-H:$k --fleet PL:$FD/L11_s${s}_fleet.pt"
    for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
      echo "R${x}_t${k}_s$s $em scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
      echo "SV${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $k 0.1) $F" >> $J
      case $f in B2*) ;; *) echo "TG${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $k 0.1) $F --light-obs q:1:0.25" >> $J;; esac; done; done; done; done
echo "conf rows: $(wc -l < $J) lines x $(echo $CS | wc -w) seeds"
run_jobs $J $D/conf "$CS" "scripts/CITY_w13_modes.py" || { echo "confirmation failure: stop"; exit 1; }
W19_SMOKE=${SMOKE:-0} $PY scripts/CITY_w19_report.py $STAGE $D || { echo "report FAIL"; exit 1; }
echo "W19-S$STAGE done $(date)"
