#!/usr/bin/env bash
# W20 (PROTOCOL_CITY_WAVE20_20261009): does the closed loop hit the benchmark signal representations, and does TSI-G (human-twin sensing)
# repair a frozen signal without retraining?  Families SRL (sumo-rl default), RDQ (RESCO drq_norm + wait_norm), RMP (RESCO mplight + pressure),
# RWV (RESCO wave, threshold-free control); 5 lights each (the RL-H recipe, W19 trainer, DQN seed by slot), main Krauss grid4, FRESH3 fleets,
# fresh traffic 1400-1419 (W19's).  Steps: training [KW20-T] -> twin calibration (CREEP) -> KW20-1/2/3 -> forecasters (FRESH3 recipe; KF-3,
# KW19-2-style, KF-2) -> gate rows -> R / SV / BIS x HBEFA4 / PHEMlight5 (+ BIS on the W19 AH lights 34-38) -> CITY_w20_report.py.
# SMOKE=1: slot 0, 15-episode smoke trainings (3 gave never-switching lights), calibration 2 seeds x 300 s, fleet s1413, seed 860, into W20_DIR (W19 rows from W19_SMOKE_DIR).
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
FAMS="SRL RDQ RMP RWV"
D=${W20_DIR:-research/city_sim/w20_20261009}; D19=${W19_SMOKE_DIR:-research/city_sim/w19_20261008}
mkdir -p $D/lights $D/traces $D/m2b $D/prep $D/cdata $D/cmodel $D/check $D/gate $D/conf
export XPLAY_TMP=$(cd $D/check && pwd) W7_FPR_DIR=$(cd $D && pwd) W20_LIGHTS=$(cd $D/lights && pwd); G=research/city_sim/demand/grid4
[ "${SMOKE:-0}" = 1 ] && export W19_LIGHTS=$(cd $D19/lights && pwd)
DEV=research/city_sim/spat_pilot_20261004/fleets_v11/L11_s13_fleet.pt; FD=research/city_sim/w15_20261007/fresh3/fleets
RUN="$PY -u scripts/CITY_w20_run.py"; P5=em:PHEMlight5/PC_EU4_G; echo "W20 start $(date)"
echo "sources: $(shasum -a 256 scripts/CITY_w20_bench.py scripts/CITY_w20_run.py scripts/CITY_w19_obs.py scripts/CITY_w19_run.py scripts/CITY_w19_train_light.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
k0() { case $1 in SRL) echo 84;; RDQ) echo 89;; RMP) echo 94;; RWV) echo 99;; AH) echo 34;; esac; }
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; SL="0"; FS="1413"; LEP=15; TS="0 1 2 3 4 5 6 7"; CS="860"; NF=1; CALS="0 1"; CALE=300; export W7_PREP_N=1 W7_PREP_END=300
else SM=""; SL="0 1 2 3 4"; FS="1413 1513 1613 1713"; LEP=120; TS="0 1 2 3 4 5 6 7"; CS="$(seq -s ' ' 1400 1419)"; NF=8; CALS="0 1 2 3 4 5 6 7"; CALE=3600; fi
[ "${SMOKE:-0}" = 1 ] || [ -f $G/CONF1400_generated ] || { echo "traffic 1400-1419 missing (W19 generates it): stop"; exit 1; }
LT=""; FIRST=""; for f in $FAMS; do FIRST="$FIRST $(k0 $f)"; for j in $SL; do LT="$LT $(( $(k0 $f) + j ))"; done; done
LAH=""; for j in $SL; do LAH="$LAH $((34 + j))"; done; echo "families $FAMS lights$LT; AH lights$LAH"
# 1. training
J=$D/train_jobs.txt; : > $J; for k in $LT; do echo $k >> $J; done
export PY D SM LEP RUN TS DEV NF; xargs -P 10 -L 1 bash -c '[ -f $D/lights/RL-H_t$0.pt ] || nice -n 5 $PY -u scripts/CITY_w20_train_light.py --out $D/lights --k $0 --episodes $LEP $SM > $D/lights/train_t$0.out 2>&1 || { echo "FAIL train $0"; exit 255; }' < $J || { echo "training failure: stop"; exit 1; }
$PY -c "
import sys, torch; sys.path.insert(0, '.'); import scripts.CITY_w20_bench as B; import scripts.CITY_w19_obs as W
for k in [int(x) for x in '$LT'.split()]:
    d = torch.load('$D/lights/RL-H_t%d.pt' % k, weights_only=False); f = W.fam_of(k)
    assert d['family'] == f and d['episodes'] == $LEP and d['dqn_seed'] == W.dqn_seed(k) and d['net'][0].in_features == W.DIM[W.FAMS[f][1]], (k, d['family'])
print('KW20-T PASS: families, episodes, seeds, input dims')" || { echo "KW20-T FAIL: stop"; exit 1; }; echo "training done $(date)"
# 2. twin calibration on all-human pre-deployment logs (TRAIN seeds, FT), then every later process uses W20_CREEP
[ -f $D/twin_calib.json ] || W20_CAL_P=9 $RUN scripts/CITY_w20_twin_calib.py $D/twin_calib.json $CALE $CALS > $D/check/twin_calib.txt 2>&1 || { echo "twin calibration FAIL"; tail -3 $D/check/twin_calib.txt; exit 1; }
grep -E "CREEP|chosen" $D/check/twin_calib.txt; export W20_CREEP=$($PY -c "import json; print(json.load(open('$D/twin_calib.json'))['creep'])"); echo "W20_CREEP=$W20_CREEP"
# 3. self-checks KW20-1 (obs, first light of each family), KW20-2 (TSI-G with an empty fleet = raw; AH and RDQ), KW20-3 (twin fidelity, AH)
CK() { $RUN scripts/CITY_w20_check.py $1 $2 > $D/check/kw20_$1_t$2.txt 2>&1; grep KW20 $D/check/kw20_$1_t$2.txt | cut -c1-300; }
for K1 in $FIRST; do CK obs $K1; grep -q "^PASS" $D/check/kw20_obs_t$K1.txt || { echo "KW20-1 FAIL t$K1: stop"; exit 1; }; done
for K1 in $(echo $LAH | cut -d' ' -f1) $(k0 RDQ); do CK bis0 $K1; grep -q "^PASS" $D/check/kw20_bis0_t$K1.txt || { echo "KW20-2 FAIL t$K1: stop"; exit 1; }; done
CK twin $(echo $LAH | cut -d' ' -f1)
# 4. forecasters (FRESH3 recipe)
J=$D/trace_jobs.txt; : > $J; for k in $LT; do echo $k >> $J; done
xargs -P 9 -L 1 bash -c '[ -f $D/traces/fit_RLH$0.json ] || nice -n 5 $RUN scripts/CITY_eval4_sigma.py --sigma 0.3 --light RL-H:$0 --fleet L-ACT:0 --guard always --seeds $TS $SM --record $D/traces/rlh$0_s{seed}.npz --tag fit_RLH$0 --out $D/traces >> $D/traces/run.log 2>&1 || { echo "FAIL trace $0"; exit 255; }' < $J || { echo "trace failure: stop"; exit 1; }
for k in $LT; do F=""; for s in $TS; do F="$F $D/traces/rlh${k}_s$s.npz"; done; [ -f $D/m2b/forecast_rlh$k.json ] || $RUN scripts/CITY_spat_forecast.py fit $k $D/m2b/forecast_rlh$k.json $F > $D/m2b/fit_t$k.log 2>&1 || { echo "open-loop fit FAIL t$k"; tail -3 $D/m2b/fit_t$k.log; exit 1; }; done
# degenerate lights (some green index never completed in the 8 traces: no forecaster can be fitted) exclude their whole family (registered)
DEG=$($PY -c "
import json, sys; sys.path.insert(0, '.'); import scripts.CITY_w20_bench as B; import scripts.CITY_w19_obs as W
bad = sorted({W.fam_of(k) for k in [int(x) for x in '$LT'.split()] if len(json.load(open('$D/m2b/forecast_rlh%d.json' % k))['pooled']) < 2}); print(' '.join(bad))")
if [ -n "$DEG" ]; then echo "DEGENERATE (excluded with every light of the family): $DEG"; F2=""; for f in $FAMS; do case " $DEG " in *" $f "*) ;; *) F2="$F2 $f";; esac; done; FAMS=$F2
  LT=""; FIRST=""; for f in $FAMS; do FIRST="$FIRST $(k0 $f)"; for j in $SL; do LT="$LT $(( $(k0 $f) + j ))"; done; done
  J=$D/trace_jobs.txt; : > $J; for k in $LT; do echo $k >> $J; done; echo "families kept: $FAMS"; fi
export W20_FAMS="$FAMS"
xargs -P 9 -L 1 bash -c '[ -f $D/prep/prov_rlh$0_cl.json ] || nice -n 5 $RUN scripts/CITY_w19_prep.py $0 $D/prep > $D/prep/prep_k$0.out 2>&1 || { echo "FAIL prep $0"; exit 255; }' < $J || { echo "prep failure: stop"; exit 1; }
for k in $LT; do $PY -c "
import json; T = json.load(open('$D/prep/prov_rlh${k}_cl.json')); assert len(T['per']) == 16 and T['n_files'] == $NF, (len(T['per']), T['n_files']); print('KF-3 t$k ok')" || { echo "KF-3 FAIL t$k"; exit 1; }; done
$PY -c "
import sys, numpy as np, torch; sys.path.insert(0, '.'); import scripts.CITY_m3_core as M; import scripts.CITY_w20_bench as B; import scripts.CITY_w19_obs as W
for k in [int(x) for x in '$LT'.split()]:
    f = W.fam_of(k); assert ('W19 prep family in force %s obs %s' % (f, W.FAMS[f][1])) in open('$D/prep/prep_k%d.out' % k).read(), ('family not in force', k)
    net = torch.load('$D/lights/RL-H_t%d.pt' % k, weights_only=False)['net']; w = M.widen(net); din = net[0].in_features
    rng = np.random.default_rng(k); O = rng.uniform(0, 3, (100000, din)).astype(np.float32); F = rng.uniform(0, 3, (100000, 5)).astype(np.float32)
    with torch.no_grad():
        a = net(torch.as_tensor(O)).argmax(1); b = w(torch.as_tensor(np.concatenate([O, F], 1))).argmax(1)
    assert int((a != b).sum()) == 0, (k, int((a != b).sum()))
print('KW20-P PASS: family in force in every prep; widened = family net on 100000 inputs per light')" || { echo "KW20-P FAIL: stop"; exit 1; }
J=$D/collect_jobs.txt; : > $J; for k in $LT; do for s in $TS; do echo "$k $s" >> $J; done; done
xargs -P 9 -L 1 bash -c '[ -f $D/cdata/c2_t$0/feat_s$1.npz ] || nice -n 5 $RUN scripts/CITY_n2_collect.py --featlog $D/cdata/c2_t$0 --spat-arm fc2:0.1:$D/prep/prov_rlh$0_cl.json --light RL-H:$0 --fleet PL:$DEV --seeds $1 $SM --tag C_t$0_s$1 --out $D/cdata/c2_t$0 >> $D/cdata/run.log 2>&1 || { echo "FAIL collect $0 $1"; exit 255; }' < $J || { echo "collection failure: stop"; exit 1; }
for k in $LT; do [ -f $D/cmodel/n2_k$k.pt ] || $PY -u scripts/CITY_n2_fit.py $k $D/cdata/c2_t$k $D/cmodel > $D/cmodel/fit_t$k.log 2>&1 || { echo "FIT FAIL t$k"; exit 1; }; done
F1=$(echo $FS | cut -d' ' -f1)
for K1 in $FIRST; do K=$D/check/kf2_t$K1; mkdir -p $K
  $RUN scripts/CITY_eval_n2.py --n2 0.5:$D/cmodel/n2_k$K1.pt --featlog $K --light RL-H:$K1 --fleet PL:$FD/L11_s${F1}_fleet.pt --seeds 0 --smoke --tag KF2_n2 --out $K > $K/run.log 2>&1 || { echo "KF-2 run FAIL t$K1"; exit 1; }
  $PY scripts/CITY_n2_parity.py $K 0 $D/cmodel/n2_k$K1.pt | tee $D/check/kf2_t$K1.txt || { echo "KF-2 FAIL t$K1: stop"; exit 1; }; done
echo "forecasters done $(date)"
# 5. rows
run_jobs() { export PY SM; export OUT=$2 SS="$3" CH="$4"
  xargs -P 9 -L 1 bash -c 'T=$0; M=$1; shift; [ -f $OUT/$T.json ] || nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_w20_run.py $CH "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
J=$D/gate_jobs.txt; : > $J; echo "OFF_t0_h none scripts/CITY_eval6_v11.py --light FT --fleet L-ACT:0 --guard always" >> $J
for k in $LT; do echo "GATE_t${k}_h none scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always" >> $J; done
run_jobs $J $D/gate "$CS" "" || { echo "gate rows failure: stop"; exit 1; }; echo "gate rows done $(date)"
N4() { echo "--n4 $2:hyb:$1/prep/prov_rlh$3_cl.json:$1/cmodel/n2_k$3.pt"; }
J=$D/conf_jobs.txt; : > $J
for k in $LT $LAH; do PD=$D; case " $LAH " in *" $k "*) PD=$D19;; esac
  for s in $FS; do F="--light RL-H:$k --fleet PL:$FD/L11_s${s}_fleet.pt"
    for em in none $P5; do x=""; [ "$em" = none ] || x="P5"
      case " $LAH " in *" $k "*) ;; *)
        echo "R${x}_t${k}_s$s $em scripts/CITY_eval_f1.py --spat-arm none $F" >> $J
        echo "SV${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $PD 0.1 $k) $F" >> $J;; esac
      echo "BIS${x}_t${k}_s$s $em scripts/CITY_eval_n4.py $(N4 $PD 0.1 $k) $F --light-obs bis" >> $J; done; done; done
echo "conf rows: $(wc -l < $J) lines x $(echo $CS | wc -w) seeds"
run_jobs $J $D/conf "$CS" "scripts/CITY_w13_modes.py" || { echo "confirmation failure: stop"; exit 1; }
W20_SMOKE=${SMOKE:-0} $PY scripts/CITY_w20_report.py $D $D19 || { echo "report FAIL"; exit 1; }
echo "W20 done $(date)"
