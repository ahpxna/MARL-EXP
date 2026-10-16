#!/usr/bin/env bash
# W21-L (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-L): train four fleets on the full Midtown map (MT-E setting, deployed SPaT service,
# B2D light t59..t62 paired with seeds 1413..1713, scratch, 200 episodes, resumable) -> evaluate SVm under B2D t59-63 and AH t34-38 on days
# 0-4 -> KW21-L1 (a Midtown-fleet R cell = W21-B's MTW_R) -> CITY_w21l_report.py.  Re-running resumes unfinished trainings and skips
# finished rows.  SMOKE=1: one fleet, 2 smoke episodes, t59 / t34, day 0, --smoke, into .../smoke_l.
set -o pipefail; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=actrest MT_NET=midtown_full W13_AB=0:0
PY=external_envs/city_runtime/bin/python; W19=research/city_sim/w19_20261008; B=research/city_sim/w21_20261015/midtown
if [ "${SMOKE:-0}" = 1 ]; then E=${W21L_DIR:-research/city_sim/w21_20261015/smoke_l}; FS="1413"; NEP=2; SMT="--smoke"; LB="59"; LA="34"; DAYS="0"; SM="--smoke"
else E=${W21L_DIR:-research/city_sim/w21_20261015/midtown_fleet}; FS="1413 1513 1613 1713"; NEP=200; SMT=""; LB="59 60 61 62 63"; LA="34 35 36 37 38"; DAYS="0 1 2 3 4"; SM=""; fi
mkdir -p $E/fleets; echo "W21-L start $(date); dir $E; $(pmset -g batt | sed -n 2p | cut -c1-60)"
echo "sources: $(shasum -a 256 scripts/CITY_w21_train_fleet_mt.py scripts/CITY_w13_train_f1bt.py scripts/CITY_fleet_train_f1b.py scripts/DEMO_midtown.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
# 1. training (parallel, resumable)
i=0; for s in $FS; do k=$((59 + i)); i=$((i + 1))
  [ -f $E/fleets/MTL_s${s}_fleet.pt ] || W13_N4=0.1:$W19/prep/prov_rlh${k}_cl.json:$W19/cmodel/n2_k$k.pt nice -n 5 $PY -u scripts/DEMO_midtown.py scripts/CITY_w20_run.py scripts/CITY_w21_train_fleet_mt.py --seed $s --light-k $k --episodes $NEP --name MTL_s$s --out $E/fleets --resume $SMT >> $E/fleets/train_s$s.out 2>&1 &
done; wait; echo "training done $(date)"
for s in $FS; do [ -f $E/fleets/MTL_s${s}_fleet.pt ] || { echo "training FAILED for s$s: stop (re-run to resume)"; tail -3 $E/fleets/train_s$s.out; exit 1; }; done
# 2. evaluation
export PY E SM DAYS; export M="$PY -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py"
run() { xargs -P ${LANES:-6} -L 1 bash -c 'T=$0; grep -qs "\"status\": \"COMPLETE\"" $E/$T.json && exit 0
  nice -n 5 $M "$@" --seeds $DAYS $SM --tag $T --out $E > $E/$T.log 2>&1 || echo "FAIL $T"' < $1
  bad=0; while read -r T _; do grep -qs '"status": "COMPLETE"' $E/$T.json || { echo "INCOMPLETE $T"; bad=1; }; done < $1; return $bad; }
J=$E/jobs_eval.txt; : > $J; F1=$(echo $FS | cut -d' ' -f1)
echo "MTL_R_t59_s$F1 scripts/CITY_eval_f1.py --spat-arm none --light RL-H:59 --fleet PL:$E/fleets/MTL_s${F1}_fleet.pt" >> $J
for k in $LB $LA; do for s in $FS; do echo "MTL_SV_t${k}_s$s scripts/CITY_eval_n4.py --n4 0.1:hyb:$W19/prep/prov_rlh${k}_cl.json:$W19/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:$E/fleets/MTL_s${s}_fleet.pt" >> $J; done; done
echo "evaluation: $(wc -l < $J) jobs x $(echo $DAYS | wc -w) days"; run $J || echo "evaluation incomplete (listed above)"; echo "evaluation done $(date)"
W21_SMOKE=${SMOKE:-0} $PY scripts/CITY_w21l_report.py $E $B "$FS" "$LB" "$LA" "$DAYS" || { echo "report FAIL"; exit 1; }
echo "W21-L done $(date)"
