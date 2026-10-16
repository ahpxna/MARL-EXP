#!/usr/bin/env bash
# W21-E (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-E): TSI-G (BIS, every light) and TSI's default (TG, AH) in the W17 field-matched world,
# on W21-A's lights, fleets, forecasters and fresh traffic 1420-1439.  Steps: CREEP recalibrated in this world (CITY_w21_twin_calib_w17.py,
# KW17-0 in the workers) -> KW20-2 (bis0, AH t34 and RDQ t89) and KW20-3 (twin, AH t34) -> BIS / TG rows (fuel-by-mode logger) -> world
# check -> CITY_w21e_report.py.  LANES (default 6).  SMOKE=1: W21-A's smoke directory (slot 0 of each family), fleet s2213, seed 860.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; LANES=${LANES:-6}
FAMS="${W21_FAMS:-AH SRL RDQ RMP RWV}"
if [ "${SMOKE:-0}" = 1 ]; then D=${W21A_DIR:-research/city_sim/w21_20261015/smoke_a}; SL="0"; FS="2213"; CS="860"; SM="--smoke"; CALE=300; CALS="0 1"
else D=${W21A_DIR:-research/city_sim/w21_20261015/w17}; SL="0 1 2 3 4"; FS="2213 2313 2413 2513"; CS="$(seq -s ' ' 1420 1439)"; SM=""; CALE=3600; CALS="0 1 2 3 4 5 6 7"; fi
export XPLAY_TMP=$(cd $D/check && pwd) W7_FPR_DIR=$(cd $D && pwd) W20_LIGHTS=$(cd $D/lights && pwd) W19_LIGHTS=$(cd $D/lights && pwd)
FD=research/city_sim/w17_20261008/fresh5/fleets; W17="$PY -u scripts/CITY_w17_world.py"; RUN="$W17 scripts/CITY_w20_run.py"
echo "W21-E start $(date); dir $D; lanes $LANES"
echo "sources: $(shasum -a 256 scripts/CITY_w21_twin_calib_w17.py scripts/CITY_w20_bench.py scripts/CITY_w20_run.py scripts/CITY_w17_world.py scripts/CITY_eval_n4.py | awk '{print $2":"substr($1,1,12)}' | tr '\n' ' ')"
k0() { case $1 in AH) echo 34;; SRL) echo 84;; RDQ) echo 89;; RMP) echo 94;; RWV) echo 99;; esac; }
LT=""; for f in $FAMS; do for j in $SL; do LT="$LT $(( $(k0 $f) + j ))"; done; done; LAH=""; for j in $SL; do LAH="$LAH $((34 + j))"; done
# 1. CREEP in this world
[ -f $D/twin_calib_w17.json ] || W20_CAL_P=9 $PY -u scripts/CITY_w21_twin_calib_w17.py $D/twin_calib_w17.json $CALE $CALS > $D/check/twin_calib_w17.txt 2>&1 || { echo "twin calibration FAIL"; tail -3 $D/check/twin_calib_w17.txt; exit 1; }
n=$(grep -c "KW17-0: type v_passenger tau" $D/check/twin_calib_w17.txt); echo "KW17-0 lines in the calibration workers: $n"; [ "$n" -ge 1 ] || { echo "W17 world not in force in calibration: stop"; exit 1; }
grep -E "^CREEP|chosen" $D/check/twin_calib_w17.txt; export W20_CREEP=$($PY -c "import json; print(json.load(open('$D/twin_calib_w17.json'))['creep'])"); echo "W20_CREEP=$W20_CREEP"
# 2. KW20-2 / KW20-3 in this world
CK() { $RUN scripts/CITY_w20_check.py $1 $2 > $D/check/kw21e_$1_t$2.txt 2>&1; grep KW20 $D/check/kw21e_$1_t$2.txt | cut -c1-300; }
for K1 in 34 $([ "${SMOKE:-0}" = 1 ] && echo 84 || echo 89); do CK bis0 $K1; grep -q "^PASS" $D/check/kw21e_bis0_t$K1.txt || { echo "KW20-2 FAIL t$K1: stop"; exit 1; }; done
CK twin 34
# 3. rows
run_jobs() { export PY SM W17 OUT=$2 SS="$3" CH="$4"
  xargs -P $LANES -L 1 bash -c 'T=$0; M=$1; shift; [ -f $OUT/$T.json ] || nice -n 5 $W17 scripts/CITY_w9_run.py $M scripts/CITY_w20_run.py $CH "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run_e.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
N4() { echo "--n4 0.1:hyb:$D/prep/prov_rlh$1_cl.json:$D/cmodel/n2_k$1.pt"; }
J=$D/conf_jobs_e.txt; : > $J
for k in $LT; do for s in $FS; do F="--light RL-H:$k --fleet PL:$FD/L11_s${s}_fleet.pt"; echo "BIS_t${k}_s$s none scripts/CITY_eval_n4.py $(N4 $k) $F --light-obs bis" >> $J; done; done
for k in $LAH; do for s in $FS; do F="--light RL-H:$k --fleet PL:$FD/L11_s${s}_fleet.pt"; echo "TG_t${k}_s$s none scripts/CITY_eval_n4.py $(N4 $k) $F --light-obs q:1:0.25" >> $J; done; done
echo "rows: $(wc -l < $J) jobs x $(echo $CS | wc -w) seeds"
run_jobs $J $D/conf "$CS" "scripts/CITY_w13_modes.py" || { echo "rows failure: stop"; exit 1; }
n=$(grep -c "KW17-0: type v_passenger tau" $D/conf/run_e.log); j=$(wc -l < $J); echo "KW17-0 lines in the W21-E rows: $n (jobs $j)"
grep -q "KW17-0 FAIL" $D/conf/run_e.log && { echo "KW17-0 FAIL: stop"; exit 1; }; [ "$n" -ge "$j" ] || { echo "KW17-0 lines fewer than jobs: stop"; exit 1; }
W21_SMOKE=${SMOKE:-0} W21_FAMS="$FAMS" $PY scripts/CITY_w21e_report.py $D || { echo "report FAIL"; exit 1; }
echo "W21-E done $(date)"
