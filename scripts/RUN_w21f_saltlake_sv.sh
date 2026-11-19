#!/usr/bin/env bash
# W21-F (PROTOCOL_CITY_WAVE21_20261015, Amendment W21-F): the forecast alone (SV: the F1-4 four-green forecaster at q 0.1, no adapter) and a
# rerun of R on recorded Salt Lake demand (400S & 200W, RLW t11, fleets s13 / s113, the 20 CONF days, HBEFA4, fuel-by-mode logger), exactly
# F1-4's chain (CITY_w9_run none -> CITY_sl_runw4 -> CITY_w13_modes -> CITY_m4s_tsi_eval).  F1-4's provider files and R / TG / HARM rows are
# copied unchanged from git (sparse checkout) into the W21-F directory.  KW21-F1: rerun R = F1-4 R.  Then CITY_w21f_report.py.
# SMOKE=1: fleet s13, the first CONF day, 600 s, into W21F_DIR (default .../w21_20261015/smoke_f).
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 SL_SITE=400sX200w; PY=external_envs/city_runtime/bin/python; LANES=${LANES:-4}
if [ "${SMOKE:-0}" = 1 ]; then S=${W21F_DIR:-research/city_sim/w21_20261015/smoke_f}; else S=${W21F_DIR:-research/city_sim/w21_20261015/saltlake}; fi
G=research/city_sim/f1_saltlake/tsi; mkdir -p $S/prov $S/model $S/conf $S/f14; export XPLAY_TMP=$(cd $S && pwd)
for f in fkcl.json ft.json ol.json; do [ -s $S/prov/$f ] || git show HEAD:$G/prov/$f > $S/prov/$f || { echo "git copy FAIL $f"; exit 1; }; done
[ -s $S/model/n2k4.pt ] || cp -p $G/model/n2k4.pt $S/model/n2k4.pt; [ -s $S/model/n2k4.pt.json ] || git show HEAD:$G/model/n2k4.pt.json > $S/model/n2k4.pt.json
for a in R TG HARM; do for s in 13 113; do [ -s $S/f14/${a}_t11_s$s.json ] || git show HEAD:$G/conf/${a}_t11_s$s.json > $S/f14/${a}_t11_s$s.json || { echo "git copy FAIL ${a}_t11_s$s"; exit 1; }; done; done
L11=research/city_sim/f1_saltlake/gateW/lights/RLW_400sX200w_11.pt; FLD=research/city_sim/f1_saltlake/m1/fleets; TK="n2k:$S/prov/fkcl.json:$S/model/n2k4.pt"
DAYS() { $PY -c "import sys; sys.path.insert(0,'.'); from scripts.CITY_sl_build import days; print(' '.join(str(d.timetuple().tm_yday) for d in days('400sX200w','$1')))"; }
CS="$(DAYS conf)"; FS="13 113"; SM=""
if [ "${SMOKE:-0}" = 1 ]; then CS="$(echo $CS | cut -d' ' -f1)"; FS="13"; SM="--smoke"; fi
echo "W21-F start $(date); dir $S; CONF days $CS"
run_jobs() { export PY SM; export OUT=$2 SS="$3"
  xargs -P $LANES -L 1 bash -c 'T=$0; M=$1; Q=$2; shift 2; [ -f $OUT/$T.json ] && exit 0; if [ "$Q" != "-" ]; then export SL_Q=$Q; fi
    nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_sl_runw4.py scripts/CITY_w13_modes.py scripts/CITY_m4s_tsi_eval.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
J=$S/conf_jobs.txt; : > $J
for s in $FS; do P="PL:$FLD/L11_sl_s${s}_fleet.pt"
  echo "R_t11_s$s none - --tk none --light RLW:$L11 --fleet $P" >> $J
  echo "SV_t11_s$s none 0.1 --tk $TK --light RLW:$L11 --fleet $P" >> $J; done
run_jobs $J $S/conf "$CS" || { echo "rows failure: stop"; exit 1; }
W21_SMOKE=${SMOKE:-0} $PY scripts/CITY_w21f_report.py $S || { echo "report FAIL"; exit 1; }
echo "W21-F done $(date)"
