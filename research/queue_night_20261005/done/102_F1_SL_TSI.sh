#!/usr/bin/env bash
# F1-3 / F1-4 (PROTOCOL_CITY_F1_SALTLAKE_20261008, Amendment A5): 400S & 200W, RLW light seed 11, four-green TSI (N2K4 + RLWQ adapter).
# Calibration (development fleet GLOSAL:0.3; 8 TRAIN days): open-loop K table -> closed-loop K table -> N2K4 logs -> fit -> KS-1 / KS-2;
# tuning on TUNE days (R, grid (A, B) x q, HBEFA4 / PHEMlight5) -> R15-U; CONF days generated (non-existence check); M2 (OFF, R, HARM =
# old FT program as SPaT) and R, TG, TU with the deployed fleets s13 / s113 x HBEFA4 / PHEMlight5 -> D-F1a.
# SMOKE=1: 2 TRAIN days, 1 TUNE day, 1 CONF day (from the conf list, generated only if absent), fleet s13, 600 s, into SL_DIR.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 SL_SITE=400sX200w; PY=external_envs/city_runtime/bin/python
B=${SL_DIR:-research/city_sim/f1_saltlake}; D=$B/tsi; mkdir -p $D/traces $D/prov $D/data $D/model $D/check $D/tune $D/conf; export XPLAY_TMP=$(cd $D/check && pwd)
L11=research/city_sim/f1_saltlake/gateW/lights/RLW_400sX200w_11.pt; FLD=research/city_sim/f1_saltlake/m1/fleets; RUN4="$PY -u scripts/CITY_sl_runw4.py"; EV="$RUN4 scripts/CITY_m4s_tsi_eval.py"
P5=em:PHEMlight5/PC_EU4_G; echo "F1-SL-TSI start $(date)"
DAYS() { $PY -c "import sys; sys.path.insert(0,'.'); from scripts.CITY_sl_build import days; print(' '.join(str(d.timetuple().tm_yday) for d in days('400sX200w','$1')))"; }
TR8="$(DAYS train | cut -d' ' -f1-8)"; TU4="$(DAYS tune)"; CS="$(DAYS conf)"; FS="13 113"; SM=""
if [ "${SMOKE:-0}" = 1 ]; then TR8="$(echo $TR8 | cut -d' ' -f1-2)"; TU4="$(echo $TU4 | cut -d' ' -f1)"; CS="$(echo $CS | cut -d' ' -f1)"; FS="13"; SM="--smoke"; fi
# 0. CONF days (recorded demand; generated once after the non-existence check)
if [ ! -f research/city_sim/demand/saltlake/400sX200w/demand_conf.json ]; then $PY scripts/CITY_sl_build.py demand 400sX200w conf || { echo "CONF demand FAIL: stop"; exit 1; }; fi
# 1. open-loop K table (RLW, all humans), FT table (FT, all humans), closed-loop K table (development fleet on the open-loop table)
$EV --tk none --light RLW:$L11 --fleet L-ACT:0 --guard always --seeds $TR8 $SM --record $D/traces/ol_s{seed}.npz --tag OL --out $D/traces >> $D/traces/run.log 2>&1 || { echo "OL traces FAIL: stop"; exit 1; }
$EV --tk none --light FT --fleet L-ACT:0 --guard always --seeds $TR8 $SM --record $D/traces/ft_s{seed}.npz --tag FTT --out $D/traces >> $D/traces/run.log 2>&1 || { echo "FT traces FAIL: stop"; exit 1; }
$RUN4 scripts/CITY_sl_fitk.py $D/prov/ol.json $(for s in $TR8; do echo $D/traces/ol_s$s.npz; done) || { echo "fit OL FAIL: stop"; exit 1; }
$RUN4 scripts/CITY_sl_fitk.py $D/prov/ft.json $(for s in $TR8; do echo $D/traces/ft_s$s.npz; done) || { echo "fit FT FAIL: stop"; exit 1; }
$EV --tk fk:0.5:$D/prov/ol.json --light RLW:$L11 --fleet GLOSAL:0.3 --seeds $TR8 $SM --record $D/traces/cl_s{seed}.npz --tag CL --out $D/traces >> $D/traces/run.log 2>&1 || { echo "CL traces FAIL: stop"; exit 1; }
$RUN4 scripts/CITY_sl_fitk.py $D/prov/fkcl.json $(for s in $TR8; do echo $D/traces/cl_s$s.npz; done) || { echo "fit CL FAIL: stop"; exit 1; }
# 2. N2K4 logs, fit, KS-1 / KS-2 (KS-1 at the provider default q 0.5: the parity compares the 0.5 column)
for s in $TR8; do [ -f $D/data/feat_s$s.npz ] || $EV --tk fk:0.1:$D/prov/fkcl.json --light RLW:$L11 --fleet GLOSAL:0.3 --featlog $D/data --seeds $s $SM --tag C_s$s --out $D/data >> $D/data/run.log 2>&1 & done; wait
for s in $TR8; do [ -f $D/data/feat_s$s.npz ] || { echo "collection incomplete s$s: stop"; exit 1; }; done
$RUN4 scripts/CITY_n2k4.py fit $D/data $D/model/n2k4.pt > $D/model/fit.log 2>&1 || { echo "N2K4 fit FAIL: stop"; tail -3 $D/model/fit.log; exit 1; }
K1=$(echo $TR8 | cut -d' ' -f1); TK="n2k:$D/prov/fkcl.json:$D/model/n2k4.pt"
$EV --tk $TK --light RLWQ:$L11:1:0.25 --fleet GLOSAL:0.3 --featlog $D/check/ks1 --seeds $K1 --smoke --tag KS1 --out $D/check > $D/check/ks1.log 2>&1 || { echo "KS1 run FAIL: stop"; tail -5 $D/check/ks1.log; exit 1; }
$RUN4 scripts/CITY_n2k4.py parity $D/check/ks1 $K1 $D/model/n2k4.pt | tee $D/check/ks1_parity.txt || { echo "KS-1 FAIL: stop"; exit 1; }
$PY -c "import json;x=json.load(open('$D/check/KS1_tk.json'));p=x['provider'];print('KS-2', p);raise SystemExit(0 if p['n2k']>0 and p['exc']==0 else 1)" || { echo "KS-2 FAIL: stop"; exit 1; }
# 3. tuning (development fleet), HBEFA4 / PHEMlight5, modes logger
run_jobs() { export PY SM; export OUT=$2 SS="$3"
  xargs -P 6 -L 1 bash -c 'T=$0; M=$1; Q=$2; shift 2; [ -f $OUT/$T.json ] && exit 0; if [ "$Q" != "-" ]; then export SL_Q=$Q; fi
    nice -n 5 $PY -u scripts/CITY_w9_run.py $M scripts/CITY_sl_runw4.py scripts/CITY_w13_modes.py scripts/CITY_m4s_tsi_eval.py "$@" --seeds $SS $SM --tag $T --out $OUT >> $OUT/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $1; }
J=$D/tune_jobs.txt; : > $J
for X in "" _P5; do M=none; [ -z "$X" ] || M=$P5; echo "R$X $M - --tk none --light RLW:$L11 --fleet GLOSAL:0.3" >> $J
  for ab in "1 0" "1.5 0" "2 0" "1 0.25" "1.5 0.25" "2 0.25" "1 0.5" "1.5 0.5" "2 0.5"; do set -- $ab; T=$(echo "T_a$1_b$2" | tr '.' 'p')
    echo "${T}$X $M 0.5 --tk $TK --light RLWQ:$L11:$1:$2 --fleet GLOSAL:0.3" >> $J; echo "${T}_q01$X $M 0.1 --tk $TK --light RLWQ:$L11:$1:$2 --fleet GLOSAL:0.3" >> $J; done; done
run_jobs $J $D/tune "$TU4" || { echo "tuning failure: stop"; exit 1; }
SL_SMOKE=${SMOKE:-0} $PY scripts/CITY_sl_tsi_report.py select $D || { echo "selection FAIL: stop"; exit 1; }
read UA UB UQ <<< "$($PY -c "import json; c=json.load(open('$D/tune/choice.json'))['choice'].split(','); print(c[0], c[1], c[2])")"
# 4. confirmation (deployed fleets) incl. M2 arms
J=$D/conf_jobs.txt; : > $J
for s in $FS; do P="PL:$FLD/L11_sl_s${s}_fleet.pt"
  for X in "" P5; do M=none; [ -z "$X" ] || M=$P5
    echo "OFF${X}_t11_s$s $M - --tk none --light RLW:$L11 --fleet L-ACT:0 --guard always" >> $J
    echo "R${X}_t11_s$s $M - --tk none --light RLW:$L11 --fleet $P" >> $J
    echo "HARM${X}_t11_s$s $M - --tk fk:0.5:$D/prov/ft.json --light RLW:$L11 --fleet $P" >> $J
    echo "TG${X}_t11_s$s $M 0.1 --tk $TK --light RLWQ:$L11:1:0.25 --fleet $P" >> $J
    echo "TU${X}_t11_s$s $M $UQ --tk $TK --light RLWQ:$L11:$UA:$UB --fleet $P" >> $J; done; done
run_jobs $J $D/conf "$CS" || { echo "confirmation failure: stop"; exit 1; }
SL_SMOKE=${SMOKE:-0} $PY scripts/CITY_sl_tsi_report.py report $D || { echo "report FAIL"; exit 1; }
echo "F1-SL-TSI done $(date)"
