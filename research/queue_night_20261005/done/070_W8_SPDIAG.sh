#!/usr/bin/env bash
# W8-1 SPDIAG (PROTOCOL_CITY_WAVE8_20261005): D2 forecast-error runs (HYBK with feature logs), D3 oracle headroom (record R, replay with exact
# future vs sigma*), D4 service masked to 2- / 3-green signals; D1 offline; report.  SMOKE=1: one seed, 600 s, light 11 only.
set -o pipefail
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
D=${W8_DIR:-research/city_sim/w8_20261005/spdiag}; mkdir -p $D/d2 $D/d3 $D/d4 $D/check; export XPLAY_TMP=$PWD/$D/check
SP=research/city_sim/m4_20261004/spider; M=research/city_sim/sptsi_20261005/model; CH=research/city_sim/sptsi_20261005/tune/choice.json
EV="$PY -u scripts/CITY_m4s_tsi_eval.py"; EVM="$PY -u scripts/CITY_w8_spmask_eval.py"; ORC="$PY -u scripts/CITY_m4s_run.py scripts/CITY_m3_headroom.py"; echo "W8-SPDIAG start $(date)"
if [ "${SMOKE:-0}" = 1 ]; then SM="--smoke"; LK="11"; S2="1100"; S34="1100"; else SM=""; LK="11 111"; S2="1100 1101"; S34="1100 1101 1102 1103"; fi
export PY D SP M SM EV EVM ORC
J=$D/jobs.txt; : > $J
for k in $LK; do TK="n2k:$SP/s3b/prov/fkcl_rlk$k.json:$M/n2k_sp$k.pt"; AB=$($PY -c "import json;print(json.load(open('$CH'))['$k']['choice'].replace(',',':'))")
  for s in $S2; do echo "d2 D2_${k}_s$s $s $EV --tk $TK --featlog $D/d2/fl_${k}_s$s --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J; done
  echo "d3 REC_$k all $EV --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3 --record $D/d3/rec_$k/phases_s{seed}.npz" >> $J
  echo "d4 R_$k all $EV --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J
  echo "d4 FULL_$k all $EV --tk $TK --light RLKQ:$SP/RLK_sp$k.pt:$AB --fleet GLOSAL:0.3" >> $J
  echo "d4 K2ONLY_$k all $EVM --mask k2 --tk $TK --light RLKQ:$SP/RLK_sp$k.pt:$AB --fleet GLOSAL:0.3" >> $J
  echo "d4 K3ONLY_$k all $EVM --mask k3 --tk $TK --light RLKQ:$SP/RLK_sp$k.pt:$AB --fleet GLOSAL:0.3" >> $J; done
for k in $LK; do mkdir -p $D/d3/rec_$k; done
export S34; xargs -P 6 -L 1 bash -c 'O=$0; T=$1; S=$2; shift 2; [ "$S" = all ] && S="$S34"; [ -f $D/$O/$T.json ] || nice -n 5 "$@" --seeds $S $SM --tag $T --out $D/$O >> $D/$O/run.log 2>&1 || { echo "FAIL $T"; exit 255; }' < $J || { echo "diagnostic runs failed: stop"; exit 1; }
# D3: replay with exact future (oracle) and with no SPaT (sigma*) on the recorded R schedule
for k in $LK; do [ -f $D/d3/ORC_$k.json ] || nice -n 5 $ORC --replay-dir $D/d3/rec_$k --fleet GLOSAL:0.3 --seeds $S34 $SM --tag ORC_$k --out $D/d3 >> $D/d3/run.log 2>&1 &
  [ -f $D/d3/SIG_$k.json ] || nice -n 5 $EV --tk none --replay-dir $D/d3/rec_$k --fleet GLOSAL:0.3 --seeds $S34 $SM --tag SIG_$k --out $D/d3 >> $D/d3/run.log 2>&1 & done; wait
for k in $LK; do for a in ORC SIG; do [ -f $D/d3/${a}_$k.json ] || { echo "D3 run missing ${a}_$k: stop"; exit 1; }; done; done
$PY scripts/CITY_w8_spdiag.py $D || exit 1; echo "W8-SPDIAG done $(date)"
