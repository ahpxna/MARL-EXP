#!/usr/bin/env bash
# SPIDER-TSI (PROTOCOL_CITY_SPIDER_TSI_20261005): seeds -> smoke -> collection -> fit -> KS-1 / KS-2 -> per-light tuning -> confirmation -> report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/sptsi_20261005; export XPLAY_TMP=$PWD/$D/check
SP=research/city_sim/m4_20261004/spider; G=research/city_sim/demand/spider/p2.0; RT=external_envs/city_runtime/lib/python3.12/site-packages/sumo/tools/randomTrips.py; EV="$PY -u scripts/CITY_m4s_tsi_eval.py"
echo "SPTSI start $(date)"
gen() { F=$1; shift; if [ ! -f $G/$F ]; then for s in "$@"; do [ -f $G/rou_s$s.xml ] && { echo "KS-0 FAIL: rou_s$s existed"; exit 1; }; done
  for s in "$@"; do $PY $RT -n research/city_sim/net/spider.net.xml -o $G/trips_s$s.xml -r $G/rou_s$s.xml --prefix v --vehicle-class passenger --fringe-factor 10 --seed $s --min-distance 300 --period 2.0 > /dev/null 2>&1 || { echo "GEN FAIL $s"; exit 1; }; done; date > $G/$F; fi; }
gen TUNE1100_generated 1100 1101 1102 1103; gen CONF1110_generated $(seq 1110 1129); echo "seeds ready $(date)"
$EV --tk fk:0.1:$SP/s3b/prov/fkcl_rlk11.json --light RLK:$SP/RLK_sp11.pt --fleet GLOSAL:0.3 --featlog $D/check/smk0 --seeds 0 --smoke --tag SMK0 --out $D/check > $D/check/smk0.log 2>&1 || { echo "SMOKE0 FAIL"; tail -8 $D/check/smk0.log; exit 1; }
J=$D/collect.txt; : > $J; for k in 11 111; do for s in 0 1 2 3 4 5 6 7; do echo "$k $s" >> $J; done; done
export PY D SP EV; xargs -P 4 -L 1 bash -c '[ -f $D/data/k$0/feat_s$1.npz ] || nice -n 5 $EV --tk fk:0.1:$SP/s3b/prov/fkcl_rlk$0.json --light RLK:$SP/RLK_sp$0.pt --fleet GLOSAL:0.3 --featlog $D/data/k$0 --seeds $1 --tag C_k$0_s$1 --out $D/data/k$0 >> $D/data/run.log 2>&1 || echo "FAIL collect $0 $1"' < $J
for k in 11 111; do [ "$(ls $D/data/k$k/feat_s*.npz 2>/dev/null | wc -l)" -eq 8 ] || { echo "collection incomplete k$k"; exit 1; }; done; echo "collected $(date)"
for k in 11 111; do $PY -u scripts/CITY_n2k.py fit $D/data/k$k $D/model/n2k_sp$k.pt > $D/model/fit_k$k.log 2>&1 & done; wait; tail -1 $D/model/fit_k11.log | cut -c1-200
for k in 11 111; do [ -f $D/model/n2k_sp$k.pt ] || { echo "fit FAIL k$k"; exit 1; }; done
TK11="n2k:$SP/s3b/prov/fkcl_rlk11.json:$D/model/n2k_sp11.pt"
$EV --tk $TK11 --light RLKQ:$SP/RLK_sp11.pt:2:0 --fleet GLOSAL:0.3 --featlog $D/check/ks1 --seeds 0 --smoke --tag KS1 --out $D/check > $D/check/ks1.log 2>&1 || { echo "KS1 run FAIL"; tail -8 $D/check/ks1.log; exit 1; }
$PY scripts/CITY_n2k.py parity $D/check/ks1 0 $D/model/n2k_sp11.pt | tee $D/check/ks1_parity.txt || { echo "KS-1 FAIL: stop"; exit 1; }
$PY -c "import json;x=json.load(open('$D/check/KS1_tk.json'));p=x['provider'];print('KS-2', p);raise SystemExit(0 if p['n2k']>0 and p['fk_direct']>0 else 1)" || { echo "KS-2 FAIL"; exit 1; }
J=$D/tune_jobs.txt; : > $J
for k in 11 111; do TK="n2k:$SP/s3b/prov/fkcl_rlk$k.json:$D/model/n2k_sp$k.pt"; echo "R_$k --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J
  for ab in "0 0" "1 0" "2 0" "1 0.25" "1.5 0.25" "1 0.5" "2 0.5"; do set -- $ab; T=$(echo "T_${k}_a$1_b$2" | tr '.' 'p'); echo "$T --tk $TK --light RLKQ:$SP/RLK_sp$k.pt:$1:$2 --fleet GLOSAL:0.3" >> $J; done; done
xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/tune/$T.json ] || nice -n 5 $EV "$@" --seeds 1100 1101 1102 1103 --tag $T --out $D/tune >> $D/tune/run.log 2>&1 || echo "FAIL $T"' < $J
$PY scripts/CITY_sptsi_tune.py | tee $D/tune/tune.txt || { echo "TUNE FAIL"; exit 1; }
J=$D/conf_jobs.txt; : > $J
for k in 11 111; do AB=$($PY -c "import json;print(json.load(open('$D/tune/choice.json'))['$k']['choice'].replace(',',':'))"); TK="n2k:$SP/s3b/prov/fkcl_rlk$k.json:$D/model/n2k_sp$k.pt"
  echo "R_$k --tk none --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J; echo "TSIK_$k --tk $TK --light RLKQ:$SP/RLK_sp$k.pt:$AB --fleet GLOSAL:0.3" >> $J
  echo "HYBK_$k --tk $TK --light RLK:$SP/RLK_sp$k.pt --fleet GLOSAL:0.3" >> $J; echo "ADPK_$k --tk none --light RLKQ:$SP/RLK_sp$k.pt:$AB --fleet GLOSAL:0.3" >> $J; done
export SS="$(seq -s ' ' 1110 1129)"; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/conf/$T.json ] || nice -n 5 $EV "$@" --seeds $SS --tag $T --out $D/conf >> $D/conf/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; $PY scripts/CITY_sptsi_report.py; echo "SPTSI done $(date)"
