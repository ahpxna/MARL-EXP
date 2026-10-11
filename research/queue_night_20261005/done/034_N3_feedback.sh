#!/usr/bin/env bash
# N3 (PROTOCOL_CITY_N3_FEEDBACK_20261005): (a) pub / shadow DEV 8 jobs; (b) collection 16 TRAIN runs -> refit -> DEV 4 jobs; report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/n3_20261005; export XPLAY_TMP=$PWD/$D/check
P=research/city_sim/spat_pilot_20261004/fleets_v11; M=research/city_sim/n2_20261005/model; echo "N3 start $(date)"
$PY -u scripts/CITY_eval_n3.py --n3 0.5:shadow:$M/n2_k0.pt --light RL-H:0 --fleet PL:$P/L11_s13_fleet.pt --seeds 600 --smoke --tag SMK --out $D/check > $D/check/smoke.log 2>&1 || { echo "SMOKE FAIL"; tail -6 $D/check/smoke.log; exit 1; }
$PY -c "import json;x=json.load(open('$D/check/SMK_n3.json'))['runs'][0];print('smoke n3', x['ttg']['n'], x['ttg']['mae'], x['ttr']['n'], x['ttr']['mae'], 'cens', x['censored'])"
J=$D/collect.txt; : > $J; for k in 0 1; do F=s13; [ $k = 1 ] && F=s113; for s in 0 1 2 3 4 5 6 7; do echo "$k $F $s" >> $J; done; done
export PY D P M; xargs -P 4 -L 1 bash -c '[ -f $D/data/k$0/feat_s$2.npz ] || nice -n 5 $PY -u scripts/CITY_eval_n3.py --n3 0.5:pub:$M/n2_k$0.pt --featlog $D/data/k$0 --light RL-H:$0 --fleet PL:$P/L11_$1_fleet.pt --seeds $2 --tag C_k$0_s$2 --out $D/data/k$0 >> $D/data/run.log 2>&1 || echo "FAIL collect $0 $2"' < $J
for k in 0 1; do [ "$(ls $D/data/k$k/feat_s*.npz | wc -l)" -eq 8 ] || { echo "collection incomplete k$k"; exit 1; }; done; echo "collected $(date)"
for k in 0 1; do $PY -u scripts/CITY_n2_fit.py $k $D/data/k$k $D/model > $D/model/fit_k$k.log 2>&1 & done; wait; ls $D/model/
J=$D/jobs.txt; : > $J
for k in 0 1; do for fl in s13 s113; do F="--light RL-H:$k --fleet PL:$P/L11_${fl}_fleet.pt"
  echo "N3pub_k${k}_${fl} --n3 0.5:pub:$M/n2_k$k.pt $F" >> $J; echo "N3sh_k${k}_${fl} --n3 0.5:shadow:$M/n2_k$k.pt $F" >> $J
  echo "N3ref_k${k}_${fl} --n3 0.5:pub:$D/model/n2_k$k.pt $F" >> $J; echo "N3refsh_k${k}_${fl} --n3 0.5:shadow:$D/model/n2_k$k.pt $F" >> $J; done; done
export SS="600 601 602 603 604 605 606 607 608 609 610 611"; xargs -P 4 -L 1 bash -c 'T=$0; [ -f $D/dev/$T.json ] || nice -n 5 $PY -u scripts/CITY_eval_n3.py "$@" --seeds $SS --tag $T --out $D/dev >> $D/dev/run.log 2>&1 || echo "FAIL $T"' < $J
echo "panel done $(date)"; $PY scripts/CITY_n3_report.py; echo "N3 done $(date)"
