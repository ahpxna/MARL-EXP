#!/usr/bin/env bash
# MT-D (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010): learned lights with a 50 s maximum green (actuated maxDur), days 0-4, 6 lanes.
#   full map: MTF_LGc_t<k> (LIGHT-grid), MTF_BGc_t<k>_s<f> (grid lights + grid fleets, adapted forecast); old map: MTR_LGc_t<k>.
set -u; cd "$(dirname "$0")/.."
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=osm MT_MAX_G=50
PY=external_envs/city_runtime/bin/python; EF=research/city_sim/midtown_transfer_20261010/eval_full; E5=research/city_sim/midtown_transfer_20261010/eval5
W19=research/city_sim/w19_20261008; F3=research/city_sim/w15_20261007/fresh3/fleets; J=$EF/jobs_cap.txt; : > $J
for k in 59 60 61 62 63; do
  echo "MTF_LGc_t$k|midtown_full|$EF|scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always" >> $J
  echo "MTR_LGc_t$k|midtown|$E5|scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always" >> $J
  for f in 1413 1513 1613 1713; do
    echo "MTF_BGc_t${k}_s$f|midtown_full|$EF|scripts/CITY_eval_n4.py --n4 0.1:hyb:$W19/prep/prov_rlh${k}_cl.json:$W19/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:$F3/L11_s${f}_fleet.pt" >> $J
  done
done
echo "MT-D start $(date): $(wc -l < $J) jobs"
cat $J | xargs -P 6 -S 8192 -I{} zsh -c 'IFS="|" read -r tag net out cmd <<< "{}"; MT_NET=$net nice -n 5 '"$PY"' -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py ${=cmd} --seeds 0 1 2 3 4 --tag $tag --out $out > $out/$tag.log 2>&1 || echo "FAIL $tag"'
bad=0; while IFS='|' read -r tag net out _; do grep -q '"status": "COMPLETE"' $out/$tag.json 2>/dev/null || { echo "INCOMPLETE $tag"; bad=1; }; done < $J
echo "MT-D done $(date)"; exit $bad
