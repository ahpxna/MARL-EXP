#!/usr/bin/env bash
# MT-E (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010): full map, AI on the 511 two-green signals and the city's actuated programs on the other 56
# (MT_BASE=actrest), days 0-4, 6 lanes: MTF_LGar_t<k> (LIGHT-grid) and MTF_BGar_t<k>_s<f> (grid lights + grid fleets, adapted forecast).
set -u; cd "$(dirname "$0")/.."
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=actrest MT_NET=midtown_full
PY=external_envs/city_runtime/bin/python; E=research/city_sim/midtown_transfer_20261010/eval_full
W19=research/city_sim/w19_20261008; F3=research/city_sim/w15_20261007/fresh3/fleets; J=$E/jobs_actrest.txt; : > $J
for k in 59 60 61 62 63; do
  echo "MTF_LGar_t$k|scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always" >> $J
  for f in 1413 1513 1613 1713; do
    echo "MTF_BGar_t${k}_s$f|scripts/CITY_eval_n4.py --n4 0.1:hyb:$W19/prep/prov_rlh${k}_cl.json:$W19/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:$F3/L11_s${f}_fleet.pt" >> $J
  done
done
echo "MT-E start $(date): $(wc -l < $J) jobs"
cat $J | xargs -P 6 -S 8192 -I{} zsh -c 'IFS="|" read -r tag cmd <<< "{}"; nice -n 5 '"$PY"' -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py ${=cmd} --seeds 0 1 2 3 4 --tag $tag --out '"$E"' > '"$E"'/$tag.log 2>&1 || echo "FAIL $tag"'
bad=0; while IFS='|' read -r tag _; do grep -q '"status": "COMPLETE"' $E/$tag.json 2>/dev/null || { echo "INCOMPLETE $tag"; bad=1; }; done < $J
MT_EVAL_DIR=$E MT_TAG_PREFIX=MTF $PY scripts/MT_report.py research/city_sim/midtown_transfer_20261010/report_mt_full.txt
echo "MT-E done $(date)"; exit $bad
