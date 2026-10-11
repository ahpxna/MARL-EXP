#!/usr/bin/env bash
# MT-A5 fleet job (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010): the four Midtown-trained fleets (MT-A3, retrain/fleets/MT<seed>_fleet.pt) vs the
# grid fleets on test days 0-4: under FT with exact SPaT (MTR_FM / MTR_FG), and with the grid lights t59-63 + the adapted forecast (MTR_BM;
# MTR_BG already ran in phase 1).  6 lanes.  Fails if a Midtown fleet checkpoint is missing (no waiting).
set -u; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=osm
PY=external_envs/city_runtime/bin/python; E5=research/city_sim/midtown_transfer_20261010/eval5; MF=research/city_sim/midtown_transfer_20261010/retrain/fleets
F3=research/city_sim/w15_20261007/fresh3/fleets; W19=research/city_sim/w19_20261008
for s in 1413 1513 1613 1713; do test -f $MF/MT${s}_fleet.pt || { echo "MISSING Midtown fleet MT$s"; exit 1; }; done
J=$E5/jobs_306.txt; : > $J
for s in 1413 1513 1613 1713; do
  echo "MTR_FM_s$s|scripts/CITY_eval6_v11.py --light FT --fleet PL:$MF/MT${s}_fleet.pt" >> $J
  echo "MTR_FG_s$s|scripts/CITY_eval6_v11.py --light FT --fleet PL:$F3/L11_s${s}_fleet.pt" >> $J
done
for k in 59 60 61 62 63; do for s in 1413 1513 1613 1713; do
  echo "MTR_BM_t${k}_s$s|scripts/CITY_eval_n4.py --n4 0.1:hyb:$W19/prep/prov_rlh${k}_cl.json:$W19/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:$MF/MT${s}_fleet.pt" >> $J
done; done
echo "fleet tests start $(date): $(wc -l < $J) jobs"
cat $J | xargs -P 6 -S 8192 -I{} bash -c 'line="{}"; tag=${line%%|*}; cmd=${line#*|}; nice -n 5 '"$PY"' -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py $cmd --seeds 0 1 2 3 4 --tag $tag --out '"$E5"' > '"$E5"'/$tag.log 2>&1 || echo "FAIL $tag"'
bad=0; while IFS='|' read -r tag _; do grep -q '"status": "COMPLETE"' $E5/$tag.json 2>/dev/null || { echo "INCOMPLETE $tag"; bad=1; }; done < $J
$PY scripts/MT_report.py; echo "job done $(date)"; exit $bad
