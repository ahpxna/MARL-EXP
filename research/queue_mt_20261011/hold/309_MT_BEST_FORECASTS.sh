#!/usr/bin/env bash
# MT-A6 tests, days 0-4 (teleports 300): lights + fleets with Midtown-fitted forecasts.  6 lanes.
#   MTR_BGF_t<k>_s<f>      grid lights + grid fleets, forecast re-fitted on Midtown (no AI retrained: the interface-only arm)
#   MTR_BMM_a4_t<k>_s<f>   A4 lights + Midtown fleets, their own forecast
#   MTR_BMM_ft_t<k>_s<f>   A5-ft lights + Midtown fleets, their own forecast
set -u; cd /Users/phanan/cig-amf-main
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=osm
PY=external_envs/city_runtime/bin/python; E5=research/city_sim/midtown_transfer_20261010/eval5; R=research/city_sim/midtown_transfer_20261010/retrain
F3=research/city_sim/w15_20261007/fresh3/fleets; J=$E5/jobs_309.txt; : > $J
for k in 59 60 61 62 63; do for f in 1413 1513 1613 1713; do
  echo "MTR_BGF_t${k}_s$f|research/city_sim/w19_20261008/lights|$R/forecast_grid|$F3/L11_s${f}_fleet.pt|$k" >> $J
  echo "MTR_BMM_a4_t${k}_s$f|$R/lights_a4|$R/forecast_a4|$R/fleets/MT${f}_fleet.pt|$k" >> $J
  echo "MTR_BMM_ft_t${k}_s$f|$R/moe_ft|$R/forecast_ft|$R/fleets/MT${f}_fleet.pt|$k" >> $J
done; done
while IFS='|' read -r tag L FC FL k; do test -f $FC/cmodel/n2_k$k.pt && test -f $FL || { echo "MISSING input for $tag"; exit 1; }; done < $J
echo "tests start $(date): $(wc -l < $J) jobs"
cat $J | xargs -P 6 -S 8192 -I{} bash -c 'IFS="|" read -r tag L FC FL k <<< "{}"; W19_LIGHTS=$L nice -n 5 '"$PY"' -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py scripts/CITY_eval_n4.py --n4 0.1:hyb:$FC/prep/prov_rlh${k}_cl.json:$FC/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:$FL --seeds 0 1 2 3 4 --tag $tag --out '"$E5"' > '"$E5"'/$tag.log 2>&1 || echo "FAIL $tag"'
bad=0; while IFS='|' read -r tag _; do grep -q '"status": "COMPLETE"' $E5/$tag.json 2>/dev/null || { echo "INCOMPLETE $tag"; bad=1; }; done < $J
$PY scripts/MT_report.py; echo "job done $(date)"; exit $bad
