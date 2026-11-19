#!/usr/bin/env bash
# MT-A6: SPaT forecasters fitted on Midtown TRAINING traffic (scripts/RUN_mt_forecast.sh) for (i) the grid lights t59-63 unchanged (interface
# re-calibration only), (ii) the A4 lights, (iii) the A5-ft lights.  5 lanes per set.
set -u; cd /Users/phanan/cig-amf-main; R=research/city_sim/midtown_transfer_20261010/retrain; KS="59 60 61 62 63"
for k in $KS; do test -f $R/lights_a4/RL-H_t$k.pt && test -f $R/moe_ft/RL-H_t$k.pt || { echo "MISSING A4/ft light t$k"; exit 1; }; done
scripts/RUN_mt_forecast.sh research/city_sim/w19_20261008/lights $R/forecast_grid "$KS" 5 || exit 1
scripts/RUN_mt_forecast.sh $R/lights_a4 $R/forecast_a4 "$KS" 5 || exit 1
scripts/RUN_mt_forecast.sh $R/moe_ft $R/forecast_ft "$KS" 5 || exit 1
echo "job done $(date)"
