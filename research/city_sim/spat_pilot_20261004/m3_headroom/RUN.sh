#!/usr/bin/env bash
# M3 headroom diagnostic (ORACLE): replayed RL-H:k schedules (σ* runs, SELECT 100-104); σ* replay (self-check vs the recorded run) and the
# frozen fleets with oracle SPaT of the replayed schedule.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; P=research/city_sim/spat_pilot_20261004; H=$P/m3_headroom; export XPLAY_TMP=$PWD/$H/tmp
for k in 0 1 2 3; do R=$H/replay_rlh$k; S="100 101 102 103 104"
  nice -n 5 $PY -u scripts/CITY_eval4_sigma.py --sigma 0.3 --light FT --fleet L-ACT:0 --guard always --replay-dir $R --seeds $S --tag S03_rep$k --out $H >> $H/run.log 2>&1 &
  nice -n 5 $PY -u scripts/CITY_m3_headroom.py --light FT --replay-dir $R --fleet ESLD:$P/lane_d/theta_s$((k+2)).json --seeds $S --tag F0a_orc$k --out $H >> $H/run.log 2>&1 &
  nice -n 5 $PY -u scripts/CITY_m3_headroom.py --light FT --replay-dir $R --fleet PL:$P/fleets_v11/L11_s$((213+100*k))_fleet.pt --seeds $S --tag F0b_orc$k --out $H >> $H/run.log 2>&1 &
done; wait; echo "headroom done $(date)"
