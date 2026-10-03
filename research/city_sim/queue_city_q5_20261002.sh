#!/usr/bin/env bash
# City queue (02/10/2026 19:2x): Q5 after the Q3 queue step (PLAN_CITY_IDEAS_20261002.md); waits on its process, no polling.
cd /Users/phanan/cig-amf-main
echo "wait Q3 queue pid 23960 $(date)"; caffeinate -i -w 23960 2>/dev/null
echo "Q5 start $(date)"; nice -n 12 external_envs/runtime/bin/python -u scripts/CITY_q5_commitment.py --out research/city_sim/q5_commitment_20261002 --workers 2 > research/city_sim/q5_commitment_20261002.log 2>&1
echo "Q5 end $(date)"; grep -E "tuning|demand|P5" research/city_sim/q5_commitment_20261002.log | cut -c1-600
