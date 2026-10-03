#!/usr/bin/env bash
# City queue (02/10/2026 19:0x): Q3 after Q2 (PLAN_CITY_IDEAS_20261002.md); waits on the Q2 process without polling.
cd /Users/phanan/cig-amf-main
echo "wait Q2 pid 23571 $(date)"; caffeinate -i -w 23571 2>/dev/null
echo "Q3 start $(date)"; nice -n 12 external_envs/city_runtime/bin/python -u scripts/CITY_q3_info_fd.py --out research/city_sim/q3_info_fd_20261002 --workers 2 > research/city_sim/q3_info_fd_20261002.log 2>&1
echo "Q3 end $(date)"; tail -12 research/city_sim/q3_info_fd_20261002.log
