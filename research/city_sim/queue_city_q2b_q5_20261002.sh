#!/usr/bin/env bash
# City queue (02/10/2026 19:3x; user 19:3x "cho Q2b chạy trước Q5"): Q2b, then Q5 (Q5's first start was stopped at 19:3x and
# archived at legacy/city_sim_q5_stopped_20261002/).
cd /Users/phanan/cig-amf-main
echo "Q2b start $(date)"; nice -n 12 external_envs/city_runtime/bin/python -u scripts/CITY_q2b_eco_robustness.py --out research/city_sim/q2b_eco_robustness_20261002 --workers 3 > research/city_sim/q2b_eco_robustness_20261002.log 2>&1
echo "Q2b end $(date)"; grep -v "^\[" research/city_sim/q2b_eco_robustness_20261002.log | cut -c1-400
echo "Q5 start $(date)"; nice -n 12 external_envs/runtime/bin/python -u scripts/CITY_q5_commitment.py --out research/city_sim/q5_commitment_20261002 --workers 2 > research/city_sim/q5_commitment_20261002.log 2>&1
echo "Q5 end $(date)"; grep -E "tuning|demand|P5" research/city_sim/q5_commitment_20261002.log | cut -c1-600
