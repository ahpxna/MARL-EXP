# 021 reward-v2 correctness trace, full horizon (Amendment W3 §4): FT (teleports) and RL-H_0, ACT; random commands; seeds 100-101
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; mkdir -p research/city_sim/wave2_20261004/021
external_envs/city_runtime/bin/python -u scripts/CITY_v2_trace_check.py --lights FT RL-H:0 ACT --seeds 100 101 --end 5400 --out research/city_sim/wave2_20261004/021/v2_trace.json
