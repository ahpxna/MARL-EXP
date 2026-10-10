# 034 reward-v3 correctness trace, full horizon (PROTOCOL_CITY_B6 Amendment B6-A1 §2): ACT, FT (teleports), RL-H_0; random commands; seeds 100-101
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; O=research/city_sim/wave2_20261004/034; mkdir -p $O/tmp; export XPLAY_TMP=$PWD/$O/tmp
external_envs/city_runtime/bin/python -u scripts/CITY_v3_trace_check.py --lights ACT FT RL-H:0 --seeds 100 101 --end 5400 --out $O/v3_trace.json
