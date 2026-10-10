# 035 B6 v3 fleets — research/city_sim/PROTOCOL_CITY_B6_BENEFICIAL_FLEET_20261004.md
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; O=research/city_sim/fleet_upgrade_20261004
for f in research/city_sim/wave2_20261004/021/v2_trace.json research/city_sim/wave2_20261004/034/v3_trace.json; do
  grep -q '"verdict": "PASS"' $f 2>/dev/null || { echo "GATE: $f is not PASS -> no v3 training (B6-A1 §2)"; exit 1; }; done
printf '%s\n' "13 L-ACT-v3_t0" "113 L-ACT-v3_t1" | xargs -P 2 -L 1 sh -c 'nice -n 5 external_envs/city_runtime/bin/python -u scripts/CITY_fleet_train_v3.py --against ACT --episodes 120 --fleet-seed $0 --name $1 --out '"$O"' > '"$O"'/$1.out 2>&1 || echo "FAIL $1"'
