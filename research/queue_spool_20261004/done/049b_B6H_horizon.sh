# 049b B6-H (PROTOCOL_CITY_B6 §B6-H, registered 09:13 04/10): trainer v7, 480 episodes, DQN seeds 13 / 113 vs ACT:
#   R3h cotv/release/trip, R5a v3/release/approach, R5h v3/release/trip; horizon trace check first (refuses to train on FAIL);
#   eval4 SELECT 100-104 under ACT with always-SUMO (049h); report H-1..H-3 (+ σ-family from 049a).
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; O=research/city_sim/fleet_upgrade_20261004; W=research/city_sim/wave2_20261004
$PY scripts/CITY_v7_horizon_check.py || { echo "horizon check FAIL: B6-H not trained"; exit 1; }
{ for A in "cotv trip R3h" "v3 approach R5a" "v3 trip R5h"; do set -- $A; for t in 0 1; do echo "$1 $2 $((13 + 100 * t)) L-ACT-${3}_t$t"; done; done; } |
  xargs -P 6 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_fleet_train_v7.py --reward $0 --actions release --horizon $1 --fleet-seed $2 --name $3 --episodes 480 --out '"$O"' > '"$O"'/$3.out 2>&1 || echo "FAIL $3"'
mkdir -p $W/049h/tmp
{ for R in R3h R5a R5h; do for t in 0 1; do echo "--light ACT --fleet U:L-ACT-${R}_t$t --seeds 100 101 102 103 104 --tag U-L-ACT-${R}_t${t}_ACT"; done; done
  echo "--light ACT --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag OFF_ACT"; } | LANES=4 bash scripts/SPOOL_eval4_run.sh $W/049h
$PY scripts/CITY_b6sh_report.py sigma horizon
