# 050r B6-R5 (PROTOCOL_CITY_B6 §B6-R5, registered 09:39 04/10): replicate R5h (v7, v3 / release / trip, 480 episodes, vs ACT) on new DQN
# seeds 213 / 313 / 413 / 513 (t2..t5); evaluate on FRESH traffic 410-419 under ACT with always-SUMO, the σ-family (0..0.4) and t0 / t1.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; O=research/city_sim/fleet_upgrade_20261004; W=research/city_sim/wave2_20261004
$PY scripts/CITY_v7_horizon_check.py || { echo "horizon check FAIL: not trained"; exit 1; }
printf '%s\n' "213 L-ACT-R5h_t2" "313 L-ACT-R5h_t3" "413 L-ACT-R5h_t4" "513 L-ACT-R5h_t5" |
  xargs -P 4 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_fleet_train_v7.py --reward v3 --actions release --horizon trip --fleet-seed $0 --name $1 --episodes 480 --out '"$O"' > '"$O"'/$1.out 2>&1 || echo "FAIL $1"'
mkdir -p $W/050r/tmp; T="410 411 412 413 414 415 416 417 418 419"
{ for t in 0 1 2 3 4 5; do echo "--light ACT --fleet U:L-ACT-R5h_t$t --seeds $T --tag U-L-ACT-R5h_t${t}_ACT"; done
  echo "--light ACT --fleet L-ACT:0 --guard always --seeds $T --tag OFF_ACT"; } | LANES=4 bash scripts/SPOOL_eval4_run.sh $W/050r
printf '%s\n' 0.0 0.1 0.2 0.3 0.4 | xargs -P 5 -L 1 sh -c 'XPLAY_TMP=$PWD/'"$W"'/050r/tmp nice -n 5 '"$PY"' -u scripts/CITY_eval4_sigma.py --sigma $0 --light ACT --fleet L-ACT:0 --guard always --seeds '"$T"' --tag S$0_ACT --out '"$W"'/050r >> '"$W"'/050r/run.log 2>&1 || echo "FAIL sigma $0"'
$PY scripts/CITY_b6r5_report.py
