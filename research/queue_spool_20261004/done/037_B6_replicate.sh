# 037 B6-2 recipe confirmation (PROTOCOL_CITY_B6 Amendment B6-A1 §4): only recipes with >= 1 passing seed in the B6-1 screen;
# new policy seeds t2 / t3 (DQN 213 / 313), fresh traffic 400-409, always-SUMO comparator on the same traffic.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; O=research/city_sim/fleet_upgrade_20261004; W=research/city_sim/wave2_20261004
$PY scripts/CITY_wave2_report_v2.py b6 > /dev/null || exit 1
R=$($PY -c "import json; v=json.load(open('$W/036/b6_verdicts.json')); print(' '.join(sorted({k.rsplit('_t', 1)[0] for k, x in v.items() if x})))")
echo "B6-1 passing recipes: [$R]"; [ -z "$R" ] && { echo "no recipe passed B6-1: B6-2 not run (registered)"; exit 0; }
for rec in $R; do for t in 2 3; do
  case $rec in
    U-L-ACT-v2) echo "--mode new --against ACT --reward v2 --episodes 120 --fleet-seed $((13 + 100 * t)) --name L-ACT-v2_t$t" ;;
    U-L-ACT-v3) echo "V3 $((13 + 100 * t)) L-ACT-v3_t$t" ;;
  esac; done; done | xargs -P 2 -L 1 sh -c 'if [ "$0" = V3 ]; then nice -n 5 '"$PY"' -u scripts/CITY_fleet_train_v3.py --against ACT --episodes 120 --fleet-seed $1 --name $2 --out '"$O"' > '"$O"'/$2.out 2>&1 || echo "FAIL $2";
  else n=$(echo "$0 $@" | sed "s/.*--name //"); nice -n 5 '"$PY"' -u scripts/CITY_fleet_upgrade.py "$0" "$@" --out '"$O"' > '"$O"'/$n.out 2>&1 || echo "FAIL $n"; fi'
{ for rec in $R; do for t in 2 3; do F=U:${rec#U-}_t$t; echo "--light ACT --fleet $F --seeds 400 401 402 403 404 405 406 407 408 409 --tag $(echo ${F}_ACT | tr ':' '-')"; done; done
  echo "--light ACT --fleet L-ACT:0 --guard always --seeds 400 401 402 403 404 405 406 407 408 409 --tag OFF_ACT"; } | bash scripts/SPOOL_eval3_run.sh $W/037
$PY scripts/CITY_wave2_report_v2.py b6c
$PY scripts/CITY_make_alstar_jobs.py
