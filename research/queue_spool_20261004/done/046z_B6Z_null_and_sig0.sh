# 046z B6-Z baseline reproducibility (PROTOCOL_CITY_B6 §B6-Z + amendment Z-4, registered 09:00 / 09:03 04/10): null fleets Z-rel / Z-res0 /
# Z-hold and always-SUMO on SELECT 100-104 (eval4), and the perfect-driver comparator Z-sig0 (eval4_sig0: SUMO, sigma 0) on SELECT and on
# the B6-T traffic 400-409 (046z/T).  No training.  Reporter scripts/CITY_b6z_report.py (written before the run).
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; W=research/city_sim/wave2_20261004
[ -f research/city_sim/fleet_upgrade_20261004/Z-rel_fleet.pt ] || $PY scripts/CITY_make_null_fleets.py
mkdir -p $W/046z/tmp $W/046z/T/tmp
{ for z in Z-rel Z-res0 Z-hold; do echo "--light ACT --fleet U:$z --seeds 100 101 102 103 104 --tag ${z}_ACT"; done
  echo "--light ACT --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag OFF_ACT"; } | LANES=4 bash scripts/SPOOL_eval4_run.sh $W/046z
( export XPLAY_TMP=$PWD/$W/046z/tmp; nice -n 5 $PY -u scripts/CITY_eval4_sig0.py --light ACT --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag Z-sig0_ACT --out $W/046z >> $W/046z/run.log 2>&1 || echo "FAIL sig0 SELECT" ) &
( export XPLAY_TMP=$PWD/$W/046z/T/tmp; nice -n 5 $PY -u scripts/CITY_eval4_sig0.py --light ACT --fleet L-ACT:0 --guard always --seeds 400 401 402 403 404 405 406 407 408 409 --tag Z-sig0_ACT --out $W/046z/T >> $W/046z/run.log 2>&1 || echo "FAIL sig0 400-409" ) &
wait
$PY scripts/CITY_b6z_report.py
