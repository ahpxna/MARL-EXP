# 059 SPaT pilot training (PROTOCOL_CITY_SPAT_PILOT_20261004 Amendments R1-R3): reward B, FT, 600 episodes, 12 runs in parallel
# (pilot seeds 13 / 113 + confirmation seeds 213-513, both arms).  Gates: both checks must PASS first.  Resumable (--resume).
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; O=research/city_sim/spat_pilot_20261004/fleets
mkdir -p $O
$PY scripts/CITY_spat_trace_check.py FT > $O/spat_trace_check.txt 2>&1 || { echo "SPaT trace check FAIL"; exit 1; }
V8CHECK_END=600 $PY scripts/CITY_v8_check.py > $O/v8_check.txt 2>&1 || { echo "v8 check FAIL"; exit 1; }
{ for sp in on off; do for s in 13 113 213 313 413 513; do echo "$sp $s B${sp}_s$s"; done; done; } |
  xargs -P 12 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_fleet_train_v8_ppo.py --spat $0 --seed $1 --episodes 600 --name $2 --out '"$O"' --resume >> '"$O"'/$2.out 2>&1 || echo "FAIL $2"'
echo "059 done $(date)"
