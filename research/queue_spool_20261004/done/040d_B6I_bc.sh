# 040d B6-I behaviour cloning of SUMO's driver (PROTOCOL_CITY_B6 §B6-I): acc and fine sets, seed 0; eval4 vs always-SUMO under ACT, SELECT
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; O=research/city_sim/fleet_upgrade_20261004; W=research/city_sim/wave2_20261004
printf '%s\n' "acc L-ACT-BCacc_t0" "fine L-ACT-BCfine_t0" | xargs -P 2 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_fleet_bc.py --actions $0 --epochs 20 --seed 0 --name $1 --out '"$O"' > '"$O"'/$1.out 2>&1 || echo "FAIL $1"'
mkdir -p $W/040d/tmp; export XPLAY_TMP=$PWD/$W/040d/tmp
{ for F in L-ACT-BCacc_t0 L-ACT-BCfine_t0; do echo "--light ACT --fleet U:$F --seeds 100 101 102 103 104 --tag U-${F}_ACT"; done
  echo "--light ACT --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag OFF_ACT"; } | xargs -P 3 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_eval4.py "$@" --out '"$W"'/040d >> '"$W"'/040d/run.log 2>&1 || echo "FAIL $*"' sh
cat $O/L-ACT-BCacc_t0.out $O/L-ACT-BCfine_t0.out
$PY -c "
import sys; sys.path.insert(0, '.'); import scripts.CITY_wave2_report_v2 as R
out = []; R.rb6(out, R.W / '040d', R.SEL, '-I behaviour cloning of SUMO'); t = '\n'.join(out); open(str(R.W / 'report_v2_b6I.txt'), 'w').write(t + '\n'); print(t)"
