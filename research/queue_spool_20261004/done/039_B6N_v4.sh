# 039 B6-N policy-class diagnostic (PROTOCOL_CITY_B6 §B6-N, registered 05:53): v4 release / residual x seeds 13 / 113, then eval4 vs always-SUMO
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; O=research/city_sim/fleet_upgrade_20261004; W=research/city_sim/wave2_20261004
printf '%s\n' "release 13 L-ACT-v4rel_t0" "release 113 L-ACT-v4rel_t1" "residual 13 L-ACT-v4res_t0" "residual 113 L-ACT-v4res_t1" | xargs -P 4 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_fleet_train_v4.py --actions $0 --fleet-seed $1 --name $2 --out '"$O"' > '"$O"'/$2.out 2>&1 || echo "FAIL $2"'
mkdir -p $W/039/tmp; export XPLAY_TMP=$PWD/$W/039/tmp
{ for F in L-ACT-v4rel_t0 L-ACT-v4rel_t1 L-ACT-v4res_t0 L-ACT-v4res_t1; do echo "--light ACT --fleet U:$F --seeds 100 101 102 103 104 --tag U-${F}_ACT"; done
  echo "--light ACT --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag OFF_ACT"; } | xargs -P 4 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_eval4.py "$@" --out '"$W"'/039 >> '"$W"'/039/run.log 2>&1 || echo "FAIL $*"' sh
$PY -c "
import sys; sys.path.insert(0, '.'); import scripts.CITY_wave2_report_v2 as R
out = []; R.rb6(out, R.W / '039', R.SEL, '-N policy-class diagnostic'); t = '\n'.join(out); open(str(R.W / 'report_v2_b6N.txt'), 'w').write(t + '\n'); print(t)"
external_envs/city_runtime/bin/python scripts/CITY_make_b6_next.py
