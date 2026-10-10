# 040b B6-N residual arm RERUN with the sanitized trainer v6 (city ledger C-22): residual x seeds 13 / 113, reward v3, 120 episodes; eval4 vs always-SUMO
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; O=research/city_sim/fleet_upgrade_20261004; W=research/city_sim/wave2_20261004
printf '%s\n' "13 L-ACT-v6res_t0" "113 L-ACT-v6res_t1" | xargs -P 2 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_fleet_train_v6.py --reward v3 --actions residual --fleet-seed $0 --name $1 --out '"$O"' > '"$O"'/$1.out 2>&1 || echo "FAIL $1"'
mkdir -p $W/040b/tmp; export XPLAY_TMP=$PWD/$W/040b/tmp
{ for F in L-ACT-v6res_t0 L-ACT-v6res_t1; do echo "--light ACT --fleet U:$F --seeds 100 101 102 103 104 --tag U-${F}_ACT"; done
  echo "--light ACT --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag OFF_ACT"; } | xargs -P 3 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_eval4.py "$@" --out '"$W"'/040b >> '"$W"'/040b/run.log 2>&1 || echo "FAIL $*"' sh
$PY -c "
import sys; sys.path.insert(0, '.'); import scripts.CITY_wave2_report_v2 as R
out = []; R.rb6(out, R.W / '040b', R.SEL, '-N residual rerun (v6 sanitized)'); t = '\n'.join(out); open(str(R.W / 'report_v2_b6N_residual_v6.txt'), 'w').write(t + '\n'); print(t)"
