# 040c B6-R rerun of ALL four arms with the sanitized trainer v6 (city ledger C-22: sentinel readings and garbage next-states of
# teleporting agents; v5 has neither guard).  R1 v3/acc, R2 cotv/acc, R3 cotv/release, R4 v3/fine; 480 episodes; seeds 13 / 113;
# eval4 vs always-SUMO under ACT, SELECT; same B6-1 criteria.  The v5 run (job 040) is reported, labelled "unsanitized".
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; O=research/city_sim/fleet_upgrade_20261004; W=research/city_sim/wave2_20261004
{ for A in "v3 acc R1" "cotv acc R2" "cotv release R3" "v3 fine R4"; do set -- $A; for t in 0 1; do echo "$1 $2 $((13 + 100 * t)) L-ACT-${3}v6_t$t"; done; done; } |
  xargs -P 8 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_fleet_train_v6.py --reward $0 --actions $1 --fleet-seed $2 --name $3 --episodes 480 --out '"$O"' > '"$O"'/$3.out 2>&1 || echo "FAIL $3"'
mkdir -p $W/040c/tmp; export XPLAY_TMP=$PWD/$W/040c/tmp
{ for R in R1 R2 R3 R4; do for t in 0 1; do echo "--light ACT --fleet U:L-ACT-${R}v6_t$t --seeds 100 101 102 103 104 --tag U-L-ACT-${R}v6_t${t}_ACT"; done; done
  echo "--light ACT --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag OFF_ACT"; } | xargs -P 4 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_eval4.py "$@" --out '"$W"'/040c >> '"$W"'/040c/run.log 2>&1 || echo "FAIL $*"' sh
$PY -c "
import sys; sys.path.insert(0, '.'); import scripts.CITY_wave2_report_v2 as R
out = []; R.rb6(out, R.W / '040c', R.SEL, '-R rerun (v6 sanitized)'); t = '\n'.join(out); open(str(R.W / 'report_v2_b6R_v6.txt'), 'w').write(t + '\n'); print(t)"
