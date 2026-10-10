# 046 B6-T confirmation (PROTOCOL_CITY_B6 §B6-T): R2 (cotv/acc) and R3 (cotv/release), v6, 480 episodes, NEW seeds 213 / 313, fresh traffic 400-409
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; O=research/city_sim/fleet_upgrade_20261004; W=research/city_sim/wave2_20261004
printf '%s\n' "acc 213 L-ACT-R2v6_t2" "acc 313 L-ACT-R2v6_t3" "release 213 L-ACT-R3v6_t2" "release 313 L-ACT-R3v6_t3" |
  xargs -P 4 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_fleet_train_v6.py --reward cotv --actions $0 --fleet-seed $1 --name $2 --episodes 480 --out '"$O"' > '"$O"'/$2.out 2>&1 || echo "FAIL $2"'
mkdir -p $W/046/tmp; export XPLAY_TMP=$PWD/$W/046/tmp; T="400 401 402 403 404 405 406 407 408 409"
{ for F in L-ACT-R2v6_t2 L-ACT-R2v6_t3 L-ACT-R3v6_t2 L-ACT-R3v6_t3; do echo "--light ACT --fleet U:$F --seeds $T --tag U-${F}_ACT"; done
  echo "--light ACT --fleet L-ACT:0 --guard always --seeds $T --tag OFF_ACT"; } | xargs -P 5 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_eval4.py "$@" --out '"$W"'/046 >> '"$W"'/046/run.log 2>&1 || echo "FAIL $*"' sh
$PY scripts/CITY_wave2_report_v2.py b6t
