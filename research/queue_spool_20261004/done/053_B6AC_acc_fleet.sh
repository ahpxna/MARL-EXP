# 053 B6-AC (PROTOCOL_CITY_B6 §B6-AC, registered 04/10 wake 9): ACC fleet (route variant) vs ctrl / always-SUMO under frozen ACT and RL-H_0..3,
# SELECT 100-104 (053s, development) and VALIDATION 200-209 (053v, verdict).  No training.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; W=research/city_sim/wave2_20261004
for D in "053s 100 101 102 103 104" "053v 200 201 202 203 204 205 206 207 208 209"; do
  set -- $D; d=$1; shift; S="$*"; mkdir -p $W/$d/tmp
  { for L in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3; do T=$(echo $L | tr ':' '-')
      echo "scripts/CITY_eval4_route.py --route-variant ctrl --light $L --fleet L-ACT:0 --guard always --seeds $S --tag ctrl_$T"
      echo "scripts/CITY_eval4_route.py --route-variant acc --light $L --fleet L-ACT:0 --guard always --seeds $S --tag acc_$T"
      echo "scripts/CITY_eval4.py --light $L --fleet L-ACT:0 --guard always --seeds $S --tag OFF_$T"; done; } |
    xargs -P 5 -L 1 sh -c 'XPLAY_TMP=$PWD/'"$W/$d"'/tmp nice -n 5 '"$PY"' -u "$@" --out '"$W/$d"' >> '"$W/$d"'/run.log 2>&1 || echo "FAIL $*"' sh
  $PY scripts/CITY_b6ac_report.py $W/$d $S
done
