# 054 B6-G (PROTOCOL_CITY_B6 §B6-G, registered 04/10 wake 9): always-SUMO, σ 0.3 and ACC fleets under frozen RL-C50_0..3 and RL-J_0..3, VALIDATION 200-209.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; W=research/city_sim/wave2_20261004
mkdir -p $W/054/tmp; S="200 201 202 203 204 205 206 207 208 209"
{ for L in RL-C50:0 RL-C50:1 RL-C50:2 RL-C50:3 RL-J:0 RL-J:1 RL-J:2 RL-J:3; do T=$(echo $L | tr ':' '-')
    echo "scripts/CITY_eval4.py --light $L --fleet L-ACT:0 --guard always --seeds $S --tag OFF_$T"
    echo "scripts/CITY_eval4_sigma.py --sigma 0.3 --light $L --fleet L-ACT:0 --guard always --seeds $S --tag S0.3_$T"
    echo "scripts/CITY_eval4_route.py --route-variant acc --light $L --fleet L-ACT:0 --guard always --seeds $S --tag acc_$T"; done; } |
  xargs -P 6 -L 1 sh -c 'XPLAY_TMP=$PWD/'"$W"'/054/tmp nice -n 5 '"$PY"' -u "$@" --out '"$W"'/054 >> '"$W"'/054/run.log 2>&1 || echo "FAIL $*"' sh
$PY scripts/CITY_b6g_report.py
