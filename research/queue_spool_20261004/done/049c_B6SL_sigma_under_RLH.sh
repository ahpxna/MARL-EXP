# 049c B6-SL (PROTOCOL_CITY_B6 §B6-SL, registered 04/10 wake 8): σ-fleet (0.5 / 0.3 / 0) under frozen lights ACT and RL-H_0..3, SELECT 100-104.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; W=research/city_sim/wave2_20261004
mkdir -p $W/049l/tmp
{ for sg in 0.5 0.3 0.0; do for L in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3; do echo "$sg $L S${sg}_$(echo $L | tr ':' '-')"; done; done; } |
  xargs -P 5 -L 1 sh -c 'XPLAY_TMP=$PWD/'"$W"'/049l/tmp nice -n 5 '"$PY"' -u scripts/CITY_eval4_sigma.py --sigma $0 --light $1 --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag $2 --out '"$W"'/049l >> '"$W"'/049l/run.log 2>&1 || echo "FAIL $0 $1"'
$PY scripts/CITY_b6sl_report.py
