# 049a B6-S (PROTOCOL_CITY_B6 §B6-S, registered 09:13 04/10): the non-learned σ-family, SUMO driving the agent cars with σ in {0.1..0.4}
# (+ σ 0.5 as the self-check against always-SUMO), ACT, SELECT 100-104 (049s) and 400-409 (049s/T).  No training.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; W=research/city_sim/wave2_20261004
mkdir -p $W/049s/tmp $W/049s/T/tmp
{ for sg in 0.1 0.2 0.3 0.4 0.5; do echo "$sg $W/049s 100 101 102 103 104"; echo "$sg $W/049s/T 400 401 402 403 404 405 406 407 408 409"; done; } |
  xargs -P 5 -L 1 sh -c 'sg=$0; d=$1; shift; XPLAY_TMP=$PWD/$d/tmp nice -n 5 '"$PY"' -u scripts/CITY_eval4_sigma.py --sigma $sg --light ACT --fleet L-ACT:0 --guard always --seeds "$@" --tag S${sg}_ACT --out $d >> '"$W"'/049s/run.log 2>&1 || echo "FAIL sigma $sg $d"'
$PY scripts/CITY_b6sh_report.py sigma
