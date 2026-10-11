# 051p A-L* with F* = R5h (PROTOCOL_CITY_B6 §B6-R5-P, registered 04/10 wake 9 BEFORE the B6-R5 verdict): runs ONLY if 050r CONFIRMED.
# SELECT (guard choice, AP-1) -> VALIDATION 200-209 under RL-H_0..3 (AP-2..AP-4), σ-family under the same lights on VALIDATION.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; W=research/city_sim/wave2_20261004
grep -q "VERDICT: R5h CONFIRMED" $W/050r/report_b6r5.txt 2>/dev/null || { echo "B6-R5 not confirmed: A-L* with R5h not run (registered)"; exit 0; }
$PY scripts/CITY_alstar_r5.py plan_sel | bash scripts/SPOOL_eval5_run.sh $W/051s
$PY scripts/CITY_alstar_r5.py select
$PY scripts/CITY_alstar_r5.py plan_val | bash scripts/SPOOL_eval5_run.sh $W/051v
$PY scripts/CITY_alstar_r5.py plan_sig 200 201 202 203 204 205 206 207 208 209 | grep -v " ACT " |
  xargs -P 5 -L 1 sh -c 'sg=$0; L=$1; tg=$2; shift 2; XPLAY_TMP=$PWD/'"$W"'/051v/tmp nice -n 5 '"$PY"' -u scripts/CITY_eval4_sigma.py --sigma $sg --light $L --fleet L-ACT:0 --guard always --seeds "$@" --tag $tg --out '"$W"'/051v >> '"$W"'/051v/run.log 2>&1 || echo "FAIL $sg $L"'
$PY scripts/CITY_alstar_r5.py judge
