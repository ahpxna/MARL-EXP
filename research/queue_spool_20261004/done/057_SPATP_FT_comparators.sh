# 057 SPaT pilot comparators (PROTOCOL_CITY_SPAT_PILOT_20261004 Amendment R1, σ* rule frozen before this run): under FT, always-SUMO,
# σ-family {0, 0.1, 0.2, 0.3, 0.4}, ACC and ctrl (identity), on SELECT 100-104 (057s) and fresh confirmation traffic 420-429 (057c).
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; W=research/city_sim/wave2_20261004
for D in "057s 100 101 102 103 104" "057c 420 421 422 423 424 425 426 427 428 429"; do
  set -- $D; d=$1; shift; S="$*"; mkdir -p $W/$d/tmp
  { echo "scripts/CITY_eval4.py --light FT --fleet L-ACT:0 --guard always --seeds $S --tag OFF_FT"
    for sg in 0.0 0.1 0.2 0.3 0.4; do echo "scripts/CITY_eval4_sigma.py --sigma $sg --light FT --fleet L-ACT:0 --guard always --seeds $S --tag S${sg}_FT"; done
    for v in ctrl acc; do echo "scripts/CITY_eval4_route.py --route-variant $v --light FT --fleet L-ACT:0 --guard always --seeds $S --tag ${v}_FT"; done; } |
    xargs -P 8 -L 1 sh -c 'XPLAY_TMP=$PWD/'"$W/$d"'/tmp nice -n 5 '"$PY"' -u "$@" --out '"$W/$d"' >> '"$W/$d"'/run.log 2>&1 || echo "FAIL $*"' sh
done
echo "057 done $(date)"
