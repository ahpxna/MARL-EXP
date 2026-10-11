# 048z Z-4d (PROTOCOL_CITY_B6 §B6-Z amendment, descriptive): Z-sig0 (SUMO driver, sigma 0) under RL-H_0..3 on VALIDATION 200-209, only if
# job 048 ran (CHOSEN.txt); then scripts/CITY_alstar_sig0.py report.  Written 04/10 wake 8 before 047 / 048 ran.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; W=research/city_sim/wave2_20261004
[ -f $W/048/CHOSEN.txt ] || { echo "no A-L* validation: Z-4d not run"; exit 0; }
mkdir -p $W/048z/tmp; export XPLAY_TMP=$PWD/$W/048z/tmp
$PY scripts/CITY_alstar_sig0.py plan | xargs -P 4 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_eval4_sig0.py "$@" --out '"$W"'/048z >> '"$W"'/048z/run.log 2>&1 || echo "FAIL $*"' sh
$PY scripts/CITY_alstar_sig0.py report
