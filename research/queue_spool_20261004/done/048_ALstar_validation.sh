# 048 A-L* VALIDATION (Branch P): only if job 047 produced F* (FSTAR.txt); chosen guard from SELECT; judged on traffic 200-209
cd /Users/phanan/cig-amf-main; PY=external_envs/city_runtime/bin/python; W=research/city_sim/wave2_20261004
[ -f $W/047/FSTAR.txt ] || { echo "no F*: A-L* validation not run (registered)"; exit 0; }
$PY scripts/CITY_wave2_report_v2.py alstar
$PY scripts/CITY_alstar_validation.py plan | bash scripts/SPOOL_eval5_run.sh $W/048
$PY scripts/CITY_alstar_validation.py judge
