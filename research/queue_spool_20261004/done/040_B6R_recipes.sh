# 040 B6-R recipe screen (written by CITY_make_b6_next.py): R1 v3/acc, R2 cotv/acc, R3 cotv/release, R4 v3/fine, 480 episodes, seeds 13/113
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python
{ echo "v3 acc 13 L-ACT-R1_t0"
echo "v3 acc 113 L-ACT-R1_t1"
echo "cotv acc 13 L-ACT-R2_t0"
echo "cotv acc 113 L-ACT-R2_t1"
echo "cotv release 13 L-ACT-R3_t0"
echo "cotv release 113 L-ACT-R3_t1"
echo "v3 fine 13 L-ACT-R4_t0"
echo "v3 fine 113 L-ACT-R4_t1"; } | xargs -P 8 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_fleet_train_v5.py --reward $0 --actions $1 --fleet-seed $2 --name $3 --episodes 480 --out research/city_sim/fleet_upgrade_20261004 > research/city_sim/fleet_upgrade_20261004/$3.out 2>&1 || echo "FAIL $3"'
mkdir -p research/city_sim/wave2_20261004/040/tmp; export XPLAY_TMP=$PWD/research/city_sim/wave2_20261004/040/tmp
{ echo "--light ACT --fleet U:L-ACT-R1_t0 --seeds 100 101 102 103 104 --tag U-L-ACT-R1_t0_ACT"
echo "--light ACT --fleet U:L-ACT-R1_t1 --seeds 100 101 102 103 104 --tag U-L-ACT-R1_t1_ACT"
echo "--light ACT --fleet U:L-ACT-R2_t0 --seeds 100 101 102 103 104 --tag U-L-ACT-R2_t0_ACT"
echo "--light ACT --fleet U:L-ACT-R2_t1 --seeds 100 101 102 103 104 --tag U-L-ACT-R2_t1_ACT"
echo "--light ACT --fleet U:L-ACT-R3_t0 --seeds 100 101 102 103 104 --tag U-L-ACT-R3_t0_ACT"
echo "--light ACT --fleet U:L-ACT-R3_t1 --seeds 100 101 102 103 104 --tag U-L-ACT-R3_t1_ACT"
echo "--light ACT --fleet U:L-ACT-R4_t0 --seeds 100 101 102 103 104 --tag U-L-ACT-R4_t0_ACT"
echo "--light ACT --fleet U:L-ACT-R4_t1 --seeds 100 101 102 103 104 --tag U-L-ACT-R4_t1_ACT"; echo "--light ACT --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag OFF_ACT"; } | xargs -P 4 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_eval4.py "$@" --out research/city_sim/wave2_20261004/040 >> research/city_sim/wave2_20261004/040/run.log 2>&1 || echo "FAIL $*"' sh
$PY -c "import sys; sys.path.insert(0, '.'); import scripts.CITY_wave2_report_v2 as R; out = []; R.rb6(out, R.W / '040', R.SEL, '-R recipe screen'); t = chr(10).join(out); open(str(R.W / 'report_v2_b6R.txt'), 'w').write(t); print(t)"
