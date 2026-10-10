# D1 reward alignment (04/10 13:46): FT, TRAIN traffic 0-7, every policy on its own trace.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; D=research/city_sim/spat_pilot_20261004/diag
printf '%s\n' "always always" "sigma0.3 sigma0.3" "U:L-ACT-R5h_t0 R5h_t0" "U:L-ACT-R5h_t1 R5h_t1" "P:research/city_sim/spat_pilot_20261004/diag/snap/Bon_s13_ep250_fleet.pt PPOon_s13_ep250_det"   "P:research/city_sim/spat_pilot_20261004/diag/snap/Bon_s13_ep250_fleet.pt:sto PPOon_s13_ep250_sto" "P:research/city_sim/spat_pilot_20261004/diag/snap/Boff_s113_ep550_fleet.pt PPOoff_s113_ep550_det" "P:research/city_sim/spat_pilot_20261004/diag/snap/Boff_s113_ep550_fleet.pt:sto PPOoff_s113_ep550_sto" "GLOSA GLOSA" |
  xargs -P 4 -L 1 sh -c 'XPLAY_TMP=$PWD/'"$D"'/tmp nice -n 5 '"$PY"' -u scripts/CITY_d1_reward_alignment.py $0 $1 '"$D"'/d1 0 1 2 3 4 5 6 7 >> '"$D"'/d1_run.log 2>&1 || echo "FAIL $1"'
echo "D1 done $(date)"
