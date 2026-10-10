#!/usr/bin/env bash
# D1 / D2 rows re-run with the eval-mode release fix (ledger C-41).
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; D=research/city_sim/spat_pilot_20261004/diag; export XPLAY_TMP=$PWD/$D/tmp
run() { nice -n 5 external_envs/city_runtime/bin/python -u scripts/CITY_d1_reward_alignment.py "$1" "$2" $D/d1 0 1 2 3 4 5 6 7 >> $D/d1_rerun.log 2>&1; }
run "P:$D/snap/Bon_s13_ep250_fleet.pt" PPOon_s13_ep250_det & run "P:$D/snap/Boff_s113_ep550_fleet.pt" PPOoff_s113_ep550_det &
wait
run "P:$D/d2/BC_glosa_on_fleet.pt" BC_glosa_on & run "P:$D/d2/BC_glosa_off_fleet.pt" BC_glosa_off &
wait; echo "rerun done $(date)"
