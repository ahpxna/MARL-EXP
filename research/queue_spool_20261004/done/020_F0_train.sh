# F0 / V3 trainings — research/city_sim/PROTOCOL_CITY_FLEET_UPGRADE_20261004.md
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; O=research/city_sim/fleet_upgrade_20261004; mkdir -p $O
Q7=research/city_sim/q7_cross_version_20261002; QB=research/city_sim/q7b_contract_20261002; C=research/city_sim/cotrain_20261004
{ for t in 0 1; do init=$Q7/L-ACT.pt; [ $t = 1 ] && init=$QB/L-ACT_t1.pt
    echo "--mode ft --init $init --against RL-J:$t --reward v1 --episodes 60 --fleet-seed $((2013 + 100 * t)) --name FTv1_RJ$t"
    echo "--mode ft --init $init --against RL-J:$t --reward v2 --episodes 60 --fleet-seed $((2013 + 100 * t)) --name FTv2_RJ$t"
    echo "--mode new --against RL-J:$t --reward v2 --episodes 120 --fleet-seed $((3013 + 100 * t)) --name NEWv2_RJ$t"
    echo "--mode new --against ACT --reward v2 --episodes 120 --fleet-seed $((13 + 100 * t)) --name L-ACT-v2_t$t"; done
  for k in 0 1; do init=$C/SIM-halt_k${k}_fleet.pt
    echo "--mode ft --init $init --against SIM-halt:$k --reward v1 --episodes 60 --fleet-seed $((2013 + 100 * k)) --name FTv1_SH$k"
    echo "--mode ft --init $init --against SIM-halt:$k --reward v2 --episodes 60 --fleet-seed $((2013 + 100 * k)) --name FTv2_SH$k"
    echo "--mode new --against SIM-halt:$k --reward v2 --episodes 120 --fleet-seed $((3013 + 100 * k)) --name NEWv2_SH$k"; done; } |
  xargs -P 4 -L 1 sh -c 'n=$(echo "$@" | sed "s/.*--name //"); nice -n 5 '"$PY"' -u scripts/CITY_fleet_upgrade.py "$@" --out '"$O"' > '"$O"'/$n.out 2>&1 || echo "FAIL $n"' sh
ls $O/*_fleet.pt | wc -l
