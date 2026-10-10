# 036 B6 evaluation — research/city_sim/PROTOCOL_CITY_B6_BENEFICIAL_FLEET_20261004.md
cd /Users/phanan/cig-amf-main
{ for F in U:L-ACT-v2_t0 U:L-ACT-v2_t1 U:L-ACT-v3_t0 U:L-ACT-v3_t1; do for L in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3; do
    echo "--light $L --fleet $F --seeds 100 101 102 103 104 --tag $(echo ${F}_$L | tr ':' '-')"; done; done
  for L in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3; do echo "--light $L --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag OFF_$(echo $L | tr ':' '-')"; done; } | bash scripts/SPOOL_eval3_run.sh research/city_sim/wave2_20261004/036
