# 080 L3 guards on other fleets (SELECT) — research/city_sim/PROTOCOL_CITY_WAVE2_JOBS_20261004.md
cd /Users/phanan/cig-amf-main
{ for L in ACT MP RL-H:0 RL-H:1 RL-H:2 RL-H:3; do for F in L-RLH:0 L-RLH:1 L-RLH:2 L-RLH:3 SIM-halt:0 SIM-halt:1 SIM-halt:2 SIM-halt:3 L-FT:0 L-FT:1; do
    for g in none green+oos; do echo "--light $L --fleet $F --guard $g --seeds 100 101 102 103 104 --tag $(echo ${L}_${F}_$g | tr ':+' '-P')"; done; done; done; } | bash scripts/SPOOL_eval3_run.sh research/city_sim/wave2_20261004/080
