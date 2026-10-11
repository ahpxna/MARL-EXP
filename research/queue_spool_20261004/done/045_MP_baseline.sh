# 090 MaxPressure (published light baseline) x every B3-X fleet (SELECT) — research/city_sim/PROTOCOL_CITY_WAVE2_JOBS_20261004.md
cd /Users/phanan/cig-amf-main
{ for F in human L-ACT:0 L-ACT:1 L-ACT:2 L-ACT:3 L-FT:0 L-FT:1 L-FT:2 L-FT:3 L-RLH:0 L-RLH:1 L-RLH:2 L-RLH:3 SIM-halt:0 SIM-halt:1 SIM-halt:2 SIM-halt:3 ALT-halt:0 ALT-halt:1 ALT-halt:2 ALT-halt:3 SIM-delay:0 SIM-delay:1 SIM-delay:2 SIM-delay:3; do
    echo "--light MP --fleet $F --seeds 100 101 102 103 104 --tag MP_$(echo $F | tr ':' '-')"; done; } | bash scripts/SPOOL_eval3_run.sh research/city_sim/wave2_20261004/090
