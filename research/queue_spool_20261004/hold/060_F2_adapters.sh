# 060 F2 observation adapters at the frozen light (SELECT) — research/city_sim/PROTOCOL_CITY_WAVE2_JOBS_20261004.md
cd /Users/phanan/cig-amf-main
{ for P in "RJ0 RL-J:0 L-ACT:0" "RJ1 RL-J:1 L-ACT:1" "SH0 SIM-halt:0 SIM-halt:0" "SH1 SIM-halt:1 SIM-halt:1"; do set -- $P; X=$1 L0=$2 F0=$3
    for F in $F0 U:FTv1_$X U:FTv2_$X U:NEWv2_$X; do for A in raw q:0.5:0 q:1:0 q:1:0.5 q:1:1; do
      echo "--light $L0 --light-obs $A --fleet $F --seeds 100 101 102 103 104 --tag ${X}_$(echo $F | tr ':' '-')_$(echo $A | tr ':.' '-p')"; done; done; done; } | bash scripts/SPOOL_eval3_run.sh research/city_sim/wave2_20261004/060
