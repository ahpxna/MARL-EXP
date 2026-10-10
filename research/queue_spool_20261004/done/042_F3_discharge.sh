# 040 F3 open-loop discharge diagnostic — research/city_sim/PROTOCOL_CITY_WAVE2_JOBS_20261004.md
cd /Users/phanan/cig-amf-main; O=research/city_sim/wave2_20261004/040
{ for t in 0 1 2 3; do echo "--light RL-H:$t --fleet human --seeds 100 101 102 103 104 --discharge --record $O/rec_RLH$t/phases_s{seed}.npz --tag rec_RLH$t"; done
  echo "--light ACT --fleet human --seeds 100 101 102 103 104 --discharge --record $O/rec_ACT/phases_s{seed}.npz --tag rec_ACT"
  for P in "RJ0 RL-J:0 L-ACT:0" "RJ1 RL-J:1 L-ACT:1" "SH0 SIM-halt:0 SIM-halt:0" "SH1 SIM-halt:1 SIM-halt:1"; do set -- $P
    echo "--light $2 --fleet $3 --seeds 100 101 102 103 104 --discharge --record $O/rec_$1/phases_s{seed}.npz --tag rec_$1"; done; } | bash scripts/SPOOL_eval3_run.sh $O
{ for R in RLH0 RLH1 RLH2 RLH3 ACT; do for F in human L-ACT:0 L-ACT:1 L-ACT:2 L-ACT:3 L-RLH:0; do
    echo "--replay-dir $O/rec_$R --fleet $F --seeds 100 101 102 103 104 --discharge --record $O/trace_${R}_$(echo $F | tr ':' '-')/phases_s{seed}.npz --tag rep_${R}_$(echo $F | tr ':' '-')"; done; done
  for P in "RJ0 L-ACT:0" "RJ1 L-ACT:1" "SH0 SIM-halt:0" "SH1 SIM-halt:1"; do set -- $P
    for F in $2 U:FTv1_$1 U:FTv2_$1 U:NEWv2_$1 human; do echo "--replay-dir $O/rec_$1 --fleet $F --seeds 100 101 102 103 104 --discharge --record $O/trace_${1}_$(echo $F | tr ':' '-')/phases_s{seed}.npz --tag rep_${1}_$(echo $F | tr ':' '-')"; done; done; } | bash scripts/SPOOL_eval3_run.sh $O
