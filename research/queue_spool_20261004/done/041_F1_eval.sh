# 030 F1 evaluation + V3 — research/city_sim/PROTOCOL_CITY_WAVE2_JOBS_20261004.md / PROTOCOL_CITY_FLEET_UPGRADE_20261004.md
cd /Users/phanan/cig-amf-main
{ for P in "RJ0 RL-J:0 L-ACT:0" "RJ1 RL-J:1 L-ACT:1" "SH0 SIM-halt:0 SIM-halt:0" "SH1 SIM-halt:1 SIM-halt:1"; do set -- $P; X=$1 L0=$2 F0=$3
    for F in $F0 U:FTv1_$X U:FTv2_$X U:NEWv2_$X human; do for L in $L0 ACT; do t=$(echo "${X}_${F}_${L}" | tr ':+/' '---')
      echo "--light $L --fleet $F --seeds 100 101 102 103 104 --tag sel_$t"; echo "--light $L --fleet $F --seeds 200 201 202 203 204 205 206 207 208 209 --tag test_$t"; done; done; done
  for t in 0 1; do for L in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3; do echo "--light $L --fleet U:L-ACT-v2_t$t --seeds 100 101 102 103 104 --tag V3_t${t}_$(echo $L | tr ':' '-')"; done; done; } | bash scripts/SPOOL_eval3_run.sh research/city_sim/wave2_20261004/030
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 XPLAY_TMP=$PWD/research/city_sim/wave2_20261004/030/tmp
external_envs/city_runtime/bin/python -u scripts/CITY_cmd_realized_v2.py --configs ACT/U:L-ACT-v2_t0 ACT/U:L-ACT-v2_t1 ACT/L-ACT:0 ACT/L-ACT:1 --seeds 100 101 --out research/city_sim/wave2_20261004/030/v3_cmd_realized_v2.json
