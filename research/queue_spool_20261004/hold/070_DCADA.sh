# 070 DC-Ada comparator — research/city_sim/PROTOCOL_CITY_WAVE2_JOBS_20261004.md §070 (tuner smoke 05:0x: 2 rounds x (1+2) rollouts, scratchpad)
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 MKL_NUM_THREADS=1; O=research/city_sim/wave2_20261004/070; mkdir -p $O/tmp; export XPLAY_TMP=$PWD/$O/tmp
printf '%s\n' "RJ0 RL-J:0" "RJ1 RL-J:1" "SH0 SIM-halt:0" "SH1 SIM-halt:1" | xargs -P 4 -L 1 sh -c 'nice -n 5 external_envs/city_runtime/bin/python -u scripts/CITY_dcada_tune.py --light "$1" --fleet U:FTv2_$0 --sigma 0.03 --name dcada_$0 --out '"$O"' > '"$O"'/dcada_$0.out 2>&1 || echo "FAIL $0"'
{ for P in "RJ0 RL-J:0 L-ACT:0" "RJ1 RL-J:1 L-ACT:1" "SH0 SIM-halt:0 SIM-halt:0" "SH1 SIM-halt:1 SIM-halt:1"; do set -- $P
    [ -f $O/dcada_$1.json ] || continue
    for F in $3 U:FTv2_$1; do for SEEDS in "100 101 102 103 104" "200 201 202 203 204 205 206 207 208 209"; do
      echo "--light $2 --light-obs affine:$O/dcada_$1.json --fleet $F --seeds $SEEDS --tag eval_$1_$(echo $F | tr ':' '-')_$(echo $SEEDS | cut -c1-3)"; done; done; done; } | bash scripts/SPOOL_eval3_run.sh $O/eval
