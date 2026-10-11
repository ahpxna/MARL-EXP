# 055 G4-TV (PROTOCOL_CITY_G4_COLOGNE8_20261004): train two cologne8 lights (DQN 11 / 12, 120 episodes), route variants for SUMO seeds 100-109,
# evaluate FT / RLK_s11 / RLK_s12 x base / sig0.3 / ctrl / acc on 100-109, report.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; G=research/city_sim/g4_cologne8
mkdir -p $G/eval/tmp
printf '%s\n' 11 12 | xargs -P 2 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_g4_train_light.py --seed $0 --episodes 120 --name RLK_s$0 --out '"$G"' > '"$G"'/RLK_s$0.out 2>&1 || echo "FAIL train $0"'
for v in ctrl acc; do $PY scripts/CITY_g4_make_variants.py $v 100 101 102 103 104 105 106 107 108 109 | tail -1; done
{ for L in FT RLK:RLK_s11 RLK:RLK_s12; do for F in base sig0.3 ctrl acc; do echo "$L $F $(echo $L | sed 's/^RLK://')_$F"; done; done; } |
  xargs -P 6 -L 1 sh -c 'XPLAY_TMP=$PWD/'"$G"'/eval/tmp nice -n 5 '"$PY"' -u scripts/CITY_g4_eval.py --light $0 --fleet $1 --tag $2 --out '"$G"'/eval >> '"$G"'/eval/run.log 2>&1 || echo "FAIL $0 $1"'
$PY scripts/CITY_g4_report.py
