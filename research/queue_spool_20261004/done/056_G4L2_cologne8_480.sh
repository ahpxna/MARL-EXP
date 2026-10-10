# 056 G4-L2 (PROTOCOL_CITY_G4_COLOGNE8_20261004 §G4-L2): RLK at 480 episodes (DQN 11 / 12); G4-1' on 100-109; if it passes, T4 / T5 on fresh 110-129.
cd /Users/phanan/cig-amf-main; export PYTHONHASHSEED=0 OMP_NUM_THREADS=1; PY=external_envs/city_runtime/bin/python; G=research/city_sim/g4_cologne8
mkdir -p $G/eval480/tmp $G/eval480b/tmp
printf '%s\n' 11 12 | xargs -P 2 -L 1 sh -c 'nice -n 5 '"$PY"' -u scripts/CITY_g4_train_light.py --seed $0 --episodes 480 --name RLK480_s$0 --out '"$G"' > '"$G"'/RLK480_s$0.out 2>&1 || echo "FAIL train $0"'
printf '%s\n' RLK480_s11 RLK480_s12 | xargs -P 2 -L 1 sh -c 'XPLAY_TMP=$PWD/'"$G"'/eval480/tmp nice -n 5 '"$PY"' -u scripts/CITY_g4_eval.py --light RLK:$0 --fleet base --tag $0_base --out '"$G"'/eval480 >> '"$G"'/eval480/run.log 2>&1'
$PY scripts/CITY_g4_report2.py g41
[ -f $G/eval480/G41_PASS ] || { echo "G4-1' not supported: T4 / T5 re-test not run (registered)"; exit 0; }
S="110 111 112 113 114 115 116 117 118 119 120 121 122 123 124 125 126 127 128 129"
for v in ctrl acc; do $PY scripts/CITY_g4_make_variants.py $v $S | tail -1; done
{ for L in FT RLK:RLK480_s11 RLK:RLK480_s12; do for F in base sig0.3 ctrl acc; do echo "$L $F $(echo $L | sed 's/^RLK://')_$F"; done; done; } |
  xargs -P 6 -L 1 sh -c 'XPLAY_TMP=$PWD/'"$G"'/eval480b/tmp nice -n 5 '"$PY"' -u scripts/CITY_g4_eval.py --light $0 --fleet $1 --seeds '"$S"' --tag $2 --out '"$G"'/eval480b >> '"$G"'/eval480b/run.log 2>&1 || echo "FAIL $0 $1"'
$PY scripts/CITY_g4_report2.py tv
