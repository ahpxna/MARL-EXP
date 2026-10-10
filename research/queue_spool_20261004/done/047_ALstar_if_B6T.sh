# 047 Branch P after B6-T (PROTOCOL_CITY_B6 decision tree + §B6-T): runs ONLY if a recipe passed B6-T on both new seeds (046/b6_verdicts.json).
# F* = that recipe (time-beneficial); A-L* on SELECT: lights ACT, RL-H_0..3, RL-C50_0..3 x F* seeds t0..t3 x guards none / fallback / clip / green+oos
# + always-SUMO under every light (eval5: release-class fleets; gate support = L-ACT_0 tau support, i.e. ACT's).  Endpoints AL*-1..4 as registered 05:47 ("benefit" = time per B6-T).
cd /Users/phanan/cig-amf-main; PY=external_envs/city_runtime/bin/python; W=research/city_sim/wave2_20261004
R=$($PY -c "
import json
v = json.load(open('$W/046/b6_verdicts.json')); rec = {}
for k, ok in v.items():
    r, t = k.rsplit('_t', 1); rec.setdefault(r, {})[t] = ok
print(' '.join(sorted(r for r, d in rec.items() if d.get('2') and d.get('3'))))" 2>/dev/null)
echo "B6-T recipes passing on both new seeds: [$R]"; [ -z "$R" ] && { echo "no time-beneficial recipe: Branch P not run (registered)"; exit 0; }
N=$(echo $R | awk '{print $1}' | sed 's/^U-//')
{ for L in ACT RL-H:0 RL-H:1 RL-H:2 RL-H:3 RL-C50:0 RL-C50:1 RL-C50:2 RL-C50:3; do for t in 0 1 2 3; do for g in none fallback clip green+oos; do
    echo "--light $L --fleet U:${N}_t$t --guard $g --support-from L-ACT:0 --seeds 100 101 102 103 104 --tag $(echo ${N}_t${t}_${L}_$g | tr ':+' '-P')"; done; done
    echo "--light $L --fleet L-ACT:0 --guard always --seeds 100 101 102 103 104 --tag $(echo OFF_$L | tr ':' '-')"; done; } | bash scripts/SPOOL_eval5_run.sh $W/047
echo "F* = $N" > $W/047/FSTAR.txt
