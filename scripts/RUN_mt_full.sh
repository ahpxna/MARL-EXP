#!/usr/bin/env bash
# MT-C (PROTOCOL_CITY_MIDTOWN_TRANSFER_20261010; user 11/10: "tải xong thì chạy lại thí nghiệm trên map đầy đủ luôn"): the Midtown tests rerun on
# the FULL Overpass extract (research/city_sim/net/midtown_full.net.xml, built by data/osm_full_20261011/fetch_and_build.sh with the same
# netconvert options as midtown.net.xml).  Steps: actuated twin (same options as midtown_actuated.net.xml) -> test demand days 0-4 (the same
# randomTrips command) -> 600 s smoke (FT, LIGHT t59) -> full tests on days 0-4, 6 lanes -> report.  No retraining.
set -u; cd "$(dirname "$0")/.."
export PYTHONHASHSEED=0 OMP_NUM_THREADS=1 W20_CREEP=3 MT_BASE=osm MT_NET=midtown_full
PY=external_envs/city_runtime/bin/python; N=research/city_sim/net; DD=research/city_sim/demand; E=research/city_sim/midtown_transfer_20261010/eval_full
SITE=external_envs/city_runtime/lib/python3.12/site-packages/sumo; NC=$SITE/bin/netconvert; RT=$SITE/tools/randomTrips.py; export SUMO_HOME=$SITE
mkdir -p $E; echo "MT-C start $(date)"
test -f $N/midtown_full.net.xml || { echo "MISSING $N/midtown_full.net.xml (Overpass fetch not done)"; exit 1; }
if [ ! -f $N/midtown_full_actuated.net.xml ]; then
  $NC --sumo-net-file $N/midtown_full.net.xml --output-file $N/midtown_full_actuated.net.xml --output.street-names true --geometry.min-radius.fix.railways false \
      --geometry.avoid-overlap false --geometry.max-grade.fix false --offset.disable-normalization true --tls.default-type actuated --tls.rebuild true \
      --no-turnarounds true > $E/netconvert_actuated.log 2>&1 || { echo "actuated netconvert failed"; tail -5 $E/netconvert_actuated.log; exit 1; }
fi
for s in 0 1 2 3 4; do
  [ -f $DD/midtown_full_p075_s$s.rou.xml ] || $PY $RT -n $N/midtown_full.net.xml -o $DD/midtown_full_p075_s$s.trips.xml -r $DD/midtown_full_p075_s$s.rou.xml \
      --prefix v --vehicle-class passenger --fringe-factor 5 --seed $s --min-distance 400 --period 0.75 > /dev/null 2>&1 || { echo "randomTrips failed s$s"; exit 1; }
done
grep -c "<vehicle " $DD/midtown_full_p075_s{0,1,2,3,4}.rou.xml
$PY - <<'PY'
import sys, warnings; warnings.filterwarnings('ignore'); sys.path.insert(0, '.')
import sumolib
net = sumolib.net.readNet('research/city_sim/net/midtown_full.net.xml', withPrograms=True); g = {}
for t in net.getTrafficLights():
    ph = list(t.getPrograms().values())[0].getPhases(); n = sum(('G' in p.state or 'g' in p.state) and 'y' not in p.state.lower() for p in ph); g[n] = g.get(n, 0) + 1
E = [e for e in net.getEdges() if e.getFunction() != 'internal']
print('full net: edges', len(E), 'km', round(sum(e.getLength() for e in E) / 1000, 1), 'signals', len(net.getTrafficLights()), 'greens per signal', dict(sorted(g.items())), '-> AI-controlled (two-green):', g.get(2, 0))
PY
R="$PY -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py"
W19=research/city_sim/w19_20261008; F3=research/city_sim/w15_20261007/fresh3/fleets; MTL=research/city_sim/midtown_transfer_20261010/retrain/moe_ft
# smoke
$R scripts/CITY_eval6_v11.py --light FT --fleet L-ACT:0 --guard always --seeds 0 --smoke --tag MTF_smoke_FT --out $E/smoke > $E/smoke_ft.log 2>&1 || { echo "smoke FT failed"; tail -5 $E/smoke_ft.log; exit 1; }
$R scripts/CITY_eval6_v11.py --light RL-H:59 --fleet L-ACT:0 --guard always --seeds 0 --smoke --tag MTF_smoke_LG --out $E/smoke > $E/smoke_lg.log 2>&1 || { echo "smoke LIGHT failed"; tail -5 $E/smoke_lg.log; exit 1; }
grep -h "s0: TL" $E/smoke_*.log
# full tests, days 0-4
J=$E/jobs.txt; : > $J
echo "MTF_FT|-|scripts/CITY_eval6_v11.py --light FT --fleet L-ACT:0 --guard always" >> $J
echo "MTF_ACT|-|scripts/CITY_eval6_v11.py --light ACT --fleet L-ACT:0 --guard always" >> $J
for k in 59 60 61 62 63; do
  echo "MTF_LG_t$k|-|scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always" >> $J
  echo "MTF_A5ft_t$k|$MTL|scripts/CITY_eval6_v11.py --light RL-H:$k --fleet L-ACT:0 --guard always" >> $J
  for f in 1413 1513 1613 1713; do
    echo "MTF_BG_t${k}_s$f|-|scripts/CITY_eval_n4.py --n4 0.1:hyb:$W19/prep/prov_rlh${k}_cl.json:$W19/cmodel/n2_k$k.pt --light RL-H:$k --fleet PL:$F3/L11_s${f}_fleet.pt" >> $J
  done
done
echo "tests start $(date): $(wc -l < $J) jobs"
cat $J | xargs -P 6 -S 8192 -I{} zsh -c 'line="{}"; tag=${line%%|*}; rest=${line#*|}; lights=${rest%%|*}; cmd=${rest#*|}
  [ "$lights" = "-" ] || export W19_LIGHTS=$lights
  nice -n 5 '"$PY"' -u scripts/DEMO_midtown.py scripts/CITY_w9_run.py none scripts/CITY_w20_run.py ${=cmd} --seeds 0 1 2 3 4 --tag $tag --out '"$E"' > '"$E"'/$tag.log 2>&1 || echo "FAIL $tag"'
bad=0; while IFS='|' read -r tag _; do grep -q '"status": "COMPLETE"' $E/$tag.json 2>/dev/null || { echo "INCOMPLETE $tag"; bad=1; }; done < $J
MT_EVAL_DIR=$E MT_TAG_PREFIX=MTF $PY scripts/MT_report.py research/city_sim/midtown_transfer_20261010/report_mt_full.txt
echo "MT-C done $(date)"; exit $bad
