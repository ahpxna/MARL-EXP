#!/usr/bin/env bash
# Fetch all Midtown roads from Overpass (user 11/10: "tải lại OSM đầy đủ cho Midtown đi"), retrying while the public servers are overloaded,
# then build research/city_sim/net/midtown_full.net.xml with the SAME netconvert options as midtown.net.xml (only the input file differs).
set -u; cd /Users/phanan/cig-amf-main; D=research/city_sim/data/osm_full_20261011
Q='[out:xml][timeout:180];(way["highway"](40.741527,-73.998224,40.769017,-73.954077);relation["type"="restriction"](40.741527,-73.998224,40.769017,-73.954077););(._;>;);out body;'
echo "$Q" > $D/query_body.overpassql
ok=0
for attempt in 1 2 3 4 5 6 7 8; do
  for url in https://overpass-api.de/api/interpreter https://overpass.kumi.systems/api/interpreter https://overpass.private.coffee/api/interpreter; do
    curl -sS -m 300 -A "cig-amf-city-sim/1.0 (research traffic simulation; SUMO netconvert)" -H "Accept: */*" -o $D/try.osm.xml --data-urlencode "data=$Q" "$url"
    n=$(grep -c '<way ' $D/try.osm.xml 2>/dev/null || echo 0)
    echo "attempt $attempt $url ways $n $(date +%T)"
    if [ "$n" -gt 1000 ] && tail -c 200 $D/try.osm.xml | grep -q '</osm>'; then mv $D/try.osm.xml $D/midtown_full.osm.xml; echo "source $url $(date)" > $D/source.txt; ok=1; break 2; fi
  done
  sleep 600
done
[ $ok = 1 ] || { echo "Overpass still unavailable after 8 attempts"; exit 1; }
shasum -a 256 $D/midtown_full.osm.xml | tee $D/sha256.txt
echo "ways $(grep -c '<way ' $D/midtown_full.osm.xml) nodes $(grep -c '<node ' $D/midtown_full.osm.xml) relations $(grep -c '<relation ' $D/midtown_full.osm.xml)"
test -e research/city_sim/net/midtown_full.net.xml && { echo "midtown_full.net.xml exists: not overwritten"; exit 1; }
/Users/phanan/cig-amf-main/external_envs/city_runtime/lib/python3.12/site-packages/sumo/bin/netconvert --osm-files $D/midtown_full.osm.xml --output-file research/city_sim/net/midtown_full.net.xml --output.street-names true --output.original-names true \
  --proj.utm true --geometry.remove true --roundabouts.guess true --tls.discard-simple true --tls.join true --tls.guess-signals true \
  --tls.default-type static --ramps.guess true --keep-edges.by-vclass passenger --remove-edges.isolated true \
  --no-turnarounds.except-deadend true --junctions.join true --seed 1 > $D/netconvert.log 2>&1 || { echo "netconvert failed"; tail -5 $D/netconvert.log; exit 1; }
external_envs/city_runtime/bin/python - <<'PY'
import sumolib, re, warnings; warnings.filterwarnings('ignore')
for f in ('midtown', 'midtown_full'):
    net = sumolib.net.readNet(f'research/city_sim/net/{f}.net.xml', withPrograms=True)
    E = [e for e in net.getEdges() if e.getFunction() != 'internal']; names = {e.getName() for e in E}
    w = sorted({int(m.group(1)) for n in names for m in [re.match(r'West (\d+)', n or '')] if m}); ea = sorted({int(m.group(1)) for n in names for m in [re.match(r'East (\d+)', n or '')] if m})
    print(f, 'edges', len(E), 'km', round(sum(e.getLength() for e in E) / 1000, 1), 'signals', len(net.getTrafficLights()), '| West', (w[0], w[-1]) if w else None, 'East', (ea[0], ea[-1]) if ea else None,
          '| FDR' , any('FDR' in (n or '') or 'Franklin D. Roosevelt' in (n or '') for n in names), 'York', any('York Avenue' in (n or '') for n in names))
PY
echo "done $(date)"
