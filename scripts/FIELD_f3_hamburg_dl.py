#!/usr/bin/env python3
"""F3 download (PROTOCOL_FIELD_F2_F3T_F4_20261008, Amendment A3; user-approved 08/10): Hamburg traffic-light SensorThings data.
Systems (trafficLightsID, string order ascending) are scanned; a system qualifies with >= 4 connections whose laneType contains 'KFZ' and
that have a detector_car datastream with observations in the window.  The first 4 qualifying systems are kept, at most 6 connections each (Amendment A3b).  For each qualifying
connection, primary_signal and detector_car observations 2026-10-01T00:00Z .. 2026-10-08T00:00Z are fetched page by page ($select
phenomenonTime,result), one request at a time with a 0.2-s pause, into research/field_data/hamburg/<thing>_<layer>.csv.gz.
Stops at 300 MB raw response volume.  Manifest: research/field_data/hamburg/manifest.json.   W_SMOKE=1: 1 system, 1 day."""
import gzip, json, os, sys, time, urllib.parse, urllib.request
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; OUT = ROOT / ('research/field_data/hamburg_smoke' if os.environ.get('W_SMOKE') == '1' else 'research/field_data/hamburg'); OUT.mkdir(parents=True, exist_ok=True)
BASE = 'https://tld.iot.hamburg.de/v1.1/'; SM = os.environ.get('W_SMOKE') == '1'
T0, T1 = '2026-10-01T00:00:00Z', ('2026-10-02T00:00:00Z' if SM else '2026-10-08T00:00:00Z'); NSYS = 1 if SM else 4; CAP = 300e6; VOL = [0]


def get(url):
    for k in range(5):
        try:
            with urllib.request.urlopen(url, timeout=120) as r:
                b = r.read(); VOL[0] += len(b); time.sleep(0.2); return json.loads(b)
        except Exception as e:
            print('retry', k, e, flush=True); time.sleep(5 * (k + 1))
    raise RuntimeError(url)


def q(path, **kw):
    return BASE + path + '?' + urllib.parse.urlencode({f'${k}': v for k, v in kw.items()}, safe="(),/'$@ ").replace(' ', '%20')


systems, picked, url = {}, [], q('Things', orderby='properties/trafficLightsID asc', top='200',
                                  select='@iot.id,name,properties/trafficLightsID,properties/laneType',
                                  expand='Datastreams($select=@iot.id,properties/layerName)')
order = []
while url and len(picked) < NSYS:
    d = get(url); url = d.get('@iot.nextLink')
    for x in d['value']:
        sid = x['properties'].get('trafficLightsID'); lt = x['properties'].get('laneType') or ''
        if sid not in systems:
            systems[sid] = []; order.append(sid)
        ds = {s.get('properties', {}).get('layerName'): s['@iot.id'] for s in x.get('Datastreams', [])}
        if 'KFZ' in lt and 'detector_car' in ds and 'primary_signal' in ds:
            systems[sid].append(dict(thing=x['name'], ps=ds['primary_signal'], det=ds['detector_car']))
    for sid in order[:-1]:                                             # systems complete once the next one has started
        if sid in [p['sid'] for p in picked] or sid in getattr(sys.modules[__name__], '_seen', set()):
            continue
        _seen = getattr(sys.modules[__name__], '_seen', set()); _seen.add(sid); setattr(sys.modules[__name__], '_seen', _seen)
        C = systems[sid]
        if len(C) < 4:
            continue
        ok = [c for c in C if get(q(f'Datastreams({c["det"]})/Observations', top='1', select='phenomenonTime',
                                    filter=f'phenomenonTime ge {T0} and phenomenonTime lt {T1}'))['value']]
        if len(ok) >= 4:
            picked.append(dict(sid=sid, conns=ok[:6])); print('picked system', sid, len(ok), 'connections (kept 6)', flush=True)   # A3b
            if len(picked) >= NSYS:
                break
man = dict(window=[T0, T1], systems=picked, files=[])
for p in picked:
    for c in p['conns']:
        for layer, dsid in (('primary_signal', c['ps']), ('detector_car', c['det'])):
            fn = OUT / f'{c["thing"]}_{layer}.csv.gz'
            if fn.exists():
                man['files'].append(fn.name); continue
            url = q(f'Datastreams({dsid})/Observations', top='10000', select='phenomenonTime,result', orderby='phenomenonTime asc',
                    filter=f'phenomenonTime ge {T0} and phenomenonTime lt {T1}'); n = 0; rows = []
            while url:
                d = get(url); url = d.get('@iot.nextLink'); rows += [f'{o["phenomenonTime"]},{o["result"]}' for o in d['value']]; n += len(d['value'])
                if VOL[0] > CAP:
                    break
            with gzip.open(fn, 'wt') as f:
                f.write('time,result\n' + '\n'.join(rows) + '\n')
            man['files'].append(fn.name); print(f'{fn.name}: {n} obs; volume {VOL[0] / 1e6:.1f} MB', flush=True)
            if VOL[0] > CAP:
                print('CAP reached: stop'); break
        if VOL[0] > CAP:
            break
    if VOL[0] > CAP:
        break
man['volume_bytes'] = VOL[0]; (OUT / ('manifest_smoke.json' if SM else 'manifest.json')).write_text(json.dumps(man, indent=1))
print('done; systems', [p['sid'] for p in picked], 'files', len(man['files']), f'volume {VOL[0] / 1e6:.1f} MB')
