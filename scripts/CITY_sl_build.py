#!/usr/bin/env python3
"""F1-0 (PROTOCOL_CITY_F1_SALTLAKE_20261008): Salt Lake City corridors from RESCO with recorded 2023 demand.
  demand <site> <role>   per day: RESCO's own utils/csv_to_flo.generate_flow_from_csv (imported unchanged; its config module is replaced
                         by a namespace with map, flow 1.0, start 57600, end 61200, uuid) on a scratch copy of the .flo.xml with the signal
                         CSV folders linked; random seeded by the day of year; departures shifted by -57600 (16:00 -> 0); uuid4 vehicle ids
                         replaced in departure order by v<doy>_<k>.  Output research/city_sim/demand/saltlake/<site>/rou_s<doy>.xml.
                         KSL-1: vehicles per (route, 5-min interval) equal RESCO's output for the same seed (identity check after the
                         id remap) and the CSV-total comparison is reported.
  programs <site>        four greens from RESCO's phase states [EW protected lefts, EW all green, NS protected lefts, NS all green] in
                         lead-left order, each followed by a 3-s yellow (G/g that turns r -> y) and a 1-s all-red; FT durations by
                         Webster from the TRAIN days' per-route volumes (critical route group per green, s = 1800 veh/h/lane,
                         lost time 4 s per phase, cycle clipped to [60, 150]); netconvert --tllogic-files into
                         research/city_sim/net/saltlake_<site>.net.xml.  KSL-3: every link green (G/g) in >= 1 green, yellows 3 s, all-reds 1 s.
Roles: train (weekdays 9 Jan - 28 Apr), tune (1-4 May), dev (10 weekdays from 5 Jun), conf (20: every third weekday from 5 Sep;
only on request, after a non-existence check).  Sites: 400sX200w, stateXuniversity."""
import datetime as dt, json, os, random, shutil, subprocess, sys, tempfile, types, re
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT)); sys.path.insert(0, str(ROOT / 'external_assets/RESCO'))
ENV = ROOT / 'external_assets/RESCO/resco_benchmark/environments'; DEM = ROOT / 'research/city_sim/demand/saltlake'; NET = ROOT / 'research/city_sim/net'
SITES = {'400sX200w': ('saltlake2_400sX200w', ['7241', '7242']), 'stateXuniversity': ('saltlake2_stateXuniversity', ['7243', '7142'])}
MISSING = {'stateXuniversity': [(dt.datetime(2023, 2, 9, 11, 20), dt.datetime(2023, 2, 13, 9, 5))], '400sX200w': []}
BIN = ROOT / 'external_envs/city_runtime/bin'


def weekdays(a, b):
    d = a; out = []
    while d <= b:
        if d.weekday() < 5:
            out.append(d)
        d += dt.timedelta(days=1)
    return out


def days(site, role):
    bad = lambda d: any(s.date() <= d.date() <= e.date() for s, e in MISSING[site])  # noqa: E731
    if role == 'train':
        L = weekdays(dt.datetime(2023, 1, 9), dt.datetime(2023, 4, 28))
    elif role == 'tune':
        L = weekdays(dt.datetime(2023, 5, 1), dt.datetime(2023, 5, 4))
    elif role == 'dev':
        L = weekdays(dt.datetime(2023, 6, 5), dt.datetime(2023, 6, 30))[:10]
    elif role == 'conf':
        L = weekdays(dt.datetime(2023, 9, 5), dt.datetime(2023, 12, 29))[::3][:20]
    else:
        raise ValueError(role)
    return [d for d in L if not bad(d)]


def resco_flow(site, day, outdir):
    name, sigs = SITES[site]; cfgm = types.ModuleType('resco_benchmark.config.config')
    cfg = types.SimpleNamespace(map=name, flow=1.0, start_time=57600, end_time=61200, uuid=f'f1_{day:%Y%m%d}')
    cfgm.config = cfg
    for m in ('resco_benchmark', 'resco_benchmark.config'):
        sys.modules.setdefault(m, types.ModuleType(m))
    sys.modules['resco_benchmark.config.config'] = cfgm
    if 'resco_benchmark.utils.csv_to_flo' in sys.modules:
        del sys.modules['resco_benchmark.utils.csv_to_flo']
    import importlib.util
    spec = importlib.util.spec_from_file_location('resco_benchmark.utils.csv_to_flo', ENV.parent / 'utils/csv_to_flo.py')
    C = importlib.util.module_from_spec(spec); sys.modules['resco_benchmark.utils.csv_to_flo'] = C; spec.loader.exec_module(C)
    flo = Path(outdir) / f'{name}.flo.xml'
    if not flo.exists():
        shutil.copy(ENV / name / f'{name}.flo.xml', flo)
        for s in sigs:
            os.symlink(ENV / name / s, Path(outdir) / s)
    random.seed(day.timetuple().tm_yday)
    fp, n = C.generate_flow_from_csv(day, str(flo))
    return fp, n


def demand(site, role):
    out = DEM / site; out.mkdir(parents=True, exist_ok=True); tmp = tempfile.mkdtemp(prefix='sl_'); rep = []
    if role == 'conf':
        for d in days(site, role):
            if (out / f'rou_s{d.timetuple().tm_yday}.xml').exists():
                print('KSL conf FAIL: exists', d); sys.exit(1)
    for d in days(site, role):
        doy = d.timetuple().tm_yday; fp, n = resco_flow(site, d, tmp); tree = ET.parse(fp); root = tree.getroot()
        vs = [e for e in root if e.tag == 'vehicle']; ref = Counter((e.get('route'), int(e.get('depart')) // 300) for e in vs)
        for e in vs:
            root.remove(e)
        vs.sort(key=lambda e: (int(e.get('depart')), e.get('route'), e.get('id')))
        for k, e in enumerate(vs):
            e.set('id', f'v{doy}_{k}'); e.set('depart', str(int(e.get('depart')) - 57600)); root.append(e)
        tree.write(out / f'rou_s{doy}.xml')
        chk = Counter((e.get('route'), (int(e.get('depart')) + 57600) // 300) for e in vs)
        rep.append(dict(day=str(d.date()), doy=doy, vehicles=len(vs), resco_count=n, ksl1=(chk == ref)))
        os.remove(fp)
    ok = all(r['ksl1'] for r in rep); (out / f'demand_{role}.json').write_text(json.dumps(rep, indent=1))
    print(f'{site} {role}: {len(rep)} days, vehicles/h mean {sum(r["vehicles"] for r in rep) / len(rep):.0f}; KSL-1 {"PASS" if ok else "FAIL"}')
    shutil.rmtree(tmp); return ok


def greens_of(site):
    name, _ = SITES[site]; net = ET.parse(ENV / name / f'{name}.net.xml').getroot(); G = {}
    for tl in net.iter('tlLogic'):
        ph = [p.get('state') for p in tl.iter('phase')]
        G[tl.get('id')] = [ph[4], ph[3], ph[8], ph[7]]                 # EW prot. lefts, EW all green, NS prot. lefts, NS all green
    return G


def transition(a, b):
    y = ''.join('y' if (c in 'Gg' and d not in 'Gg') else (c if c in 'Gg' else ('s' if c == 's' else 'r')) for c, d in zip(a, b))
    r = ''.join('r' if c in 'Gg' and d not in 'Gg' else (c if (c in 'Gg' and d in 'Gg') else ('s' if c == 's' else 'r')) for c, d in zip(a, b))
    return y, r


def webster(site, G):
    """Per light: flow ratio y_i of each green = max over the routes it serves of (veh/h) / (1800 * lanes); C = (1.5 L + 5) / (1 - Y)."""
    name, _ = SITES[site]; vol = Counter(); nd = 0
    for d in days(site, 'train'):
        f = DEM / site / f'rou_s{d.timetuple().tm_yday}.xml'
        for e in ET.parse(f).getroot().iter('vehicle'):
            vol[e.get('route')] += 1
        nd += 1
    vol = {k: v / nd for k, v in vol.items()}
    net = ET.parse(ENV / name / f'{name}.net.xml').getroot(); routes = {r.get('id'): r.get('edges').split() for r in
                                                                        ET.parse(ENV / name / f'{name}.flo.xml').getroot().iter('route')}
    conn = defaultdict(list)                                           # tl -> link index -> (from edge, to edge, from lane)
    for c in net.iter('connection'):
        if c.get('tl') is not None:
            conn[c.get('tl')].append((int(c.get('linkIndex')), c.get('from'), c.get('to')))
    nl = {e.get('id'): len(list(e.iter('lane'))) for e in net.iter('edge')}
    out = {}
    for tl, gs in G.items():
        y = []
        for st in gs:
            green_moves = {(f, t) for (i, f, t) in conn[tl] if st[i] in 'Gg'}; best = 0.0
            for rid, edges in routes.items():
                for f, t in zip(edges, edges[1:]):
                    if (f, t) in green_moves:
                        lanes = max(1, sum(1 for (i, ff, tt) in conn[tl] if ff == f and tt == t and st[i] in 'Gg'))
                        best = max(best, vol.get(rid, 0.0) / (1800.0 * lanes))
            y.append(best)
        Y = min(sum(y), 0.9); L = 4 * 4.0; C = min(150.0, max(60.0, (1.5 * L + 5) / (1 - Y))); eff = C - L
        g = [max(5.0, eff * yi / max(1e-9, sum(y))) for yi in y]; out[tl] = dict(y=y, C=C, g=[round(x) for x in g])
    return out


def programs(site, durations=None, outname=None, write_tll=None):
    G = greens_of(site); W = webster(site, G); name, _ = SITES[site]; tll = ['<tlLogics>']; rep = {}
    if durations is not None:
        for tl in W:
            W[tl]['g'] = list(durations[tl])
    for tl, gs in G.items():
        ph = []; trans_ok = True
        for k, st in enumerate(gs):
            nx = gs[(k + 1) % 4]; y, r = transition(st, nx)
            if 'y' not in y:                                           # A4: no link loses green (protected -> permissive left): the old
                ph += [(W[tl]['g'][k] + 4, st)]                        # yellow + all-red repeated this state for 4 s; merged into the green
            else:
                ph += [(W[tl]['g'][k], st), (3, y), (1, r)]; trans_ok &= not any(c in 'Gg' for c in r)
        tll.append(f'  <tlLogic id="{tl}" type="static" programID="f1" offset="0">')
        tll += [f'    <phase duration="{d}" state="{s}"/>' for d, s in ph]; tll.append('  </tlLogic>')
        cover = [i for i in range(len(gs[0])) if not any(st[i] in 'Gg' for st in gs)]
        rep[tl] = dict(webster=W[tl], uncovered_links=cover, yellow_ok=all(d == 3 for d, s in ph if 'y' in s), allred_ok=trans_ok,
                       phases=[(d, s) for d, s in ph])
    tll.append('</tlLogics>'); f = Path(write_tll) if write_tll else DEM / site / 'f1_programs.tll.xml'; f.write_text('\n'.join(tll) + '\n')
    if write_tll:
        return f
    out = NET / (outname or f'saltlake_{site}.net.xml')
    subprocess.run([str(BIN / 'netconvert'), '-s', str(ENV / name / f'{name}.net.xml'), '--tllogic-files', str(f), '-o', str(out),
                    '--no-warnings'], check=True, capture_output=True)
    txt = out.read_text(); n0 = txt.count('<tlLogic ')                  # A4: keep only programID f1 (RESCO's programs stayed in the net, and
    txt = re.sub(r'\n\s*<tlLogic id="[^"]+" type="static" programID="(?!f1")[^"]*"[^>]*>.*?</tlLogic>', '', txt, flags=re.S)   # NetInfoK read them)
    out.write_text(txt); rep['tlLogic_removed'] = n0 - txt.count('<tlLogic ')
    from scripts.CITY_lightk import NetInfoK
    ng = {tl: len(v['greens']) for tl, v in NetInfoK(str(out)).tls.items()}; rep['KSL-3b_greens'] = ng   # A4: exactly the 4 greens
    ok = all(not r['uncovered_links'] and r['yellow_ok'] and r['allred_ok'] for k, r in rep.items() if k not in ('KSL-3b_greens', 'tlLogic_removed')) and all(v == 4 for v in ng.values())
    (DEM / site / 'programs.json').write_text(json.dumps(rep, indent=1)); print(json.dumps(rep, indent=1)); print(f'KSL-3 {"PASS" if ok else "FAIL"} -> {out}')
    return ok


if __name__ == '__main__':
    cmd, site = sys.argv[1], sys.argv[2]
    ok = demand(site, sys.argv[3]) if cmd == 'demand' else programs(site)
    sys.exit(0 if ok else 1)
