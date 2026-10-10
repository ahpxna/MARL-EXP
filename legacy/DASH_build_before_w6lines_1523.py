#!/usr/bin/env python3
"""Dashboard builder (02/10/2026 22:5x EDT; user 22:4x: "robust hơn, cập nhật dễ, phân ra kết quả tốt và xấu").

Reads research/dashboard/registry.json (one entry per experiment), parses every listed report for registered prediction lines
("<label> -> SUPPORTED", "<label>: NOT SUPPORTED {...}", "-> not tested"), classifies them (tốt / xấu / chưa test / chỉ báo cáo,
with the registry's caveats), reads progress (log iterations, manifest counts) and running processes, extracts the chart data
of the entries that name a chart, and writes data.json ATOMICALLY (temporary file + os.replace) into every --out directory,
plus index.html (copied from research/dashboard/index.html).  It never raises: any failure of one source becomes an 'error'
field of that source and the rest is still written.
Usage: python3 scripts/DASH_build.py [--out DIR ...] [--watch SECONDS]

05/10 extension (user: "viết cái khung để stream data"): adding an experiment needs ONLY a registry entry.
  * generic verdict lines: any report line with VERDICT / CANDIDATE / OPPORTUNITY / HELPS / IMPROVES / FEEDBACK / CALIBRATION is classified
    by keywords (good: SUPPORTED, PASS, YES, True, HELPS, DEGRADES, INFO-LIMITED; bad: REJECTED, NOT SUPPORTED, FAIL, NO, False, NOT SHOWN,
    NOT DETECTED; else info); an entry's "verdict_map" {substring: class} overrides; identical lines are kept once.
  * chart "contrasts": every report line '<name>: <metric> v [lo, hi] (up u) | ...' (metrics fuel_agent / timeloss / timeloss_agent /
    timeloss_human, or 'agent fuel %' / 'city TL' / 'agent TL' / 'human TL') becomes a row; one chart per entry (key c_<id>).
  * global "_frontier": every contrast named '... - R' or '... vs R' (or in the entry's "frontier" list) is a point (agent TL, agent fuel),
    with the M3 gate box (fuel < 0, agent TL < +0.5) drawn by the page.
"""
from __future__ import annotations
import argparse, glob, json, os, re, shutil, subprocess, sys, time, traceback
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REG = ROOT / 'research/dashboard/registry.json'
PAGE = ROOT / 'research/dashboard/index.html'
OUTS = [ROOT / 'research/dashboard', ROOT / 'research/marl_budget/dashboard_20261002']
VERDICT = re.compile(r'^(?P<label>.+?)\s*(?:->|:)\s*(?P<v>NOT SUPPORTED|SUPPORTED|not tested)\b(?P<rest>.*)$')
PID = re.compile(r'^\s*([A-Za-z][A-Za-z0-9]*(?:-\d+|\d+)[a-z]?)\b')
NUM = r'[-+]?\d+(?:\.\d+)?'


def parse_predictions(text, caveats):
    out = []
    for line in text.splitlines():
        m = VERDICT.match(line.strip())
        if not m:
            continue
        label = m.group('label').strip(); v = m.group('v'); rest = m.group('rest').strip()
        cls = {'SUPPORTED': 'good', 'NOT SUPPORTED': 'bad', 'not tested': 'untested'}[v]
        if '(reported)' in label or label.startswith('B4 ') or 'exploratory' in label.lower():
            cls = 'info'
        note = None
        for c in caveats or []:
            if c.get('match') and c['match'] in label:
                note = c.get('note')
                if c.get('class') == 'void':
                    cls = 'void'
                elif c.get('class') == 'caveat' and cls in ('good', 'bad'):
                    cls = cls + '_caveat'
        rest = re.sub(r'(-?\d+\.\d{3})\d+', r'\1', rest)            # 0.70230059 -> 0.702
        pid = PID.match(label); out.append(dict(id=pid.group(1) if pid else '', label=label[:220], verdict=v, cls=cls,
                                                 detail=rest[:260], note=note))
    return out


GEN_LINE = re.compile(r'(VERDICT|CANDIDATE|OPPORTUNITY|HELPS|IMPROVES|FEEDBACK|CALIBRATION|OVERALL)')
GOODW = ('SUPPORTED', 'PASS', 'YES', 'True', 'HELPS', 'DEGRADES', 'INFO-LIMITED')
BADW = ('REJECTED', 'NOT SUPPORTED', 'FAIL', ' NO', ':NO', 'False', 'NOT SHOWN', 'NOT DETECTED')


def parse_generic(text, vmap):
    out, seen = [], set()
    for line in text.splitlines():
        l = line.strip()
        if not l or l in seen or not GEN_LINE.search(l) or VERDICT.match(l):
            continue
        seen.add(l); cls = None
        for k, c in (vmap or {}).items():
            if k in l:
                cls = c; break
        if cls is None:
            head, _, tail = l.partition(':'); t = tail or head
            if any(w in t for w in BADW):
                cls = 'bad'
            elif any(w in t for w in GOODW):
                cls = 'good'
            else:
                cls = 'info'
        label, _, detail = l.partition(':')
        out.append(dict(id='', label=label[:220], verdict=detail.strip()[:60], cls=cls, detail=detail.strip()[:260], note=None))
    return out


MET = re.compile(r'(?P<m>fuel_agent|timeloss_agent|timeloss_human|timeloss|agent fuel %|city TL|agent TL|human TL)\s+(?P<v>[-+]?\d+\.\d+)\s*%?'
                 r'(?:\s*\[(?P<lo>[-+]?\d+\.\d+),\s*(?P<hi>[-+]?\d+\.\d+)\])?(?:\s*\((?:lo\s*[-+]?\d+\.\d+,\s*)?up\s*(?P<up>[-+]?\d+\.\d+)\))?')
MNAME = {'fuel_agent': 'fuel', 'agent fuel %': 'fuel', 'timeloss': 'cityTL', 'city TL': 'cityTL', 'timeloss_agent': 'agentTL', 'agent TL': 'agentTL',
         'timeloss_human': 'humanTL', 'human TL': 'humanTL'}


def ch_contrasts(text):
    rows, seen = [], set()
    for line in text.splitlines():
        if '|' not in line or ':' not in line:
            continue
        name, _, rest = line.strip().partition(':'); name = name.strip()
        mets = {}
        for seg in rest.split('|'):
            mm = MET.search(seg)
            if mm:
                k = MNAME[mm.group('m')]
                if k not in mets:
                    mets[k] = {x: (float(mm.group(x)) if mm.group(x) else None) for x in ('v', 'lo', 'hi', 'up')}
        if len(mets) >= 2 and name and name not in seen and len(name) < 80:
            seen.add(name); rows.append(dict(name=name, m=mets))
    return dict(kind='contrasts', rows=rows)


def progress(spec):
    files = sorted(glob.glob(str(ROOT / spec['glob'])))
    if spec['kind'] == 'manifests':
        return dict(label=spec['label'], done=len(files), total=spec['total'])
    rx = re.compile(spec['regex']); items = []
    for f in files:
        last = 0
        try:
            with open(f, 'rb') as fh:
                fh.seek(max(0, os.path.getsize(f) - 20000)); tail = fh.read().decode('utf-8', 'replace')
            for mm in rx.finditer(tail):
                last = int(mm.group(1))
            done = (Path(f[:-4]) / 'manifest.json').exists() if f.endswith('.log') else False
        except Exception:
            done = False
        items.append(dict(name=Path(f).stem, it=spec['total'] if done else last, done=done))
    return dict(label=spec['label'], items=items, total=spec['total'])


def running():
    pats = {'test D (distill v11, 4×4)': 'MARL_e3_actor_distill_v11', 'fallback eval': 'MARL_e3_fallback_eval',
            'NYC (wrapper)': 'MARL_nyc_wrapper', 'E3 eval': 'MARL_e3_ageclip_eval', 'SUMO city (Q-runs)': 'CITY_q', 'SUMO live viewer': 'CITY_live_viewer', 'Lean': 'lake env lean'}
    try:
        ps = subprocess.run(['ps', '-axo', 'pid,etime,pcpu,command'], capture_output=True, text=True, timeout=10).stdout.splitlines()
    except Exception as e:
        return dict(error=str(e))
    def secs(et):
        d, _, hms = et.rpartition('-'); f = [int(x) for x in hms.split(':')]
        while len(f) < 3:
            f.insert(0, 0)
        return (int(d) if d else 0) * 86400 + f[0] * 3600 + f[1] * 60 + f[2]
    res = {}
    for name, p in pats.items():
        hits = []
        for l in ps[1:]:
            f = l.split(None, 3)
            if len(f) < 4 or p not in f[3]:
                continue
            exe = Path(f[3].split()[0]).name
            if exe in ('zsh', 'bash', 'sh', '-zsh', 'grep', 'disclaimer') or 'run_with_watchdog' in f[3] or 'caffeinate' == exe:
                continue
            hits.append(f)
        if hits:
            top = max(hits, key=lambda f: secs(f[1]))
            res[name] = dict(n=len(hits), longest=top[1])
    try:
        res['_load'] = os.getloadavg()[0]
    except Exception:
        pass
    return res


# ----- chart extractors: each takes the report text and returns a JSON-able dict ---------------------------------------
def ch_gain_rows(text):
    """'arm | K=1 +1.99 [0.44, 3.51] | K=2 ...' (test C / D) -> {arm: {K: [mean, lo, hi]}}."""
    out = {}
    for line in text.splitlines():
        parts = [p.strip() for p in line.split('|')]
        if len(parts) < 3 or not parts[0] or '=' in parts[0] or ' ' in parts[0]:
            continue
        row = {}
        for p in parts[1:]:
            m = re.match(rf'(K=\d|iid)\s+({NUM})\s+\[({NUM}),\s*({NUM})\]', p)
            if m:
                row[m.group(1)] = [float(m.group(2)), float(m.group(3)), float(m.group(4))]
        if row:
            out[parts[0]] = row
    return dict(kind='gainbars', series=out)


def ch_g4tm(text):
    out = {}
    for line in text.splitlines():
        m = re.match(rf'(\w+) \| (K=\d|iid) \| ({NUM}) % \[({NUM}), ({NUM})\]', line.strip())
        if m:
            out.setdefault(m.group(1), {})[m.group(2)] = [float(m.group(3)), float(m.group(4)), float(m.group(5))]
    return dict(kind='gainbars', series=out)


def ch_q7(text):
    rows = {}
    for line in text.splitlines():
        parts = [p.strip() for p in line.split('|')]
        if len(parts) >= 3 and parts[0] in ('FT', 'ACT', 'RL-H', 'RL-C', 'RL-J'):
            r = {}
            for p in parts[1:]:
                m = re.match(rf'(human|L-ACT|L-RLH) ({NUM})', p)
                if m:
                    r[m.group(1)] = float(m.group(2))
            rows[parts[0]] = r
    return dict(kind='grouped', categories=list(rows), groups=['human', 'L-ACT', 'L-RLH'],
                values={g: [rows[c].get(g) for c in rows] for g in ['human', 'L-ACT', 'L-RLH']}, ylabel='time loss (s/xe)')


def ch_q3(text):
    hdr = None; series = {}
    for line in text.splitlines():
        parts = [p.strip() for p in line.split('|')]
        if parts[0] == 'mode':
            hdr = [p.replace('p ', '') for p in parts[1:]]
        elif parts[0].endswith(' age') and hdr:
            series[parts[0].replace(' age', '')] = [float(x) for x in parts[1:]]
    return dict(kind='lines', x=hdr, series=series, xlabel='chu kỳ sinh xe p (s) — trái: thưa, phải: dày', ylabel='tuổi tin (s)')


def ch_q2(text):
    hdr = None; series = {}
    for line in text.splitlines():
        parts = [p.strip() for p in line.split('|')]
        if parts[0] == 'mode':
            hdr = [p.replace('rho ', 'ρ ') for p in parts[1:]]
        elif hdr and parts[0] in ('FT', 'ACT', 'HQ', 'VQ') and len(parts) == len(hdr) + 1:
            series[parts[0]] = [float(x) for x in parts[1:]]
    return dict(kind='lines', x=hdr, series=series, xlabel='tỷ lệ xe eco', ylabel='time loss (s)')


def ch_q4(text):
    pts = []
    for line in text.splitlines():
        parts = [p.strip() for p in line.split('|')]
        if len(parts) >= 8 and re.match(r'^(\d+|RANDOM)$', parts[0]):
            try:
                pts.append(dict(name=parts[0], tv=float(parts[1]), delta=float(parts[2]), density=float(parts[7])))
            except ValueError:
                pass
    return dict(kind='scatter', points=pts, xlabel='TV của corridor', ylabel='Δ (thiệt hại xe cũ)')


def ch_fallback(text):
    out = {}; net = None; arm = None
    for line in text.splitlines():
        m = re.match(r'== (\S+):', line)
        if m:
            net = m.group(1); continue
        m = re.match(r'(\w+)\s+calibration false alarm', line)
        if m:
            arm = m.group(1); continue
        m = re.match(r'\s+(K\d|iid) \| (.*)$', line)
        if m and net and arm:
            cells = {}
            for p in m.group(2).split(' | '):
                mm = re.match(rf'(\w+) ({NUM}) \[({NUM}), ({NUM})\] \(({NUM})\)', p.strip())
                if mm:
                    cells[mm.group(1)] = [float(mm.group(2)), float(mm.group(3)), float(mm.group(4)), float(mm.group(5))]
            out.setdefault(net, {}).setdefault(arm, {})[m.group(1)] = cells
    return dict(kind='fallback', nets=out)


CHARTS = {'testC': ch_gain_rows, 'testD': ch_gain_rows, 'g4tm': ch_g4tm, 'q7': ch_q7, 'q3': ch_q3, 'q2': ch_q2, 'q4': ch_q4,
          'fallback': ch_fallback, 'contrasts': ch_contrasts}


def build():
    data = dict(generated=time.strftime('%d/%m/%Y %H:%M:%S'), errors=[], experiments=[], charts={})
    try:
        reg = json.loads(REG.read_text())
    except Exception as e:
        data['errors'].append(f'registry: {e}'); return data
    data['banner'] = reg.get('banner')
    for e in reg.get('experiments', []):
        item = {k: e.get(k) for k in ('id', 'title', 'track', 'network', 'ledger', 'protocol', 'note', 'report')}
        try:
            rp = ROOT / e['report']
            if rp.exists():
                text = rp.read_text(errors='replace'); item['predictions'] = parse_predictions(text, e.get('caveats')) + parse_generic(text, e.get('verdict_map'))
                item['updated'] = time.strftime('%d/%m %H:%M', time.localtime(rp.stat().st_mtime)); item['status'] = 'done'
                if e.get('chart') in CHARTS:
                    key = f"c_{e['id']}" if e['chart'] == 'contrasts' else e['chart']
                    try:
                        data['charts'][key] = dict(title=e['title'], **CHARTS[e['chart']](text))
                        if e['chart'] == 'contrasts':
                            fl = e.get('frontier')
                            for r in data['charts'][key]['rows']:
                                n = r['name']
                                if (fl is not None and n in fl) or (fl is None and (n.endswith(' - R') or n.endswith(' vs R'))):
                                    if 'fuel' in r['m'] and 'agentTL' in r['m'] and (abs(r['m']['agentTL']['v']) > 15 or abs(r['m']['fuel']['v']) > 30):
                                        data['charts'].setdefault('_frontier', dict(kind='frontier', title='Frontier: agent fuel vs agent time (mọi arm so với R)', points=[])).setdefault('excluded', []).append(f"{e['id']}: {n}")
                                    elif 'fuel' in r['m'] and 'agentTL' in r['m']:
                                        data['charts'].setdefault('_frontier', dict(kind='frontier', title='Frontier: agent fuel vs agent time (mọi arm so với R)', points=[]))['points'].append(
                                            dict(exp=e['id'], name=n.replace(' - R', '').replace(' vs R', ''), fuel=r['m']['fuel'], agentTL=r['m']['agentTL'], panel=e.get('network', '')))
                    except Exception as ce:
                        data['charts'][key] = dict(title=e['title'], error=f'{type(ce).__name__}: {ce}')
            else:
                item['predictions'] = []; item['status'] = 'pending'
            item['progress'] = []
            for spec in e.get('progress', []):
                try:
                    item['progress'].append(progress(spec))
                except Exception as pe:
                    item['progress'].append(dict(label=spec.get('label'), error=str(pe)))
        except Exception as ex:
            item['error'] = f'{type(ex).__name__}: {ex}'; item['status'] = 'error'
            data['errors'].append(f"{e.get('id')}: {traceback.format_exc(limit=1).strip()[-300:]}")
        data['experiments'].append(item)
    data['running'] = running()
    cnt = {}
    for it in data['experiments']:
        for p in it.get('predictions', []):
            cnt[p['cls']] = cnt.get(p['cls'], 0) + 1
    data['counts'] = cnt
    return data


def write(data, outs):
    blob = json.dumps(data, ensure_ascii=False, indent=1)
    for d in outs:
        try:
            d = Path(d); d.mkdir(parents=True, exist_ok=True); tmp = d / '.data.json.tmp'
            tmp.write_text(blob, encoding='utf-8'); os.replace(tmp, d / 'data.json')
            if PAGE.exists() and PAGE.resolve() != (d / 'index.html').resolve():
                tmp2 = d / '.index.html.tmp'; shutil.copyfile(PAGE, tmp2); os.replace(tmp2, d / 'index.html')
        except Exception as e:
            print(f'write {d}: {e}', file=sys.stderr)


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', nargs='*', default=None); ap.add_argument('--watch', type=float, default=0)
    a = ap.parse_args(); outs = [Path(x) for x in a.out] if a.out else OUTS
    while True:
        d = build(); write(d, outs)
        print(f"[{d['generated']}] {sum(d['counts'].values())} predictions {d['counts']}, errors {len(d['errors'])}", flush=True)
        if not a.watch:
            break
        time.sleep(a.watch)
