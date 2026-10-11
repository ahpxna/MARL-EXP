import json, re, collections
from pathlib import Path
M = Path('/Users/phanan/cig-amf-main/research/marl_budget')
FORBID = {'e3_g4_mix_20261002', 'e3_fallback_20261002', 'e3_nyc16x3_20261002', 'e3_age_emulation_20261003'}
inv = []
for top in sorted(M.iterdir()):
    if not top.is_dir() or top.name in FORBID or not re.search(r'2026100[123]', top.name): continue
    for d in sorted(top.glob('*/manifest.json')):
        try: m = json.loads(d.read_text())
        except Exception: continue
        a = m.get('args', {}) or {}
        if isinstance(a, list): a = {}
        ck = a.get('relay') or ''
        if not ck and a.get('actors'): ck = a['actors'][0].split('=')[-1]
        fam = re.sub(r'_s\d+$', '', ck.split('/')[-2]) if ck.count('/') >= 1 else (ck or '?')
        seed = re.search(r'_s(\d+)/', ck); seed = int(seed.group(1)) if seed else None
        ts = a.get('traffic_seeds') or []
        src = list((m.get('source_hashes') or {}).keys())[:1]
        inv.append(dict(top=top.name, tag=d.parent.name, status=m.get('status'), sc=m.get('self_check'), fam=fam, seed=seed,
                        K=m.get('K', a.get('K', a.get('capacity'))), A=a.get('A'), project=a.get('project'), sched=a.get('schedule'),
                        panel=(ts[0], ts[-1], len(ts)) if ts else None, script=src[0].split('/')[-1] if src else None,
                        sha=bool(m.get('checkpoint_sha256')), arch=a.get('arch')))
json.dump(inv, open('/private/tmp/claude-502/-Users-phanan-cig-amf-main/976002e4-6f9b-4c75-8890-ea54dcea033f/scratchpad/agentB/w2/inventory.json', 'w'), default=str)
g = collections.defaultdict(lambda: collections.Counter())
for r in inv:
    key = (r['top'], r['panel'][0] if r['panel'] else None, r['script'])
    g[key][(r['fam'], str(r['K']), str(r['A']), str(r['project']), str(r['sched']))] += 1
for k, c in g.items():
    print(k); 
    for kk, v in sorted(c.items()): print('    ', kk, v)
