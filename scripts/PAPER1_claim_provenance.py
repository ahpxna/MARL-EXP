#!/usr/bin/env python3
"""P0 provenance scan for the paper-1 claim map (03/10/2026; PAPER1_DESTINATION_AND_CLOSURE_20261003 P0).
Reads only existing manifests / rows (no simulation).  Per panel directory: number of run manifests, COMPLETE / PASS counts,
producer scripts named in source_hashes and whether each recorded hash equals the CURRENT file (a mismatch means the file
changed after the run — the current source did NOT necessarily produce the artefact), checkpoint sha recorded and equal to
the current checkpoint file, actor seeds, traffic seeds and headways.  Output: <out>/provenance.json and a text table.
"""
import argparse, glob, hashlib, json, re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
M = 'research/marl_budget/'
PANELS = {
    '2701_3x3_ten_seed': M + 'e3_ten_seed_panel_20260930',
    '2801_3x3_frontier': M + 'e3_demand_frontier_20261001',
    '3201_3x3_train_match': M + 'e3_train_match_20261001',
    '3301_4x4_constk': M + 'e3_g4_constk_20261001',
    '3801_3x3_mixed': M + 'e3_mixed_channel_20261002',
    '4201_4x4_train_match': M + 'e3_g4_train_match_20261002',
    '4601_4x4_mix': M + 'e3_g4_mix_20261002',
    '4801_3x3_fallback': M + 'e3_fallback_20261002/3x3',
    '4901_4x4_fallback': M + 'e3_fallback_20261002/4x4',
    '4801_3x3_mahal': M + 'e3_fallback_mahal_20261003/3x3',
    '4901_4x4_mahal': M + 'e3_fallback_mahal_20261003/4x4',
    '5101_3x3_emulation': M + 'e3_age_emulation_20261003/3x3',
    '5101_4x4_emulation': M + 'e3_age_emulation_20261003/4x4',
    '5201_3x3_throttle': M + 'e3_joint_throttle_20261003/3x3',
    '5201_4x4_throttle': M + 'e3_joint_throttle_20261003/4x4',
    'dev901_flip': M + 'e3_crosschannel_flip_20261003',
}
_sha_cache = {}


def sha(p):
    p = ROOT / p
    if p not in _sha_cache:
        _sha_cache[p] = hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None
    return _sha_cache[p]


def scan(d):
    fs = sorted(glob.glob(str(ROOT / d / '**' / 'manifest.json'), recursive=True))
    fs = [f for f in fs if '/smoke' not in f]
    st = Counter(); prod = {}; ck = Counter(); seeds = set(); tseeds = set(); heads = set(); prefixes = Counter()
    for f in fs:
        m = json.loads(Path(f).read_text()); a = m.get('args', {}) or {}
        st[(m.get('status'), m.get('self_check'))] += 1
        run = Path(f).parent.name; prefixes[re.sub(r'_s\d+.*', '', run)] += 1
        s = re.search(r'_s(\d+)', run)
        if s:
            seeds.add(int(s.group(1)))
        for k, v in (m.get('source_hashes') or {}).items():
            if k.startswith('scripts/') and ('eval' in k or 'probe' in k):
                cur = sha(k); e = prod.setdefault(k, Counter()); e['equal' if v == cur else 'DIFFERS'] += 1
        rel = a.get('relay') or a.get('actors')
        rec = m.get('checkpoint_sha256') or m.get('relay_sha256')
        if isinstance(rec, dict):                       # probes record {role: sha}; compare each role with its args path
            ok = all(a.get(r) and sha(a[r]) == v for r, v in rec.items() if isinstance(v, str))
            ck['equal (per role)' if ok else 'DIFFERS (per role)'] += 1
        elif isinstance(rel, str) and '=' not in rel:
            if rec is None:
                ck['no sha recorded'] += 1
            else:
                ck['equal' if rec == sha(rel) else 'DIFFERS'] += 1
        else:
            ck['n/a (Z / multi-actor)' if rec is None else ('equal' if rel and rec == sha(rel.split('=')[1]) else 'recorded')] += 1
        ts = a.get('traffic_seeds') or m.get('traffic_seeds') or []
        tseeds.update(int(x) for x in ts if str(x).isdigit() or isinstance(x, int))
        heads.update(a.get('headways') or [])
    return dict(dir=d, manifests=len(fs), status={f'{k[0]}/{k[1]}': v for k, v in st.items()}, run_prefixes=dict(prefixes),
                producers={k: dict(v) for k, v in prod.items()}, checkpoint_sha=dict(ck), actor_seeds=sorted(seeds),
                traffic_seeds=[min(tseeds), max(tseeds), len(tseeds)] if tseeds else None, headways=sorted(heads))


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    res = {k: scan(v) for k, v in PANELS.items()}
    ri = ROOT / M / 'ri_age_role_20261002/results.json'
    if ri.exists():
        r = json.loads(ri.read_text()); rec = r.get('source_sha256')
        res['RI_age_role'] = dict(dir=str(ri.relative_to(ROOT)), recorded_sha=rec,
                                  producer='scripts/RI_age_role_testbed.py', equal_current=rec == sha('scripts/RI_age_role_testbed.py'))
    (out / 'provenance.json').write_text(json.dumps(res, indent=1))
    lines = []
    for k, v in res.items():
        if 'manifests' not in v:
            lines.append(f'{k}: {v}'); continue
        lines.append(f"{k}: {v['manifests']} manifests {v['status']}; seeds {v['actor_seeds']}; traffic {v['traffic_seeds']} x {v['headways']}")
        lines.append(f"    producers {v['producers']}")
        lines.append(f"    checkpoint sha {v['checkpoint_sha']}; runs {v['run_prefixes']}")
    (out / 'provenance.txt').write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', default='research/papers/audits/paper1_claim_map_20261003')
    main(p.parse_args())
