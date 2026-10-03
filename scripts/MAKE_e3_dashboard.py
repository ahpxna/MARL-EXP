#!/usr/bin/env python3
"""Local dashboard of the E3 compatibility evidence (02/10/2026 01:1x EDT; user 01:0x "chiếu lên localhost").  Reads only
existing result files (no simulation) and writes research/marl_budget/dashboard_20261002/index.html; re-run to refresh.
Interim numbers are labelled as such (train-match seeds 0–3, the 4×4 replication seed 0)."""
from __future__ import annotations
import glob, json, os, subprocess, sys, time
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT)); os.chdir(ROOT)
M = Path('research/marl_budget'); OUT = M / 'dashboard_20261002'; OUT.mkdir(exist_ok=True)


def rows(path, rule=None):
    r = json.loads((Path(path) / 'rows.json').read_text())
    return {x['episode']: x['queue_sum'] for x in r if rule is None or x.get('rule') == rule}


def gain(R, Z):
    e = sorted(set(R) & set(Z)); return -(sum(R[k] for k in e) / sum(Z[k] for k in e) - 1) * 100


def g4():
    D = M / 'e3_g4_s0_devlook_20261001'; Z = rows(D / 'Zdev', 'none'); dev = {}
    for K in ('1', '2', '3', '4', '5', '6', '0'):
        f = np.load(D / f'NF_{"iid" if K == "0" else "const" + K}' / 'flags.npz')
        dev[K] = dict(gain=gain(rows(D / f'R_K{K}', 'prefix'), Z), netZ=float(f['protoS'].mean() - f['zok'].mean()))
    c = json.loads((M / 'e3_channel_composition_20261001/g4_nopolicy/composition.json').read_text()); comp = {}
    for K in dev:
        h = c[K]['age_hist']; st = c[K]['steps']; nev = c[K]['never']; F = int(K) if K != '0' else c[K]['entries'] - sum(h[1:]) / st
        comp[K] = dict(F=round(F, 2), never=round(nev, 2), B3=round(c[K]['B3'], 2), net_rel=round(F - (sum(h[10:]) / st + nev), 2),
                       net_abs=round(F - (sum(h[3:]) / st + nev), 2))
    P = M / 'e3_g4_replication_20261001'; rep = {}
    if (P / 'Z_s0/manifest.json').exists():
        Z0 = rows(P / 'Z_s0', 'none')
        for t, rule, name in (('R_s0_iid', 'prefix', 'iid'), ('R_s0_iid', 'cap4', 'cap4'), ('R_s0_low', 'prefix', 'low')):
            if (P / t / 'manifest.json').exists():
                rep[name] = round(gain(rows(P / t, rule), Z0), 2)
    A = M / 'e3_grid4x4_20260930/actors'; actors = []
    for log in sorted(A.glob('*.log')):
        n = log.stem; done = (A / n / 'manifest.json').exists(); state = (A / n / 'state_last.pt').exists()
        last = log.read_text(errors='ignore').strip().splitlines()[-1][:90] if log.stat().st_size else ''
        best = json.loads((A / n / 'manifest.json').read_text()).get('best_select') if done else None
        actors.append(dict(name=n, done=done, resumable=state, best=best, last=last))
    return dict(dev=dev, comp=comp, rep=rep, actors=actors)


def g3():
    CELLS = [('prefix', 'iid'), ('prefix', 'cap4'), ('prefix', 'low'), ('agefirst', 'cap4'), ('agefirst', 'low'), ('agefirst', 'iid'),
             ('agefirst', 'const1'), ('agefirst', 'const2'), ('agefirst', 'const3')]
    from scripts.MARL_e3_witness_burden_report import gains
    g = gains(); cells = []
    for o, c in CELLS:
        pd = (M / f'e3_order_dose_20261001/{o}_{c}_s{{}}') if (o, c) in CELLS[:5] else None
        F = S = N = B = 0.0
        for s in range(10):
            p = (M / f'e3_order_dose_20261001/{o}_{c}_s{s}') if pd else (M / f'e3_viewstats_v2_20261001/s{s}_K{0 if c == "iid" else int(c[5:])}')
            z = np.load(p / 'flags.npz'); F += z['n_fresh'].mean() / 10; S += z['n_stale'].mean() / 10
            N += (z['n_nbr'] - z['n_fresh'] - z['n_relay']).mean() / 10; B += z['b3'].mean() / 10
        cells.append(dict(cell=f'{o}/{c}', net=round(F - S - N, 2), B3=round(B, 2), gain=round(g[(o, c)], 2), kind='order x capacity'))
    C = json.loads((M / 'e3_net_count_20261001/composition.json').read_text())
    HD = json.loads((M / 'e3_hold_dose_report_20261001.json').read_text()); HP = json.loads((M / 'e3_hold_prospective_report_20261001.json').read_text())
    for K, r in [(2, 1), (2, 2), (2, 3), (2, 4), (2, 6), (3, 1), (3, 4), (3, 6)]:
        x = C[f'agefirst:{r}:const{K}']
        cells.append(dict(cell=f'hold K{K} r{r} (dev)', net=round(x['net'], 2), B3=round(x['B3'], 2), gain=round(float(np.mean(HD[f'K{K}_r{r}'])), 2), kind='hold-r development'))
        if f'K{K}_r{r}' in HP:
            cells.append(dict(cell=f'hold K{K} r{r} (prospective)', net=round(x['net'], 2), B3=round(x['B3'], 2),
                              gain=round(float(np.mean(HP[f'K{K}_r{r}']['gain'])), 2), kind='hold-r prospective'))
    return cells


def train_match():
    import scripts.MARL_e3_train_match_report as T
    out = {}
    for s in range(5):
        try:
            Z = T.load(f'Z_s{s}', 'none', f'distill_none_s{s}')
            R = {(a, K): T.load(f'R_{a}_s{s}_K{K}', 'prefix', f'{a}_s{s}') for a in ('relayCK1_st', 'relay6Cage_st') for K in (1, 0)}
        except Exception:
            continue
        if Z is None or any(v is None for v in R.values()):
            continue
        out[s] = {f'{a}|K{K}': round(T.gain(R[(a, K)], Z), 2) for a in ('relayCK1_st', 'relay6Cage_st') for K in (1, 0)}
    return out


def age_curves():
    b = json.loads((M / 'e3_age_response_20261001/age_response_K1.json').read_text())
    c = json.loads((M / 'e3_age_response_shift_20261001/relayCK1/age_response_K1.json').read_text())
    S = [s for s in ('0', '1', '2', '3') if s in c]
    return dict(iid_trained=np.mean([b[s]['acc_by_age'] for s in S], 0).round(3).tolist(), k1_trained=np.mean([c[s]['acc_by_age'] for s in S], 0).round(3).tolist(), seeds=S)


def status():
    ps = subprocess.run(['ps', '-axo', 'etime,command'], capture_output=True, text=True).stdout.splitlines()
    keys = {'train-match seed 4 (v9)': 'relayCK1_st_s4', 'arch control (shared-concat / attention)': 'relaySCCage_st|relayAttnCage_st',
            '4x4 chain': 'e3_grid4x4_20260930'}
    out = {}
    for k, pat in keys.items():
        hits = [l for l in ps if any(p in l for p in pat.split('|')) and 'python' in l.lower() and 'watchdog' not in l]
        out[k] = f'{len(hits)} process(es)'
    load = os.getloadavg()[0]; return dict(jobs=out, load=round(load, 1), time=time.strftime('%Y-%m-%d %H:%M:%S'))


def main():
    data = dict(g4=g4(), g3=g3(), tm=train_match(), age=age_curves(), status=status())
    (OUT / 'data.json').write_text(json.dumps(data, indent=1, default=float))
    html = (ROOT / 'scripts' / 'e3_dashboard_template.html').read_text().replace('__DATA__', json.dumps(data, default=float))
    (OUT / 'index.html').write_text(html); print('wrote', OUT / 'index.html', data['status'])


if __name__ == '__main__':
    main()
