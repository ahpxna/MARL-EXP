#!/usr/bin/env python3
"""Q3 (research/city_sim/PROTOCOL_CITY_Q3_INFO_FUNDAMENTAL_20261002.md, written 19:0x EDT 02/10/2026): the information
fundamental diagram of vehicle-carried neighbour information.  SUMO grid4, FT and ACT lights, six demand levels, seeds 0–2.
A vehicle entering a light-to-light link (j -> i) takes j's snapshot; it delivers it within R m of i's stop line.  Per
light-second: age of i's freshest copy of j.  Per (mode, demand, seed, link): mean / p50 / p90 / p99 age, no-copy share, mean
speed u (when occupied), flow q (entries per second), density.  No learning.
Usage: CITY_q3_info_fd.py --out DIR [--smoke] [--workers 2]"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from multiprocessing import Pool
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
NET = {'FT': 'research/city_sim/net/grid4.net.xml', 'ACT': 'research/city_sim/net/grid4_actuated.net.xml'}
LEVELS = ['8', '4', '2', '1.4', '1.0', '0.8', '0.5', '0.35', '0.25']; R_DELIVER, WARM, END = 100.0, 600, 5400


def run_one(job):
    mode, p, seed, end, out = job
    import libsumo as ls, sumolib
    net = sumolib.net.readNet(str(ROOT / NET['FT']))
    links = [e for e in net.getEdges() if e.getFunction() != 'internal' and e.getFromNode().getType() == 'traffic_light'
             and e.getToNode().getType() == 'traffic_light']
    L = {e.getID(): e.getLength() for e in links}; lanes = {e.getID(): e.getLaneNumber() for e in links}; ids = list(L)
    rou = ROOT / 'research/city_sim/demand/grid4_levels' / f'rou_p{p.replace(".", "_")}_s{seed}.xml'
    ls.start([sumolib.checkBinary('sumo'), '-n', str(ROOT / NET[mode]), '-r', str(rou), '--seed', str(seed), '--no-step-log',
              '--no-warnings', '--time-to-teleport', '300', '--step-length', '1'])
    on = {}; last = {e: None for e in ids}; ages = {e: [] for e in ids}; nocopy = {e: 0 for e in ids}; entries = {e: 0 for e in ids}
    spd = {e: [] for e in ids}; dens = {e: [] for e in ids}; t0 = time.perf_counter(); teleports = 0
    try:
        while ls.simulation.getTime() < end:
            ls.simulationStep(); t = int(ls.simulation.getTime()); teleports += ls.simulation.getStartingTeleportNumber()
            for e in ids:
                vs = ls.edge.getLastStepVehicleIDs(e)
                for v in vs:
                    st = on.get(v)
                    if st is None or st[0] != e:
                        on[v] = [e, t, False]; entries[e] += t >= WARM; st = on[v]
                    if not st[2] and ls.vehicle.getLanePosition(v) >= L[e] - R_DELIVER:
                        st[2] = True; last[e] = t if last[e] is None else max(last[e], st[1]); last[e] = max(last[e], st[1])
                if t >= WARM:
                    if last[e] is None:
                        nocopy[e] += 1
                    else:
                        ages[e].append(t - last[e])
                    if vs:
                        spd[e].append(ls.edge.getLastStepMeanSpeed(e))
                    dens[e].append(len(vs) / (L[e] * lanes[e]))
            if ls.simulation.getMinExpectedNumber() == 0 and t > WARM + 60:
                break
    finally:
        ls.close()
    cells = []
    dur = max(1, t - WARM)
    for e in ids:
        a = np.array(ages[e], float)
        cells.append(dict(link=e, L=L[e], n=len(a), mean=float(a.mean()) if len(a) else float('nan'),
                          p50=float(np.percentile(a, 50)) if len(a) else float('nan'), p90=float(np.percentile(a, 90)) if len(a) else float('nan'),
                          p99=float(np.percentile(a, 99)) if len(a) else float('nan'), nocopy=nocopy[e] / dur,
                          u=float(np.mean(spd[e])) if spd[e] else float('nan'), q=entries[e] / dur, k=float(np.mean(dens[e]))))
    np.savez_compressed(Path(out) / 'ages' / f'{mode}_p{p}_s{seed}.npz', **{e: np.array(ages[e], np.int32) for e in ids})
    return dict(mode=mode, p=p, seed=seed, cells=cells, teleports=teleports, t_end=t, wall_s=time.perf_counter() - t0)


def report(rows, out):
    modes = sorted({r['mode'] for r in rows}); levels = [p for p in LEVELS if any(r['p'] == p for r in rows)]
    agg = {}
    for m in modes:
        for p in levels:
            cs = [c for r in rows if r['mode'] == m and r['p'] == p for c in r['cells'] if c['n'] > 0]
            agg[(m, p)] = dict(mean=float(np.mean([c['mean'] for c in cs])), nocopy=float(np.mean([c['nocopy'] for c in cs])),
                               u=float(np.nanmean([c['u'] for c in cs])), q=float(np.mean([c['q'] for c in cs])), k=float(np.mean([c['k'] for c in cs])))
    L = ['Q3 network-mean age of vehicle-carried neighbour information (s), by demand (period p s; mean over links and seeds)',
         'mode | ' + ' | '.join(f'p {p}' for p in levels)]
    for m in modes:
        L.append(f'{m} age | ' + ' | '.join(f'{agg[(m, p)]["mean"]:.1f}' for p in levels))
        L.append(f'{m} no-copy share | ' + ' | '.join(f'{agg[(m, p)]["nocopy"]:.3f}' for p in levels))
        L.append(f'{m} speed u (m/s) | ' + ' | '.join(f'{agg[(m, p)]["u"]:.2f}' for p in levels))
        L.append(f'{m} flow q (veh/s) | ' + ' | '.join(f'{agg[(m, p)]["q"]:.3f}' for p in levels))
        L.append(f'{m} density k (veh/m/lane) | ' + ' | '.join(f'{agg[(m, p)]["k"]:.4f}' for p in levels))
    pred = {}
    for m in modes:
        means = [agg[(m, p)]['mean'] for p in levels]; i = int(np.argmin(means))
        interior = 0 < i < len(levels) - 1; ends = means[0] >= 1.5 * means[i] and means[-1] >= 1.5 * means[i]
        pred[f'I1 {m} U shape (interior minimum, both ends >= 1.5x)'] = dict(means=means, argmin=levels[i], pass_=bool(interior and ends))
        cs = [c for r in rows if r['mode'] == m for c in r['cells'] if c['n'] > 0 and c['q'] > 0 and c['u'] > 0]
        meas = np.array([c['mean'] for c in cs]); pr1 = np.array([(c['L'] - R_DELIVER) / c['u'] + 1 / c['q'] for c in cs])
        pr2 = np.array([(c['L'] - R_DELIVER) / c['u'] + 0.5 / c['q'] for c in cs])
        r1, r2 = float(np.corrcoef(meas, pr1)[0, 1]), float(np.corrcoef(meas, pr2)[0, 1])
        pred[f'I2 {m} closed form Pearson >= 0.9 (c = 1)'] = dict(pearson_c1=r1, pearson_c_half=r2, n=len(cs),
                                                                 mean_ratio_c1=float(np.mean(meas / pr1)), pass_=bool(r1 >= 0.9))
        ref = np.concatenate([np.load(Path(out) / 'ages' / f'{m}_p2_s{s}.npz')[e] for s in (0, 1, 2) if (Path(out) / 'ages' / f'{m}_p2_s{s}.npz').exists()
                              for e in np.load(Path(out) / 'ages' / f'{m}_p2_s{s}.npz').files])
        if len(ref):
            p99 = float(np.percentile(ref, 99)); share = {}
            for p in (levels[0], levels[-1]):
                arr = np.concatenate([np.load(Path(out) / 'ages' / f'{m}_p{p}_s{s}.npz')[e] for s in (0, 1, 2)
                                      if (Path(out) / 'ages' / f'{m}_p{p}_s{s}.npz').exists() for e in np.load(Path(out) / 'ages' / f'{m}_p{p}_s{s}.npz').files])
                share[p] = float(np.mean(arr > p99)) if len(arr) else float('nan')
            pred[f'I3 {m} support exit at both ends >= 20 %'] = dict(train_p99=p99, share=share, pass_=bool(all(v >= 0.2 for v in share.values())))
    L += [f'{k}: {"SUPPORTED" if v["pass_"] else "NOT SUPPORTED"} {json.dumps({kk: vv for kk, vv in v.items() if kk != "pass_"})}' for k, v in pred.items()]
    txt = '\n'.join(L); print(txt, flush=True); (out / 'report.txt').write_text(txt + '\n')
    (out / 'agg.json').write_text(json.dumps({f'{m}|{p}': v for (m, p), v in agg.items()}, indent=1))


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=a.smoke); (out / 'ages').mkdir(exist_ok=True)
    jobs = ([(m, p, 0, 1500, str(out)) for m in ('FT',) for p in ('8', '2', '0.8')] if a.smoke else
            [(m, p, s, END, str(out)) for m in ('FT', 'ACT') for p in LEVELS for s in (0, 1, 2)])
    t0 = time.perf_counter(); rows = []
    with Pool(a.workers) as pool:
        for r in pool.imap_unordered(run_one, jobs):
            rows.append(r); mm = np.nanmean([c['mean'] for c in r['cells']])
            print(f'[{time.perf_counter() - t0:.0f}s] {r["mode"]} p {r["p"]} s{r["seed"]}: mean age {mm:.1f} tele {r["teleports"]} t_end {r["t_end"]}', flush=True)
            (out / 'rows.json').write_text(json.dumps(rows, indent=1))
    if a.smoke:
        for r in rows:
            r['p'] = r['p']
    report(rows, out)
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                                                       n_jobs=len(jobs), smoke=a.smoke,
                                                       protocol='research/city_sim/PROTOCOL_CITY_Q3_INFO_FUNDAMENTAL_20261002.md'), indent=1))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True); ap.add_argument('--smoke', action='store_true')
    ap.add_argument('--workers', type=int, default=2); main(ap.parse_args())
