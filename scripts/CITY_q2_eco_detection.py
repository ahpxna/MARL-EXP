#!/usr/bin/env python3
"""Q2 (research/city_sim/PROTOCOL_CITY_Q2_ECO_DETECTION_20261002.md, written 19:0x EDT 02/10/2026): does eco-driving hide queues
from lights that sense halting vehicles?  SUMO grid4; lights FT (static), ACT (SUMO actuated, own induction loops), HQ
(halting-count max-queue), VQ (vehicle-count max-queue); a share rho of vehicles run a rule-based eco-approach (coast to a
crawl on red / yellow, no SPaT).  No learning.  Per vehicle: time loss, waiting time, stops, fuel; per run: hidden-queue mass
H = share of vehicle-seconds within 100 m upstream of a red / yellow head with 0.1 < v < 5 m/s.
Usage: CITY_q2_eco_detection.py --out DIR [--smoke] [--workers 2]"""
from __future__ import annotations
import argparse, hashlib, itertools, json, math, sys, time
from multiprocessing import Pool
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
NET = {'FT': 'research/city_sim/net/grid4.net.xml', 'ACT': 'research/city_sim/net/grid4_actuated.net.xml',
       'HQ': 'research/city_sim/net/grid4.net.xml', 'VQ': 'research/city_sim/net/grid4.net.xml'}
ROU = 'research/city_sim/demand/grid4/rou_s{}.xml'
ZONE, CRAWL, TGUESS, DT, MIN_G, MAX_G = 200.0, 3.0, 15.0, 5, 5, 60


def run_one(job):
    mode, rho, seed, end, out = job
    import libsumo as ls, sumolib
    from scripts.CITY_env import NetInfo, _stable_u
    info = NetInfo(str(ROOT / NET['FT'])); ti = Path(out) / 'tripinfo' / f'{mode}_r{rho}_s{seed}.xml'; ti.parent.mkdir(parents=True, exist_ok=True)
    cmd = [sumolib.checkBinary('sumo'), '-n', str(ROOT / NET[mode]), '-r', str(ROOT / ROU.format(seed)), '--seed', str(seed),
           '--no-step-log', '--no-warnings', '--time-to-teleport', '300', '--step-length', '1', '--device.emissions.probability', '1',
           '--tripinfo-output', str(ti), '--tripinfo-output.write-unfinished']
    ls.start(cmd); eco, ctrl = set(), set(); teleports = 0; hid = tot = 0; t0 = time.perf_counter()
    count = ls.lane.getLastStepHaltingNumber if mode == 'HQ' else ls.lane.getLastStepVehicleNumber
    try:
        while ls.simulation.getTime() < end and (ls.simulation.getMinExpectedNumber() > 0 or ls.simulation.getTime() < 10):
            ls.simulationStep(); t = int(ls.simulation.getTime()); teleports += ls.simulation.getStartingTeleportNumber()
            for v in ls.simulation.getDepartedIDList():
                if _stable_u(seed, v) < rho:
                    eco.add(v)
            for v in ls.simulation.getArrivedIDList():
                eco.discard(v); ctrl.discard(v)
            if mode in ('HQ', 'VQ') and t % DT == 0:              # max-queue light on halting (HQ) or vehicle (VQ) counts
                for tid, d in info.tls.items():
                    ph = ls.trafficlight.getPhase(tid)
                    if ph not in d['greens']:
                        continue
                    cur = d['greens'].index(ph); spent = ls.trafficlight.getSpentDuration(tid)
                    c = [sum(count(l) for l in s) for s in d['serve']]
                    if spent >= MIN_G and (spent >= MAX_G or c[1 - cur] >= c[cur] + 1):
                        ls.trafficlight.setPhase(tid, (d['greens'][cur] + 1) % d['n_phases'])
                    else:
                        ls.trafficlight.setPhaseDuration(tid, 1e5)
            for v in list(eco):                                       # eco-approach: coast to a crawl on red / yellow
                nt = ls.vehicle.getNextTLS(v)
                if nt and nt[0][2] <= ZONE and nt[0][3] in 'rRyYu':
                    sp = ls.vehicle.getSpeed(v); vt = max(CRAWL, nt[0][2] / TGUESS)
                    if vt < sp or v in ctrl:
                        ls.vehicle.setSpeed(v, min(vt, max(sp, CRAWL))); ctrl.add(v)
                elif v in ctrl:
                    ls.vehicle.setSpeed(v, -1); ctrl.discard(v)
            if t % 2 == 0:                                            # hidden-queue mass (all vehicles)
                for v in ls.vehicle.getIDList():
                    nt = ls.vehicle.getNextTLS(v)
                    if nt and nt[0][2] <= 100 and nt[0][3] in 'rRyYu':
                        tot += 1; sp = ls.vehicle.getSpeed(v); hid += (0.1 < sp < 5.0)
    finally:
        ls.close()
    rows = []
    for x in sumolib.xml.parse(str(ti), 'tripinfo'):
        em = x.emissions[0] if x.hasChild('emissions') else None
        rows.append((float(x.timeLoss), float(x.waitingTime), float(x.waitingCount), float(em.fuel_abs) if em is not None else math.nan,
                     float(x.arrival) >= 0, _stable_u(seed, x.id) < rho))
    A = np.array(rows, float)
    return dict(mode=mode, rho=rho, seed=seed, n=len(A), finished=float(A[:, 4].mean()), timeloss=float(A[:, 0].mean()),
                waiting=float(A[:, 1].mean()), stops=float(A[:, 2].mean()), fuel_g=float(np.nanmean(A[:, 3]) / 1000),
                timeloss_eco=float(A[A[:, 5] > 0, 0].mean()) if (A[:, 5] > 0).any() else math.nan,
                timeloss_human=float(A[A[:, 5] == 0, 0].mean()) if (A[:, 5] == 0).any() else math.nan,
                hidden_mass=hid / max(1, tot), teleports=teleports, wall_s=time.perf_counter() - t0)


def report(rows, out):
    R = {(r['mode'], r['rho'], r['seed']): r for r in rows}; seeds = sorted({r['seed'] for r in rows}); rhos = sorted({r['rho'] for r in rows})
    modes = [m for m in ('FT', 'ACT', 'HQ', 'VQ') if any(r['mode'] == m for r in rows)]

    def rel(m, rho, s, key='timeloss'):
        return R[(m, rho, s)][key] / R[(m, 0.0, s)][key] - 1

    L = ['Q2 mean time loss (s) by light mode and eco share (mean over seeds ' + str(seeds) + ')',
         'mode | ' + ' | '.join(f'rho {r}' for r in rhos)]
    for m in modes:
        L.append(f'{m} | ' + ' | '.join(f'{np.mean([R[(m, r, s)]["timeloss"] for s in seeds]):.1f}' for r in rhos))
    L.append('mean waiting time (s): ' + '; '.join(f'{m} ' + ' / '.join(f'{np.mean([R[(m, r, s)]["waiting"] for s in seeds]):.1f}' for r in rhos) for m in modes))
    L.append('stops per vehicle: ' + '; '.join(f'{m} ' + ' / '.join(f'{np.mean([R[(m, r, s)]["stops"] for s in seeds]):.2f}' for r in rhos) for m in modes))
    L.append('fuel g per vehicle: ' + '; '.join(f'{m} ' + ' / '.join(f'{np.mean([R[(m, r, s)]["fuel_g"] for s in seeds]):.1f}' for r in rhos) for m in modes))
    L.append('hidden-queue mass H: ' + '; '.join(f'{m} ' + ' / '.join(f'{np.mean([R[(m, r, s)]["hidden_mass"] for s in seeds]):.3f}' for r in rhos) for m in modes))
    L.append('finished share / teleports: ' + '; '.join(f'{m} ' + ' / '.join(f'{np.mean([R[(m, r, s)]["finished"] for s in seeds]):.3f}:{np.mean([R[(m, r, s)]["teleports"] for s in seeds]):.0f}' for r in rhos) for m in modes))
    pred = {}
    if 0.5 in rhos:
        ft = [rel('FT', 0.5, s) for s in seeds]
        pred['E1 FT |dTL(0.5)| <= 3 %'] = dict(value=float(np.mean(ft)), pass_=bool(abs(np.mean(ft)) <= 0.03))
        rng = np.random.default_rng(0)

        def excess(m):
            e = np.array([rel(m, 0.5, s) - rel('FT', 0.5, s) for s in seeds])
            bs = [e[rng.integers(0, len(e), len(e))].mean() for _ in range(4000)]
            return float(e.mean()), [float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))]
        if 'HQ' in modes:
            eh, ci = excess('HQ'); pred['E2 HQ excess over FT >= 5 points'] = dict(value=eh, ci=ci, pass_=bool(eh >= 0.05))
            if 'VQ' in modes:
                ev, civ = excess('VQ'); pred['E3 VQ excess < half of HQ'] = dict(VQ=ev, ci=civ, HQ=eh, pass_=bool(ev < eh / 2))
            wt = [np.mean([R[('HQ', r, s)]['waiting'] for s in seeds]) for r in rhos]; tl = [np.mean([R[('HQ', r, s)]['timeloss'] for s in seeds]) for r in rhos]
            pred['E5 HQ waiting falls while time loss does not (reported)'] = dict(waiting=wt, timeloss=tl, pass_=bool(wt[-1] < wt[0] and tl[-1] >= tl[0]))
            hq_ex = [np.mean([rel('HQ', r, s) - rel('FT', r, s) for s in seeds]) for r in rhos[1:]]
            hm = [np.mean([R[('FT', r, s)]['hidden_mass'] for s in seeds]) for r in rhos[1:]]
            pred['E6 H(rho) from FT runs ranks HQ excess (reported)'] = dict(H=hm, excess=hq_ex, pass_=bool(np.all(np.diff(hq_ex) * np.diff(hm) >= 0)))
        if 'ACT' in modes:
            ea, cia = excess('ACT'); pred['E4 ACT excess over FT (reported)'] = dict(value=ea, ci=cia, pass_=True)
    L += [f'{k}: {"SUPPORTED" if v["pass_"] else "NOT SUPPORTED"} {json.dumps({kk: vv for kk, vv in v.items() if kk != "pass_"})}' for k, v in pred.items()]
    txt = '\n'.join(L); print(txt, flush=True); (out / 'report.txt').write_text(txt + '\n')
    return pred


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=a.smoke)
    if a.smoke:
        jobs = [(m, r, 0, 600, str(out)) for m in ('FT', 'ACT', 'HQ', 'VQ') for r in (0.0, 0.5)]
    else:
        jobs = [(m, r, s, 5400, str(out)) for m in ('FT', 'ACT', 'HQ', 'VQ') for r in (0.0, 0.25, 0.5, 0.75) for s in range(5)]
    t0 = time.perf_counter(); rows = []
    with Pool(a.workers) as pool:
        for r in pool.imap_unordered(run_one, jobs):
            rows.append(r); print(f'[{time.perf_counter() - t0:.0f}s] {r["mode"]} rho {r["rho"]} s{r["seed"]}: TL {r["timeloss"]:.1f} wait {r["waiting"]:.1f} '
                                  f'stops {r["stops"]:.2f} H {r["hidden_mass"]:.3f} fin {r["finished"]:.3f} tele {r["teleports"]}', flush=True)
            (out / 'rows.json').write_text(json.dumps(rows, indent=1))
    src = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    pred = report(rows, out)
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_sha256=src, n_jobs=len(jobs), smoke=a.smoke,
                                                       protocol='research/city_sim/PROTOCOL_CITY_Q2_ECO_DETECTION_20261002.md'), indent=1))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True); ap.add_argument('--smoke', action='store_true')
    ap.add_argument('--workers', type=int, default=2); main(ap.parse_args())
