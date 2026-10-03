#!/usr/bin/env python3
"""Q2b (research/city_sim/PROTOCOL_CITY_Q2B_ECO_ROBUSTNESS_20261002.md, written 19:3x EDT 02/10/2026; derived from
scripts/CITY_q2_eco_detection.py): robustness of the eco-driving × sensing harm to the eco design (CRAWL3/5/7, GLOSA) and
light-side fixes (ACT_GAP5, ACT_FAR, DELAY).  Q2 question: does eco-driving hide queues
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
       'ACT_GAP5': 'research/city_sim/net/grid4_actuated_gap5.net.xml', 'ACT_FAR': 'research/city_sim/net/grid4_actuated_far.net.xml',
       'DELAY': 'research/city_sim/net/grid4_delay.net.xml', 'HQ': 'research/city_sim/net/grid4.net.xml', 'VQ': 'research/city_sim/net/grid4.net.xml'}
ROU = 'research/city_sim/demand/grid4_levels/rou_p{}_s{}.xml'
LIGHTS = ['FT', 'ACT', 'ACT_GAP5', 'ACT_FAR', 'DELAY', 'HQ', 'VQ']; ECO = ['CRAWL3', 'CRAWL5', 'CRAWL7', 'GLOSA']; DEMAND = ['2', '1_0']


def time_to_green(ls, tid, li, now):
    """SUMO's prediction: remaining time of the current phase plus program durations of the following phases until li is green."""
    logic = ls.trafficlight.getAllProgramLogics(tid)[0]; ph = ls.trafficlight.getPhase(tid); n = len(logic.phases)
    if logic.phases[ph].state[li] in 'Gg':
        return 0.0
    t = ls.trafficlight.getNextSwitch(tid) - now; k = (ph + 1) % n
    for _ in range(n):
        if logic.phases[k].state[li] in 'Gg':
            return t
        t += logic.phases[k].duration; k = (k + 1) % n
    return t
ZONE, CRAWL, TGUESS, DT, MIN_G, MAX_G = 200.0, 3.0, 15.0, 5, 5, 60


def run_one(job):
    mode, rho, seed, end, out, eco_v, dem = job
    import libsumo as ls, sumolib
    from scripts.CITY_env import NetInfo, _stable_u
    info = NetInfo(str(ROOT / NET['FT'])); ti = Path(out) / 'tripinfo' / f'{mode}_{eco_v}_d{dem}_r{rho}_s{seed}.xml'; ti.parent.mkdir(parents=True, exist_ok=True)
    cmd = [sumolib.checkBinary('sumo'), '-n', str(ROOT / NET[mode]), '-r', str(ROOT / ROU.format(dem, seed)), '--seed', str(seed),
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
                    sp = ls.vehicle.getSpeed(v); crawl = {'CRAWL5': 5.0, 'CRAWL7': 7.0}.get(eco_v, CRAWL)
                    if eco_v == 'GLOSA' and mode not in ('HQ', 'VQ'):
                        tg = time_to_green(ls, nt[0][0], nt[0][1], ls.simulation.getTime()); vt = max(2.0, nt[0][2] / max(tg, 1.0))
                    else:
                        vt = max(crawl, nt[0][2] / TGUESS)
                    if vt < sp or v in ctrl:
                        ls.vehicle.setSpeed(v, min(vt, max(sp, 2.0))); ctrl.add(v)
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
    return dict(mode=mode, eco=eco_v, demand=dem, rho=rho, seed=seed, n=len(A), finished=float(A[:, 4].mean()), timeloss=float(A[:, 0].mean()),
                waiting=float(A[:, 1].mean()), stops=float(A[:, 2].mean()), fuel_g=float(np.nanmean(A[:, 3]) / 1000),
                timeloss_eco=float(A[A[:, 5] > 0, 0].mean()) if (A[:, 5] > 0).any() else math.nan,
                timeloss_human=float(A[A[:, 5] == 0, 0].mean()) if (A[:, 5] == 0).any() else math.nan,
                hidden_mass=hid / max(1, tot), teleports=teleports, wall_s=time.perf_counter() - t0)


def report(rows, out):
    R = {(r['mode'], r['eco'], r['demand'], r['rho'], r['seed']): r for r in rows}; seeds = sorted({r['seed'] for r in rows})
    dems = [d for d in DEMAND if any(r['demand'] == d for r in rows)]; ecos = [e for e in ECO if any(r['eco'] == e for r in rows)]

    def rel(m, e, d, s):
        return R[(m, e, d, 0.5, s)]['timeloss'] / R[(m, 'NONE', d, 0.0, s)]['timeloss'] - 1

    def excess(m, e, d):
        return float(np.mean([rel(m, e, d, s) - rel('FT', e, d, s) for s in seeds]))
    L = ['Q2b excess over FT (points of relative time-loss change at rho = 0.5) by light (rows) and eco variant (columns)']
    for d in dems:
        L.append(f'demand p{d}: light | ' + ' | '.join(ecos) + ' | FT dTL / stops change (same variant)')
        for m in [x for x in LIGHTS[1:] if any(r['mode'] == x for r in rows)]:
            L.append(f'  {m} | ' + ' | '.join(f'{100 * excess(m, e, d):+.1f}' for e in ecos))
        L.append('  FT | ' + ' | '.join(f'{100 * np.mean([rel("FT", e, d, s) for s in seeds]):+.1f}% / '
                                       f'{100 * np.mean([R[("FT", e, d, 0.5, s)]["stops"] / R[("FT", "NONE", d, 0.0, s)]["stops"] - 1 for s in seeds]):+.1f}%' for e in ecos))
    pred = {}
    b1 = {f'{e}|{d}': excess('ACT', e, d) for e in ecos for d in dems}
    pred['B1 ACT excess >= +10 points for every eco variant and demand'] = dict(values=b1, pass_=bool(all(v >= 0.10 for v in b1.values())))
    if 'GLOSA' in ecos:
        b2 = {d: dict(dTL=float(np.mean([rel('FT', 'GLOSA', d, s) for s in seeds])),
                      dstops=float(np.mean([R[('FT', 'GLOSA', d, 0.5, s)]['stops'] / R[('FT', 'NONE', d, 0.0, s)]['stops'] - 1 for s in seeds]))) for d in dems}
        pred['B2 FT GLOSA: dTL <= +3 % and stops -15 %'] = dict(values=b2, pass_=bool(all(v['dTL'] <= 0.03 and v['dstops'] <= -0.15 for v in b2.values())))
    b3 = {}
    for e in [x for x in ('CRAWL3', 'GLOSA') if x in ecos]:
        for d in dems:
            ea = excess('ACT', e, d); fixes = {m: excess(m, e, d) for m in ('ACT_GAP5', 'ACT_FAR', 'DELAY') if any(r['mode'] == m for r in rows)}
            b3[f'{e}|{d}'] = dict(ACT=ea, **fixes, ok=[m for m, v in fixes.items() if v <= ea / 2])
    pred['B3 a light-side fix halves the ACT excess (CRAWL3, GLOSA; every demand)'] = dict(values=b3, pass_=bool(b3 and all(v['ok'] for v in b3.values())))
    b4 = {f'{e}|{d}': (excess('HQ', e, d) - excess('VQ', e, d)) / max(1e-9, excess('HQ', e, d)) for e in ecos for d in dems}
    pred['B4 hidden-queue share of the HQ excess (reported)'] = dict(values=b4, pass_=True)
    L += [f'{k}: {"SUPPORTED" if v["pass_"] else "NOT SUPPORTED"} {json.dumps({kk: vv for kk, vv in v.items() if kk != "pass_"})}' for k, v in pred.items()]
    txt = '\n'.join(L); print(txt, flush=True); (out / 'report.txt').write_text(txt + '\n')
    return pred


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=a.smoke)
    if a.smoke:
        jobs = [(m, r, 0, 600, str(out), e, '2') for m in ('FT', 'ACT', 'DELAY', 'HQ', 'VQ') for r, e in ((0.0, 'NONE'), (0.5, 'CRAWL3'), (0.5, 'GLOSA'))]
    else:
        jobs = [(m, r, s, 5400, str(out), e, d) for d in DEMAND for s in (0, 1, 2) for m in LIGHTS
                for r, e in [(0.0, 'NONE')] + [(0.5, x) for x in ECO]]
    t0 = time.perf_counter(); rows = []
    with Pool(a.workers) as pool:
        for r in pool.imap_unordered(run_one, jobs):
            rows.append(r); print(f'[{time.perf_counter() - t0:.0f}s] {r["mode"]} {r["eco"]} d{r["demand"]} rho {r["rho"]} s{r["seed"]}: TL {r["timeloss"]:.1f} '
                                  f'stops {r["stops"]:.2f} fin {r["finished"]:.3f} tele {r["teleports"]}', flush=True)
            (out / 'rows.json').write_text(json.dumps(rows, indent=1))
    pred = report(rows, out)
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                                                       n_jobs=len(jobs), smoke=a.smoke,
                                                       protocol='research/city_sim/PROTOCOL_CITY_Q2B_ECO_ROBUSTNESS_20261002.md'), indent=1))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True); ap.add_argument('--smoke', action='store_true')
    ap.add_argument('--workers', type=int, default=3); main(ap.parse_args())
