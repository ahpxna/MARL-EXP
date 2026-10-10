#!/usr/bin/env python3
"""Report of PROTOCOL_E3_REPAIR_PANEL_20261003.md (written 18:1x EDT 03/10, before any panel run; report written 18:4x, before
any panel run).  Main mode: the paired 4x4 table on panel 5301-5364 (gain vs Z per cell with two-level bootstrap CI, paired
differences vs PLAIN, intervention rates, harmful cells, worst cell, descriptive harm-blocked / benefit-retained ratios, costs,
detector false alarms) and the verdicts RP1-RP8 with the cell groups fixed in the protocol.  --rerun: the corrected FB_Mq on
every cell of 4901 (4x4) and 4801 (3x3) against the old FB_Mq rows of the same panels (before / after, same episodes).
Usage: MARL_e3_repair_panel_report.py [--smoke] [--rerun]"""
import argparse, json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); BASE = M / 'e3_repair_panel_20261003'
NAME = {1: 'K1', 0: 'iid', 2: 'K2', 3: 'K3'}; KS = (1, 0, 2, 3)
DETS = ['FB_S+', 'FB_S-', 'FB_M+', 'FB_M-', 'FB_Mq+', 'FB_Mq-']
ARMS = {'CK1': ['PLAIN', 'MASK'] + DETS + ['EMU', 'THR'], 'Cage': ['PLAIN', 'MASK'] + DETS, 'MIX': ['PLAIN']}
TAG = {'CK1': 'relayCK1_st', 'Cage': 'relayCage_st', 'MIX': 'relayMIX_st'}
OWN = {('CK1', 1), ('Cage', 0)}; HAZ = [('CK1', 0), ('Cage', 1)]; BEN = [('CK1', 2), ('CK1', 3), ('Cage', 2), ('Cage', 3)]
PKT_BYTES = 25


def gain(x, y, ii=None):
    return -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100


class Panel:
    def __init__(self, eps):
        self.eps = eps; self.TS = sorted({e.split('_')[0] for e in eps})
        self.IDX = {u: [i for i, e in enumerate(eps) if e.startswith(u + '_')] for u in self.TS}

    def boot(self, S, f, n=2000):
        rng = np.random.default_rng(0); bs = []
        for _ in range(n):
            ss = rng.choice(S, len(S)); ii = np.concatenate([self.IDX[self.TS[k]] for k in rng.choice(len(self.TS), len(self.TS))])
            bs.append(np.mean([f(s, ii) for s in ss]))
        return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]


def load_rows(d, eps, key, val, ckpt=None, stored=False):
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text()); assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', d
    if ckpt:
        assert f'{ckpt}/ckpt_best.pt' in str(m.get('args')), d
    rows = {r['episode']: r for r in json.loads((d / 'rows.json').read_text()) if r.get(key) == val}
    assert (set(eps) <= set(rows)) if stored else sorted(rows) == sorted(eps), f'{d} {val}: {len(rows)} rows'   # stored: earlier panels, a superset
    return [rows[e] for e in eps]


def main_report(a):
    E = BASE / ('smoke_pipe' if a.smoke else '') / '4x4'
    panel = (9001, 9002) if a.smoke else tuple(range(5301, 5365)); seeds = [0] if a.smoke else list(range(10))
    eps = [f'seed{t}_load{h}' for t in panel for h in (8, 16)]; P = Panel(eps); out = []
    Z = {}; R = {}; RAW = {}
    for s in seeds:
        z = load_rows(E / f'Z_s{s}', eps, 'arm', 'Z')
        if z is not None:
            Z[s] = np.array([r['queue_sum'] for r in z], float)
        for rc, arms in ARMS.items():
            for K in KS:
                for arm in arms:
                    rr = load_rows(E / f'RP_{TAG[rc]}_s{s}_K{K}', eps, 'arm', arm, f'{TAG[rc]}_s{s}')
                    if rr is not None:
                        R[(rc, s, K, arm)] = np.array([r['queue_sum'] for r in rr], float); RAW[(rc, s, K, arm)] = rr
    S = [s for s in seeds if s in Z and all((rc, s, K, arm) in R for rc, arms in ARMS.items() for K in KS for arm in arms)]
    out.append(f'== 4x4 repair panel {panel[0]}-{panel[-1]} x 8/16: complete seeds {S} (of {seeds})')
    if not S:
        return out, {}
    for s in S:                                            # structural checks (protocol §3): THR == PLAIN where nothing can drop
        assert np.array_equal(R[('CK1', s, 1, 'THR')], R[('CK1', s, 1, 'PLAIN')]), f'THR != PLAIN at K1, seed {s}'
        assert np.array_equal(R[('CK1', s, 1, 'MASK')], R[('CK1', s, 0, 'MASK')]), f'MASK depends on the channel, seed {s}'
    g = lambda rc, s, K, arm, ii=None: gain(R[(rc, s, K, arm)], Z[s], ii)

    def stat(rc, K, arm):
        per = [g(rc, s, K, arm) for s in S]
        return dict(mean=float(np.mean(per)), ci=P.boot(S, lambda s, ii: g(rc, s, K, arm, ii)), per=per)

    def pdiff(f):
        per = [f(s, None) for s in S]
        return dict(mean=float(np.mean(per)), ci=P.boot(S, f), pos=sum(x > 0 for x in per), n=len(S))

    T = {(rc, K, arm): stat(rc, K, arm) for rc, arms in ARMS.items() for K in KS for arm in arms}
    D = {(rc, K, arm): pdiff(lambda s, ii, rc=rc, K=K, arm=arm: g(rc, s, K, arm, ii) - g(rc, s, K, 'PLAIN', ii))
         for rc, arms in ARMS.items() for K in KS for arm in arms if arm != 'PLAIN'}
    fmt = lambda x: f"{x['mean']:+.2f} [{x['ci'][0]:+.2f}, {x['ci'][1]:+.2f}]"
    out.append('-- T1 gain vs Z, % (mean over seeds [95 % two-level bootstrap]); own cells: CK1@K1, Cage@iid; matched receiver exists only there')
    out.append('receiver | arm | ' + ' | '.join(NAME[K] for K in KS))
    for rc, arms in ARMS.items():
        for arm in arms:
            out.append(f'{rc} | {arm} | ' + ' | '.join(fmt(T[(rc, K, arm)]) for K in KS))
    out.append('-- T2 paired difference arm - PLAIN (same receiver checkpoint), % [CI] (seeds > 0)')
    for rc, arms in ARMS.items():
        for arm in arms:
            if arm != 'PLAIN':
                out.append(f'{rc} | {arm} | ' + ' | '.join(f"{fmt(D[(rc, K, arm)])} ({D[(rc, K, arm)]['pos']}/{len(S)})" for K in KS))

    def rate(rc, K, arm):
        rr = [r for s in S for r in RAW[(rc, s, K, arm)]]
        if arm.startswith('FB_'):
            return sum(r['flags'] for r in rr) / sum(r['decisions'] for r in rr)
        if arm == 'EMU':
            return sum(r['substituted'] for r in rr) / sum(r['decisions'] for r in rr)
        if arm == 'THR':
            return sum(r['dropped'] for r in rr) / max(1, sum(r['delivered'] for r in rr))
        return None
    out.append('-- T3 intervention rate: FB = fallback share of agent-decisions; EMU = substitutions per agent-decision; THR = dropped / delivered packets')
    RATE = {}
    for rc, arms in ARMS.items():
        for arm in arms:
            if rate(rc, 1, arm) is not None:
                RATE.update({(rc, K, arm): rate(rc, K, arm) for K in KS})
                out.append(f'{rc} | {arm} | ' + ' | '.join(f'{RATE[(rc, K, arm)]:.3f}' for K in KS))

    def ratio(rc, K, arm, kind):
        pl = T[(rc, K, 'PLAIN')]; x = T[(rc, K, arm)]['mean']; unstable = pl['ci'][0] <= 0 <= pl['ci'][1]
        v = (x - pl['mean']) / (-pl['mean']) if kind == 'blocked' else x / pl['mean']
        return f"{v * 100:+.0f} %{' (unstable)' if unstable else ''}"
    out.append('-- T4 per arm: harmful cells (CI upper < 0, of 4) | seed-level harmful share (gain < 0 among seed x K) | worst-cell mean | '
               'descriptive ratios (NOT endpoints): harm blocked in the hazard cell, benefit retained in the own and benefit-at-risk cells')
    SUM = {}
    for rc, arms in ARMS.items():
        for arm in arms:
            hc = sum(T[(rc, K, arm)]['ci'][1] < 0 for K in KS); per = [x for K in KS for x in T[(rc, K, arm)]['per']]
            worst = min(T[(rc, K, arm)]['mean'] for K in KS); SUM[(rc, arm)] = dict(harmful_cells=hc, seed_harmful=float(np.mean([x < 0 for x in per])), worst=worst)
            extra = ''
            if rc != 'MIX' and arm != 'PLAIN':
                hz = [K for r_, K in HAZ if r_ == rc]; bn = [K for r_, K in BEN if r_ == rc]; ow = [K for r_, K in OWN if r_ == rc]
                extra = ' | blocked ' + ', '.join(f'{NAME[K]} {ratio(rc, K, arm, "blocked")}' for K in hz) + \
                        ' | retained ' + ', '.join(f'{NAME[K]} {ratio(rc, K, arm, "retained")}' for K in ow + bn)
            out.append(f'{rc} | {arm} | {hc}/4 | {SUM[(rc, arm)]["seed_harmful"]:.2f} | {worst:+.2f}{extra}')

    # ---- costs
    out.append('-- T5 costs (runtime per episode of 120 decisions x 16 agents; bytes = delivered direct packets x 25 B, relay v2 layout)')
    for rc, arms in ARMS.items():
        for arm in arms:
            rr = [r for s in S for K in KS for r in RAW[(rc, s, K, arm)]]
            sec = np.mean([r['seconds'] for r in rr]); mem = np.mean([r['mem_max'] for r in rr])
            byt = np.mean([r['delivered'] for r in rr]) * PKT_BYTES          # the channel transmits the same under every runtime arm
            used = np.mean([r['accepted'] for r in rr]) * PKT_BYTES if arm == 'THR' else (0.0 if arm == 'MASK' else byt)
            fwd = '1 relay + 1 Z' if arm.startswith('FB_') else '1 relay'
            out.append(f'{rc} | {arm} | {sec:.3f} s/episode | forward passes per step: {fwd} | memory (max entries): {mem:.0f} | '
                       f'bytes delivered/used per episode: {byt:.0f} / {used:.0f}')
    tr = {}
    for rc in ('CK1', 'Cage', 'MIX'):
        secs = []
        for s in S:
            f = M / 'e3_grid4x4_20260930/actors' / f'{TAG[rc]}_s{s}' / 'manifest.json'
            if f.exists():
                secs.append(json.loads(f.read_text()).get('seconds', float('nan')))
        tr[rc] = float(np.nanmean(secs)) if secs else None
    cal = [json.loads((E / f'det_{TAG[rc]}_s{s}' / 'manifest.json').read_text())['seconds'] for rc in ('CK1', 'Cage') for s in S]
    out.append(f"retraining (training manifests, wall s per checkpoint, CPU, one process; resumes included): CK1 {tr['CK1']:.0f}, Cage {tr['Cage']:.0f}, "
               f"MIX {tr['MIX']:.0f}; runtime arms: 0 training + one calibration pass (64 training-channel episodes, {np.mean(cal):.0f} s incl. "
               f"leave-one-episode-out fits)")
    # ---- detectors
    out.append('-- T6 detectors (calibration on the receiver\'s training channel, seeds 301-332 x 8/16): false alarm in-sample / leave-one-episode-out '
               '(mean, max over seeds); NOT a guarantee')
    DT = {}
    for rc in ('CK1', 'Cage'):
        dj = [json.loads((E / f'det_{TAG[rc]}_s{s}' / 'detectors.json').read_text()) for s in S]
        for n in DETS:
            ins = [d['false_alarm'][n]['in_sample'] for d in dj]; loo = [d['false_alarm'][n]['loo_episode'] for d in dj]
            DT[(rc, n)] = dict(ins=float(np.mean(ins)), loo=float(np.mean(loo)))
            out.append(f'{rc} | {n} | {np.mean(ins):.4f} (max {max(ins):.4f}) / {np.mean(loo):.4f} (max {max(loo):.4f})')
        ch = [d['change_vs_old_FB_Mq'] for d in dj]
        out.append(f'{rc} | old v2 FB_Mq vs FB_Mq-: changed keys per seed {[len(c["keys"]) for c in ch]}, changed calibration mass mean '
                   f'{np.mean([c["mass"] for c in ch]):.4f}; old in-sample false alarm mean {np.mean([c["old_in_sample"] for c in ch]):.4f}')

    # ---- verdicts (protocol §6)
    V = {}; m_ = lambda rc, K, arm: T[(rc, K, arm)]['mean']
    V['RP1'] = all(T[(rc, K, 'MASK')]['ci'][1] < 0 for rc in ('CK1', 'Cage') for K in KS)
    up = pdiff(lambda s, ii: g('CK1', s, 0, 'PLAIN', ii) - g('CK1', s, 1, 'PLAIN', ii))
    V['RP2'] = T[('CK1', 0, 'PLAIN')]['ci'][1] < 0 and up['ci'][1] < 0 and T[('Cage', 1, 'PLAIN')]['ci'][1] < 0
    V['RP3'] = all(D[(rc, K, 'FB_S+')]['ci'][0] > 0 for rc, K in HAZ)
    non_own = HAZ + BEN

    def dominates(x, y):
        return all(m_(rc, K, x) >= m_(rc, K, y) for rc, K in non_own)
    V['RP4'] = all(not dominates(x, y) and not dominates(y, x) for x, y in (('FB_S+', 'FB_Mq+'), ('FB_S-', 'FB_Mq-')))
    V['RP5'] = sum(m_(rc, K, 'FB_S+') < m_(rc, K, 'PLAIN') for rc, K in BEN) >= 3
    V['RP6'] = all(m_(rc, K, d) >= 0.9 * m_(rc, K, 'PLAIN') for rc, K in OWN for d in DETS)
    hz = m_('CK1', 1, 'PLAIN') - m_('CK1', 0, 'PLAIN')
    V['RP7'] = all(m_('CK1', 0, arm) - m_('CK1', 0, 'PLAIN') < 0.5 * hz for arm in ('EMU', 'THR'))
    best_ck1_iid = max(ARMS['CK1'], key=lambda x: m_('CK1', 0, x)); best_cage_k1 = max(ARMS['Cage'], key=lambda x: m_('Cage', 1, x))
    r8a = pdiff(lambda s, ii: g('Cage', s, 0, 'PLAIN', ii) - g('CK1', s, 0, best_ck1_iid, ii))
    r8b = pdiff(lambda s, ii: g('CK1', s, 1, 'PLAIN', ii) - g('Cage', s, 1, best_cage_k1, ii))
    mixw = SUM[('MIX', 'PLAIN')]['worst']; rtw = max(SUM[(rc, arm)]['worst'] for rc in ('CK1', 'Cage') for arm in ARMS[rc])
    V['RP8'] = r8a['ci'][0] > 0 and r8b['ci'][0] > 0 and mixw > rtw
    out.append('-- verdicts (PROTOCOL_E3_REPAIR_PANEL_20261003 §6; groups fixed from 4201 / 4601 / 4901)')
    out.append(f"RP1 MASK below Z in all 8 cells: {[(rc, NAME[K], T[(rc, K, 'MASK')]['ci'][1]) for rc in ('CK1', 'Cage') for K in KS]} -> {'SUPPORTED' if V['RP1'] else 'NOT SUPPORTED'}")
    out.append(f"RP2 hazards: CK1 PLAIN iid {fmt(T[('CK1', 0, 'PLAIN')])}, iid - K1 {fmt(up)}, Cage PLAIN K1 {fmt(T[('Cage', 1, 'PLAIN')])} -> {'SUPPORTED' if V['RP2'] else 'NOT SUPPORTED'}")
    out.append(f"RP3 FB_S+ - PLAIN in hazard cells: CK1 iid {fmt(D[('CK1', 0, 'FB_S+')])}, Cage K1 {fmt(D[('Cage', 1, 'FB_S+')])} -> {'SUPPORTED' if V['RP3'] else 'NOT SUPPORTED'}")
    out.append(f"RP4 no dominance in the 6 non-own cells (FB_S+ vs FB_Mq+, FB_S- vs FB_Mq-): " +
               '; '.join(f"{x} vs {y}: " + ' '.join(f"{rc}@{NAME[K]} {m_(rc, K, x):+.2f}/{m_(rc, K, y):+.2f}" for rc, K in non_own) for x, y in (('FB_S+', 'FB_Mq+'), ('FB_S-', 'FB_Mq-')))
               + f" -> {'SUPPORTED' if V['RP4'] else 'NOT SUPPORTED'}")
    out.append(f"RP5 FB_S+ < PLAIN in >= 3 of 4 benefit-at-risk cells: {[(rc, NAME[K], round(m_(rc, K, 'FB_S+'), 2), round(m_(rc, K, 'PLAIN'), 2)) for rc, K in BEN]} -> {'SUPPORTED' if V['RP5'] else 'NOT SUPPORTED'}")
    out.append(f"RP6 every FB arm >= 90 % of PLAIN in own cells: " + ', '.join(f"{rc}@{NAME[K]} PLAIN {m_(rc, K, 'PLAIN'):+.2f} min FB {min(m_(rc, K, d) for d in DETS):+.2f}" for rc, K in sorted(OWN)) +
               f" -> {'SUPPORTED' if V['RP6'] else 'NOT SUPPORTED'}")
    out.append(f"RP7 input-only repairs recover < 50 % of the CK1 hazard ({hz:+.2f}): EMU {m_('CK1', 0, 'EMU') - m_('CK1', 0, 'PLAIN'):+.2f}, THR {m_('CK1', 0, 'THR') - m_('CK1', 0, 'PLAIN'):+.2f} -> {'SUPPORTED' if V['RP7'] else 'NOT SUPPORTED'}")
    out.append(f"RP8 matched > best runtime arm: Cage@iid - CK1 {best_ck1_iid}@iid {fmt(r8a)}; CK1@K1 - Cage {best_cage_k1}@K1 {fmt(r8b)}; MIX worst {mixw:+.2f} vs best runtime worst {rtw:+.2f} -> {'SUPPORTED' if V['RP8'] else 'NOT SUPPORTED'}")
    res = dict(seeds=S, table={f'{rc}|{NAME[K]}|{arm}': T[(rc, K, arm)] for rc, arms in ARMS.items() for K in KS for arm in arms},
               diff_vs_plain={f'{rc}|{NAME[K]}|{arm}': D[(rc, K, arm)] for (rc, K, arm) in D}, rate={f'{rc}|{NAME[K]}|{arm}': v for (rc, K, arm), v in RATE.items()},
               summary={f'{rc}|{arm}': v for (rc, arm), v in SUM.items()}, detectors={f'{rc}|{n}': v for (rc, n), v in DT.items()},
               retraining_seconds=tr, verdicts={k: bool(v) for k, v in V.items()})
    return out, res


def rerun_report(a):
    out = []; res = {}
    for net, panel, seeds, arms in (('4x4', range(4901, 4965), range(10), ('relayCK1_st', 'relayCage_st')),
                                    ('3x3', range(4801, 4865), range(5), ('relayCK1_st', 'relay6Cage_st'))):
        if a.smoke:
            panel = range(panel.start, panel.start + 2); seeds = [0]
        eps = [f'seed{t}_load{h}' for t in panel for h in (8, 16)]; P = Panel(eps)
        E = BASE / ('smoke_pipe' if a.smoke else '') / ('rerun_4901' if net == '4x4' else 'rerun_4801')
        F = M / 'e3_fallback_20261002' / net; FM = M / 'e3_fallback_mahal_20261003' / net
        for arm in arms:
            out.append(f'== {net} {arm} panel {panel.start}: gain vs Z, old v2 FB_Mq | corrected FB_Mq- | FB_Mq+ | PLAIN (fallback rates)')
            for K in KS:
                S = []; G = {}
                for s in seeds:
                    z = load_rows(F / f'Z_s{s}', eps, 'system', 'Z', stored=True) if (F / f'Z_s{s}' / 'manifest.json').exists() else None
                    new = {x: load_rows(E / f'RR_{arm}_s{s}_K{K}', eps, 'arm', x, f'{arm}_s{s}') for x in ('PLAIN', 'FB_Mq-', 'FB_Mq+')}
                    old = {x: load_rows(FM / f'FBM_{arm}_s{s}_K{K}', eps, 'system', x, f'{arm}_s{s}', stored=True) for x in ('RELAY', 'FB_Mq')}
                    if z is None or any(v is None for v in list(new.values()) + list(old.values())):
                        continue
                    for e in range(len(eps)):                      # the rerun reproduced PLAIN exactly (also asserted in-run)
                        assert abs(new['PLAIN'][e]['queue_sum'] - old['RELAY'][e]['queue_sum']) < 1e-6
                    S.append(s); zq = np.array([r['queue_sum'] for r in z], float)
                    for lab, rr in (('old', old['FB_Mq']), ('new-', new['FB_Mq-']), ('new+', new['FB_Mq+']), ('plain', new['PLAIN'])):
                        G[(lab, s)] = (np.array([r['queue_sum'] for r in rr], float), sum(r.get('flags', 0) for r in rr) / sum(r['decisions'] for r in rr))
                if not S:
                    out.append(f'{NAME[K]}: no complete seeds'); continue
                zq = {s: np.array([r['queue_sum'] for r in load_rows(F / f'Z_s{s}', eps, 'system', 'Z', stored=True)], float) for s in S}
                cell = {}
                for lab in ('old', 'new-', 'new+', 'plain'):
                    per = [gain(G[(lab, s)][0], zq[s]) for s in S]
                    ci = P.boot(S, lambda s, ii, lab=lab: gain(G[(lab, s)][0], zq[s], ii))
                    cell[lab] = dict(mean=float(np.mean(per)), ci=ci, rate=float(np.mean([G[(lab, s)][1] for s in S])))
                nch = sum(int(not np.array_equal(G[('old', s)][0], G[('new-', s)][0])) for s in S)
                out.append(f"{NAME[K]} (seeds {len(S)}): " + ' | '.join(f"{lab} {c['mean']:+.2f} [{c['ci'][0]:+.2f}, {c['ci'][1]:+.2f}] ({c['rate']:.3f})" for lab, c in cell.items())
                           + f" | seeds whose old and corrected FB_Mq- episodes differ: {nch}/{len(S)}")
                res[f'{net}|{arm}|{NAME[K]}'] = dict(cell, seeds=S, seeds_changed=nch)
    return out, res


def main(a):
    d = BASE / ('smoke_pipe' if a.smoke else ''); d.mkdir(parents=True, exist_ok=True)
    out, res = rerun_report(a) if a.rerun else main_report(a)
    stem = 'rerun_report' if a.rerun else 'report'
    (d / f'{stem}.txt').write_text('\n'.join(out) + '\n'); (d / f'{stem}.json').write_text(json.dumps(res, indent=1, default=lambda o: o.item() if hasattr(o, 'item') else str(o))); print('\n'.join(out))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--smoke', action='store_true'); p.add_argument('--rerun', action='store_true')
    main(p.parse_args())
