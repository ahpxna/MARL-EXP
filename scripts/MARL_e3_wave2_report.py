#!/usr/bin/env python3
"""Report of wave 2a of PROTOCOL_E3_WAVE_ALL_PENDING_20261003 (written 23:4x EDT 03/10, before any wave-2a panel run).
--part e7: E9 replay (EXACT_PROTO_OLD == K1 on every dev episode, homogeneous OLD team) and the E7 mixed-fleet confirmation
(system / OLD / NEW gains vs ZTEAM, two-level crossed bootstrap 2000 rng 0; P-a, P-b, P-c on layout D; cost vector).
--part e8: residual-guard gate panel (gain vs Z per receiver x K x arm; E8a, E8b).  INCOMPLETE on any missing cell."""
import argparse, json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget')


def load(d):
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS', d
    return json.loads((d / 'rows.json').read_text()), m


def bootf(seeds, IDX, TS):
    def boot(f):
        rng = np.random.default_rng(0); bs = []
        for _ in range(2000):
            ss = rng.choice(seeds, len(seeds)); ii = np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])
            bs.append(np.mean([f(s, ii) for s in ss]))
        return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]
    return boot


def e7(a, E):
    out = []; seeds = [0] if a.smoke else list(range(10)); dev = [9001, 9002] if a.smoke else [901, 902, 903, 904]
    # E9 replay
    bad = []; n = 0
    for s in seeds:
        x = load(E / f'E9R_s{s}')
        if x is None:
            out.append(f'INCOMPLETE: E9R_s{s} missing'); return out
        r = {}
        for row in x[0]:
            r.setdefault(row['episode'], {})[row['arm']] = row['queue_sum']
        for ep, v in r.items():
            n += 1
            if v['U2/EXACT_PROTO_OLD'] != v['K1/ROLLBACK']:
                bad.append((s, ep))
    out.append(f"== E9 replay (homogeneous OLD team, dev {dev[0]}-{dev[-1]} x 8/16, seeds {seeds}): EXACT_PROTO_OLD == K1 on {n - len(bad)} / {n} episodes -> "
               f"{'PASS (exact)' if not bad else 'FAIL ' + str(bad[:5])}")
    # E7
    panel = (9001, 9002) if a.smoke else tuple(range(7501, 7565)); eps = [f'seed{t}_load{h}' for t in panel for h in (8, 16)]
    TS = sorted({e.split('_')[0] for e in eps}); IDX = {u: [i for i, e in enumerate(eps) if e.startswith(u + '_')] for u in TS}; boot = bootf(seeds, IDX, TS)
    ARMS = ['U1/PLAIN', 'U2/PLAIN', 'U2/EMU_OLD', 'U2/EXACT_PROTO_OLD', 'U1/FB_OLD', 'U1/FBR_OLD', 'U1/PLAIN@FT', 'U1/PLAIN@PCT', 'K1/ROLLBACK']
    R = {}; RAW = {}; miss = []
    for s in seeds:
        ref = load(E / f'REF_s{s}')
        for lay in ('D', 'C'):
            mix = load(E / f'MIX_s{s}_{lay}')
            for arm in ['ZTEAM', 'ALLOLD', 'ALLNEW'] + ARMS:
                src = ref if arm in ('ZTEAM', 'ALLOLD', 'ALLNEW') else mix
                if src is None:
                    miss.append((s, lay, arm)); continue
                rr = {r['episode']: r for r in src[0] if r['arm'] == arm}
                if sorted(rr) != sorted(eps):
                    miss.append((s, lay, arm)); continue
                RAW[(s, lay, arm)] = [rr[e] for e in eps]; R[(s, lay, arm)] = np.array([rr[e]['q_agents'] for e in eps], float)
    if miss:
        out.append(f'INCOMPLETE E7: {miss[:6]} ({len(miss)})'); return out
    for lay in ('D', 'C'):
        O = RAW[(seeds[0], lay, 'U1/PLAIN')][0]['old']; N = [i for i in range(16) if i not in O]; grp = {'sys': list(range(16)), 'old': O, 'new': N}

        def g(s, arm, gr, ii=None):
            x = R[(s, lay, arm)][:, grp[gr]].sum(1); z = R[(s, lay, 'ZTEAM')][:, grp[gr]].sum(1)
            return -(x.sum() / z.sum() - 1) * 100 if ii is None else -(x[ii].sum() / z[ii].sum() - 1) * 100
        st = lambda f: (float(np.mean([f(s, None) for s in seeds])), boot(f), int(sum(f(s, None) > 0 for s in seeds)))
        fmt = lambda x: f'{x[0]:+.2f} [{x[1][0]:+.2f}, {x[1][1]:+.2f}] ({x[2]}/{len(seeds)} > 0)'
        out.append(f"-- E7 layout {lay}{' (PRIMARY)' if lay == 'D' else ' (secondary)'}: OLD {O}")
        out.append('arm | system | OLD | NEW | delivered B / ep | unique B / ep | base delivered / unique B | OLD buffer | legacy entries | fallback share')
        for arm in ARMS + ['ALLOLD', 'ALLNEW']:
            rr = [r for s in seeds for r in RAW[(s, lay, arm)]]
            T = {gr: st(lambda s, ii, arm=arm, gr=gr: g(s, arm, gr, ii)) for gr in grp}
            out.append(f"{arm} | {fmt(T['sys'])} | {fmt(T['old'])} | {fmt(T['new'])} | {np.mean([r.get('delivered', 0) for r in rr]) * 25:.0f} | "
                       f"{np.mean([r.get('unique', 0) for r in rr]) * 25:.0f} | {np.mean([r.get('base_delivered', 0) for r in rr]) * 25:.0f} / {np.mean([r.get('base_unique', 0) for r in rr]) * 25:.0f} | "
                       f"{np.mean([r.get('buffer_old') or 0 for r in rr]):.0f} | {np.mean([r.get('legacy_entries', 0) for r in rr]):.0f} | "
                       f"{np.mean([r.get('flags', 0) for r in rr]) / (26 * len(O)):.3f}")
        D = lambda x, y, gr: st(lambda s, ii: g(s, x, gr, ii) - g(s, y, gr, ii))
        pa = D('U2/EMU_OLD', 'U1/FB_OLD', 'sys'); pb = D('U2/EMU_OLD', 'U2/PLAIN', 'sys'); pc = D('U2/EMU_OLD', 'U1/PLAIN', 'new')
        rr = [r for s in seeds for r in RAW[(s, lay, 'U2/EMU_OLD')]]
        out.append(f"emulator over OLD receivers: missing {sum(r['emu_missing'] for r in rr) / max(1, sum(r['emu_entries'] for r in rr)):.5f}, "
                   f"ambiguous {sum(r['emu_ambiguous'] for r in rr)}, substituted {sum(r['emu_substituted'] for r in rr)}")
        out.append(f"P-a EMU_OLD - FB_OLD (system) {fmt(pa)} -> {'SUPPORTED' if pa[1][0] > 0 else 'NOT SUPPORTED'}")
        out.append(f"P-b EMU_OLD - U2/PLAIN (system) {fmt(pb)} -> {'SUPPORTED' if pb[1][0] > 0 else 'NOT SUPPORTED'}")
        out.append(f"P-c NEW-group non-inferiority vs U1/PLAIN, margin 0.5 (CI lower > -0.5): {fmt(pc)} -> {'SUPPORTED' if pc[1][0] > -0.5 else 'NOT SUPPORTED'}")
        for x, y in (('U2/EMU_OLD', 'U1/PLAIN@FT'), ('U2/EMU_OLD', 'U1/PLAIN@PCT'), ('U2/EXACT_PROTO_OLD', 'U2/EMU_OLD'), ('U2/EMU_OLD', 'U1/FBR_OLD'),
                     ('U2/EMU_OLD', 'K1/ROLLBACK'), ('U2/EMU_OLD', 'ALLNEW'), ('U2/EMU_OLD', 'ALLOLD')):
            out.append(f"   (secondary, two-sided) {x} - {y}: system {fmt(D(x, y, 'sys'))}, OLD {fmt(D(x, y, 'old'))}, NEW {fmt(D(x, y, 'new'))}")
    for k in ('FTMIX', 'PCT'):                                     # training manifests (no rows.json)
        ms = [json.loads((E / f'T_{k}_s{s}' / 'manifest.json').read_text()) for s in seeds if (E / f'T_{k}_s{s}' / 'manifest.json').exists()]
        if len(ms) == len(seeds):
            out.append(f"retraining cost {k}-old per checkpoint: {ms[0]['budget_used']} simulated episodes, {ms[0]['teacher_queries']} teacher queries, "
                       f"mean {np.mean([x['seconds'] for x in ms]):.0f} s CPU")
    return out


def e8(a, E):
    out = []; seeds = [0] if a.smoke else list(range(10)); panel = (9001, 9002) if a.smoke else tuple(range(7401, 7465))
    eps = [f'seed{t}_load{h}' for t in panel for h in (8, 16)]; TS = sorted({e.split('_')[0] for e in eps}); IDX = {u: [i for i, e in enumerate(eps) if e.startswith(u + '_')] for u in TS}
    boot = bootf(seeds, IDX, TS); ARMS = ['PLAIN', 'FB_S+', 'FB_Mq-', 'FB_Mq+', 'FB_Mr-', 'FB_Mr+']; Q = {}; Z = {}; miss = []
    for r in ('relayCK1_st', 'relayCage_st'):
        for s in seeds:
            for K in (1, 0, 2, 3):
                x = load(E / f'E8_{r}_s{s}_K{K}')
                if x is None:
                    miss.append((r, s, K)); continue
                for arm in ARMS:
                    rr = {row['episode']: row['queue_sum'] for row in x[0] if row['arm'] == arm}
                    Q[(r, s, K, arm)] = np.array([rr[e] for e in eps], float)
    for s in seeds:
        z = load(E / f'E8Z_s{s}')
        if z is None:
            miss.append(('Z', s)); continue
        rr = {row['episode']: row['queue_sum'] for row in z[0]}; Z[s] = np.array([rr[e] for e in eps], float)
    if miss:
        out.append(f'INCOMPLETE E8: {miss[:6]} ({len(miss)})'); return out
    g = lambda r, s, K, arm, ii=None: -(Q[(r, s, K, arm)].sum() / Z[s].sum() - 1) * 100 if ii is None else -(Q[(r, s, K, arm)][ii].sum() / Z[s][ii].sum() - 1) * 100
    st = lambda f: (float(np.mean([f(s, None) for s in seeds])), boot(f))
    fmt = lambda x: f'{x[0]:+.2f} [{x[1][0]:+.2f}, {x[1][1]:+.2f}]'
    NAME = {1: 'K1', 0: 'iid', 2: 'K2', 3: 'K3'}
    out.append(f'== E8 residual-guard panel {panel[0]}-{panel[-1]} x 8/16, seeds {seeds}: gain vs Z')
    T = {}
    for r in ('relayCK1_st', 'relayCage_st'):
        for arm in ARMS:
            T.update({(r, K, arm): st(lambda s, ii, r=r, K=K, arm=arm: g(r, s, K, arm, ii)) for K in (1, 0, 2, 3)})
            out.append(f'{r} | {arm} | ' + ' | '.join(f"{NAME[K]} {fmt(T[(r, K, arm)])}" for K in (1, 0, 2, 3)))
    d1 = st(lambda s, ii: g('relayCK1_st', s, 0, 'FB_Mr-', ii) - g('relayCK1_st', s, 0, 'FB_Mq-', ii))
    d2 = T[('relayCage_st', 1, 'FB_Mr-')][0] - T[('relayCage_st', 1, 'FB_Mq-')][0]
    out.append(f"E8a FB_Mr- - FB_Mq-: CK1@iid {fmt(d1)} (need lower > 0), Cage@K1 {d2:+.2f} (need > 0) -> {'SUPPORTED' if d1[1][0] > 0 and d2 > 0 else 'NOT SUPPORTED'}")
    own = [T[('relayCK1_st', 1, x)][0] >= 0.9 * T[('relayCK1_st', 1, 'PLAIN')][0] and T[('relayCage_st', 0, x)][0] >= 0.9 * T[('relayCage_st', 0, 'PLAIN')][0] for x in ('FB_Mr-', 'FB_Mr+')]
    out.append(f"E8b own-channel retention >= 90 % for FB_Mr+/-: {own} -> {'SUPPORTED' if all(own) else 'NOT SUPPORTED'}")
    return out


def main(a):
    E = M / 'e3_wave_20261003' / ('smoke_pipe/w2' if a.smoke else 'w2')
    out = e7(a, E) if a.part == 'e7' else e8(a, E)
    (E / f'report_{a.part}.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--part', choices=['e7', 'e8'], required=True); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
