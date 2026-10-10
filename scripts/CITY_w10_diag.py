#!/usr/bin/env python3
"""W10-2 / W10-3 report (PROTOCOL_CITY_WAVE10_20261005).  Served SPaT answers (CITY_w10_run.py logs) are matched to realized targets from the
run's own phase trace (--record: P[i] = phase at time i + 1) and the static program's link states (the learned lights switch inside it):
  served(link, k) = state[P[k-1]][link] in 'Gg';  realized ttg = first k >= t with served (queries not served at t);
  realized ttr = first k > t with not served (queries served at t); events beyond the episode are censored (dropped).
KW10-2: under FT with the fleet's own program SPaT the answers must equal realized + c exactly, for one offset c per field (c in -4..4), on
every valid uncensored query; that c is then used for every arm of the network.  If no c is exact, the network's forecast accounting is VOID.
W10-3: held human-seconds per commanded agent-second from the rows.  Usage: CITY_w10_diag.py <diag dir>"""
import json, sys
from pathlib import Path
import numpy as np
import sumolib
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_w6_validation import rows  # noqa: E402
NETS = dict(g4=ROOT / 'research/city_sim/net/grid4.net.xml', sp=ROOT / 'research/city_sim/net/spider.net.xml', n3=ROOT / 'research/city_sim/net/rand3.net.xml')
CS = range(-4, 5)


def states(netf):
    net = sumolib.net.readNet(str(netf), withPrograms=True); out = {}
    for tl in net.getTrafficLights():
        pr = list(tl.getPrograms().values())[0]; out[tl.getID()] = [ph.state for ph in pr.getPhases()]
    return out


def match(served, rec, ST):
    """-> arrays (kind 0 ttg / 1 ttr, pred, realized) over valid uncensored queries."""
    q = np.load(served, allow_pickle=True); r = np.load(rec, allow_pickle=True); P = r['phases']; rid = {t: i for i, t in enumerate(r['ids'])}; T = len(P)
    ids = list(q['ids']); cache = {}; K, PR, RE = [], [], []
    for t, j, link, ttg, ttr, v in zip(q['t'], q['j'], q['link'], q['ttg'], q['ttr'], q['valid']):
        if not v:
            continue
        tid = ids[j]; key = (tid, int(link))
        if key not in cache:
            col = P[:, rid[tid]]; st = ST[tid]
            on = np.array([st[p][link] in 'Gg' if link < len(st[p]) else False for p in col], bool)      # on[k-1] = served at time k
            nxt_on = np.full(T + 1, -1); nxt_off = np.full(T + 1, -1); a = b = -1
            for k in range(T - 1, -1, -1):
                a = k if on[k] else a; b = k if not on[k] else b; nxt_on[k] = a; nxt_off[k] = b
            cache[key] = (on, nxt_on, nxt_off)
        on, nxt_on, nxt_off = cache[key]; i = int(round(t)) - 1
        if i < 0 or i >= T:
            continue
        if on[i]:
            k = nxt_off[i + 1] if i + 1 < T else -1
            if k < 0 or ttr >= 900:
                continue
            K.append(1); PR.append(ttr); RE.append(k - i)
        else:
            k = nxt_on[i]
            if k < 0:
                continue
            K.append(0); PR.append(ttg); RE.append(k - i)
    return np.array(K), np.array(PR, float), np.array(RE, float)


def main(D):
    out = ['== W10-2 / W10-3: served-answer forecast accounting (SERVE vs SHADOW) and held followers (PROTOCOL_CITY_WAVE10_20261005)']; summ = {}
    for nw in ('g4', 'sp', 'n3'):
        N = D / nw
        if not N.exists():
            continue
        ST = states(NETS[nw]); Rt = rows(N); tags = sorted(Rt)
        def runs(tag):
            for s in sorted(Rt[tag]):
                yield s, N / 'served' / f'{tag}_served_s{s}.npz', N / 'rec' / f'{tag}_s{s}.npz'
        # KW10-2 on FTX
        k_, p_, r_ = [], [], []
        for s, fs, fr in runs('FTX'):
            k, p, r = match(fs, fr, ST); k_.append(k); p_.append(p); r_.append(r)
        k, p, r = np.concatenate(k_), np.concatenate(p_), np.concatenate(r_); cc = {}
        for kind in (0, 1):
            m = k == kind; best = max(CS, key=lambda c: np.mean(np.abs(p[m] - (r[m] + c)) < 1e-6)) if m.any() else 0
            cc[kind] = (best, float(np.mean(np.abs(p[m] - (r[m] + best)) < 1e-6)) if m.any() else float('nan'), int(m.sum()))
        ok = all(v[1] == 1.0 for v in cc.values() if v[2] > 0)
        out.append(f'-- {nw}: KW10-2 exactness under FT (program SPaT): ttg c {cc[0][0]:+d} exact {cc[0][1]:.4f} (n {cc[0][2]}), ttr c {cc[1][0]:+d} exact {cc[1][1]:.4f} (n {cc[1][2]}) -> {"PASS" if ok else "FAIL (forecast accounting VOID for this network)"}')
        summ[nw] = {}
        for tag in tags:
            if tag == 'FTX':
                continue
            k_, e_ = [], []
            for s, fs, fr in runs(tag):
                k, p, r = match(fs, fr, ST); c = np.where(k == 0, cc[0][0], cc[1][0]); k_.append(k); e_.append(p - (r + c))
            k, e = np.concatenate(k_), np.concatenate(e_); rr = list(Rt[tag].values())
            held = sum(x.get('held_human_s', 0) for x in rr); cmd = sum(x.get('commanded_agent_s', 0) for x in rr); ml = sum(x.get('commanded_multi_lane_s', 0) for x in rr)
            d = dict(n=int(len(e)), mae=float(np.mean(np.abs(e))) if len(e) else float('nan'), bias=float(np.mean(e)) if len(e) else float('nan'),
                     gt5=float(np.mean(np.abs(e) > 5)) if len(e) else float('nan'), mae_ttg=float(np.mean(np.abs(e[k == 0]))) if (k == 0).any() else float('nan'),
                     mae_ttr=float(np.mean(np.abs(e[k == 1]))) if (k == 1).any() else float('nan'), held_per_cmd=held / max(1, cmd), held_per_run=held / len(rr),
                     multi_lane_share=ml / max(1, cmd), tl_h=float(np.mean([x['timeloss_human'] for x in rr])), tl_a=float(np.mean([x['timeloss_agent'] for x in rr])),
                     green=float(np.mean([x['green_mean'] for x in rr])), ok=ok)
            summ[nw][tag] = d
            out.append(f'  {nw} {tag}: n {d["n"]} | MAE {d["mae"]:.2f} (ttg {d["mae_ttg"]:.2f}, ttr {d["mae_ttr"]:.2f}) | bias {d["bias"]:+.2f} | >5s {d["gt5"]:.3f} | '
                       f'held human-s per commanded agent-s {d["held_per_cmd"]:.3f} ({d["held_per_run"]:.0f}/run, multi-lane share {d["multi_lane_share"]:.2f}) | '
                       f'human TL {d["tl_h"]:.2f} agent TL {d["tl_a"]:.2f} green {d["green"]:.1f}')
    # registered readings
    def grp(nw, pre):
        v = [x for t, x in summ.get(nw, {}).items() if t.startswith(pre)]
        return {k: float(np.mean([x[k] for x in v])) for k in ('mae', 'held_per_cmd', 'tl_h')} if v else None
    g_sh, g_hy, s_sh, s_hy = grp('g4', 'SHADOW'), grp('g4', 'HYB'), grp('sp', 'SHADOW'), grp('sp', 'HYBK')
    if all((g_sh, g_hy, s_sh, s_hy)) and all(x['ok'] for nw in ('g4', 'sp') for x in summ.get(nw, {}).values()):
        dg, ds = g_hy['mae'] - g_sh['mae'], s_hy['mae'] - s_sh['mae']
        perf = s_sh['mae'] <= 2 * g_sh['mae'] and ds >= 3 * max(dg, 1e-9); inh = s_sh['mae'] >= 3 * g_sh['mae']
        out.append(f'  W10-2 READING: shadow MAE grid4 {g_sh["mae"]:.2f} / spider {s_sh["mae"]:.2f}; publication shift grid4 {dg:+.2f} / spider {ds:+.2f} -> '
                   + ('PERFORMATIVE forecast shift' if perf else ('INHERENTLY LESS FORECASTABLE' if inh else 'not attributed by forecast error')))
        rate_g, rate_s = g_hy['held_per_cmd'], s_hy['held_per_cmd']; dh_g, dh_s = g_hy['tl_h'] - g_sh['tl_h'], s_hy['tl_h'] - s_sh['tl_h']
        sup = rate_s >= 3 * max(rate_g, 1e-9) and dh_s > 0 and dh_g < 0
        out.append(f'  W10-3 READING: held rate grid4 {rate_g:.3f} / spider {rate_s:.3f}; human TL service - shadow grid4 {dh_g:+.2f} / spider {dh_s:+.2f} -> '
                   + ('single-lane holding SUPPORTED' if sup else 'single-lane holding NOT supported'))
    else:
        out.append('  readings not computed (missing arms or a VOID exactness check)')
    n_sh, n_hy = grp('n3', 'SHADOW'), grp('n3', 'HYB')
    if g_sh and g_hy and n_sh and n_hy:
        out.append(f'  W10-2b rand3 (descriptive, same rules): shadow MAE {n_sh["mae"]:.2f}, publication shift {n_hy["mae"] - n_sh["mae"]:+.2f}; held rate '
                   f'{n_hy["held_per_cmd"]:.3f}; human TL service - shadow {n_hy["tl_h"] - n_sh["tl_h"]:+.2f}')
    (D / 'report_diag.txt').write_text('\n'.join(out) + '\n'); (D / 'diag_summary.json').write_text(json.dumps(summ, indent=1)); print('\n'.join(out))


if __name__ == '__main__':
    main(Path(sys.argv[1]))
