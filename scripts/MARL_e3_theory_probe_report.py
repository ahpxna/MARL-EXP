#!/usr/bin/env python3
"""Report of the THEORY PROBE runs (ledger L-176).  Offline, from probe.npz of MARL_e3_theory_probe.py.

V-F (FUNCTIONAL LIFE2/LIFE3 + D6 margin + MARL argmax_stable):
  identity   whenever osc(L_relay - L_fresh) < gap(L_fresh) the argmax agrees (must hold on every record; a pipeline check)
  curve      agreement of argmax(L_relay) with argmax(L_fresh), by fresh gap quintile and by maximum relayed age
  certificate delta + nu * h < gap, with (delta, nu) the upper envelope (q-quantile of osc per age h, least-squares line
             through those quantiles) fitted on the FIT half of the traffic seeds; soundness = P(agree | certified) and
             coverage = P(certified) on the TEST half.  Soundness below 1 means the fitted drift bound is not a bound.
V-U (UNIFIED / Paper B floor): split records by whether the 0-byte student agrees with the teacher (local fibre resolves the
  teacher's decision) or not; the relay student's teacher agreement on each split.  Prediction: the relay advantage over
  the 0-byte student sits in the disagreement split.
V-B (Paper B safe order / SUPPORT fibre): teacher(raw full) vs teacher(3 B full) disagreement, overall and by the raw gap.
"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import numpy as np


def valid(L):
    return L > -1e8


def top2(L):
    Lm = np.where(valid(L), L, -np.inf); s = np.sort(Lm, -1)
    return s[:, -1] - s[:, -2]


def osc(D, mask):
    hi = np.where(mask, D, -np.inf).max(-1); lo = np.where(mask, D, np.inf).min(-1)
    return hi - lo


def analyse(d, fit_split, q):
    Lr, Lf, LT, LTq, L0 = d['L_relay'], d['L_fresh'], d['L_T'], d['L_Tq'], d['L_0']
    mask = valid(Lf); a = lambda L: np.where(valid(L), L, -np.inf).argmax(-1)
    ar, af, aT, aTq, a0 = a(Lr), a(Lf), a(LT), a(LTq), a(L0)
    G = osc(Lr - Lf, mask); g = top2(Lf)
    ages = d['ages']; hmax = np.where((ages >= 0).any(-1), ages.max(-1), 0).astype(int)
    agree = ar == af
    out = {}
    viol = int(((G < g) & ~agree).sum())
    out['V_F_identity'] = dict(records=int(len(G)), violations=viol, certified_by_actual_osc=round(float((G < g).mean()), 4))
    qs = np.quantile(g, [0.2, 0.4, 0.6, 0.8])
    gb = np.digitize(g, qs)
    out['V_F_agree_by_gap_quintile'] = [round(float(agree[gb == k].mean()), 4) for k in range(5)]
    out['V_F_agree_by_max_age'] = {str(h): [int((hmax == h).sum()), round(float(agree[hmax == h].mean()), 4)] for h in range(0, 8) if (hmax == h).sum() >= 20}
    out['V_F_agree'] = round(float(agree.mean()), 4)
    fit = fit_split(d); test = ~fit; out['V_F_certificate'] = {}
    for qq in (0.90, 0.95, 0.99):
        hs = [h for h in range(0, 8) if (fit & (hmax == h)).sum() >= 50]
        if len(hs) >= 2:
            qv = np.array([np.quantile(G[fit & (hmax == h)], qq) for h in hs])
            nu, delta = np.polyfit(np.array(hs, float), qv, 1); nu = max(nu, 0.0)
            delta = max(delta, float(np.max(qv - nu * np.array(hs))))       # an upper envelope through every fitted quantile
        else:
            delta, nu = float(np.quantile(G[fit], qq)), 0.0
        cert = (delta + nu * hmax) < g
        out['V_F_certificate'][str(qq)] = dict(delta=round(float(delta), 4), nu=round(float(nu), 4), fit_ages=hs,
                                      test_coverage=round(float(cert[test].mean()), 4),
                                      test_soundness=round(float(agree[test & cert].mean()), 4) if (test & cert).any() else None,
                                      test_agree_uncertified=round(float(agree[test & ~cert].mean()), 4) if (test & ~cert).any() else None)
    fibre_ok = a0 == aT
    out['V_U'] = dict(share_zero_disagrees_teacher=round(float((~fibre_ok).mean()), 4),
                      relay_agree_teacher_where_zero_agrees=round(float((ar == aT)[fibre_ok].mean()), 4),
                      relay_agree_teacher_where_zero_disagrees=round(float((ar == aT)[~fibre_ok].mean()), 4),
                      fresh_student_agree_teacher_where_zero_disagrees=round(float((af == aT)[~fibre_ok].mean()), 4),
                      relay_minus_zero_teacher_agreement=round(float((ar == aT).mean() - fibre_ok.mean()), 4),
                      part_of_that_from_disagreement_split=round(float(((ar == aT) & ~fibre_ok).mean() - ((ar != aT) & fibre_ok).mean()), 4))
    gT = top2(LT); qT = np.quantile(gT, [0.2, 0.4, 0.6, 0.8]); bT = np.digitize(gT, qT); dis = aTq != aT
    out['V_B'] = dict(teacher_raw_vs_3B_disagreement=round(float(dis.mean()), 4),
                      by_raw_gap_quintile=[round(float(dis[bT == k].mean()), 4) for k in range(5)])
    return out


def main(a):
    rep = {}
    for p in sorted(Path(a.dir).glob('*/probe.npz')):
        man = json.loads((p.parent / 'manifest.json').read_text())
        if man.get('status') != 'COMPLETE':
            continue
        d = dict(np.load(p)); seeds = np.unique(d['seed']); cut = seeds[len(seeds) // 2]
        r = analyse(d, lambda dd: dd['seed'] < cut, a.quantile); r['waiting_mean'] = round(float(np.mean([x['queue_sum'] for x in json.loads((p.parent / 'rows.json').read_text())])), 1)
        r['parity_episodes'] = man.get('parity_episodes'); rep[p.parent.name] = r
        print(f'== {p.parent.name}: waiting {r["waiting_mean"]}, parity {r["parity_episodes"]}, identity violations {r["V_F_identity"]["violations"]}')
        print(f'   V-F agree relay/fresh {r["V_F_agree"]}; by gap quintile {r["V_F_agree_by_gap_quintile"]}; by max age {r["V_F_agree_by_max_age"]}')
        for qq, c in r['V_F_certificate'].items():
            print(f'   V-F certificate q{qq}: delta {c["delta"]} nu {c["nu"]}: test coverage {c["test_coverage"]}, soundness {c["test_soundness"]} (uncertified agree {c["test_agree_uncertified"]})')
        u = r['V_U']
        print(f'   V-U zero!=teacher on {u["share_zero_disagrees_teacher"]}: relay agrees with teacher there {u["relay_agree_teacher_where_zero_disagrees"]} '
              f'(fresh-input student {u["fresh_student_agree_teacher_where_zero_disagrees"]}), where zero==teacher {u["relay_agree_teacher_where_zero_agrees"]}; '
              f'net relay - zero {u["relay_minus_zero_teacher_agreement"]}')
        b = r['V_B']
        print(f'   V-B teacher raw vs 3 B disagreement {b["teacher_raw_vs_3B_disagreement"]}; by raw-gap quintile {b["by_raw_gap_quintile"]}')
    Path(a.out).write_text(json.dumps(rep, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('--dir', default='research/marl_budget/e3_theory_probe_20260930')
    p.add_argument('--quantile', type=float, default=0.99); p.add_argument('--out', default='research/marl_budget/e3_theory_probe_report_20260930.json')
    main(p.parse_args())
