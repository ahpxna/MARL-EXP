#!/usr/bin/env python3
"""E12 report (research/marl_budget/PROTOCOL_E3_E12_E14_G3_G6_20261004.md §E12; written 04/10/2026 wake 2 while the panel ran, before
any panel row was read).  E12-b: view equality (full signature) <=> coverage on every OLD agent-step (0 exceptions either way).
E12-c: this evaluator's queue = E7's U2/EMU_OLD queue on every (seed, layout, episode); on every episode with no OLD coverage failure
E7's U2/EMU_OLD queue = E7's U2/EXACT_PROTO_OLD queue.  E12-d descriptive.  Any missing cell -> INCOMPLETE."""
import json
from pathlib import Path
import numpy as np

W = Path('research/marl_budget/e3_wave_20261003'); E = W / 'e12'; SEEDS = range(10); LAYS = ('D', 'C'); NEP = 128


def main():
    out = ['== E12: when is the zero-byte emulator EMU_OLD exact?']; rows = {}; miss = []
    for s in SEEDS:
        mf = E / f'PANEL_s{s}' / 'manifest.json'
        if not mf.exists() or json.loads(mf.read_text()).get('status') != 'COMPLETE':
            miss.append(s); continue
        for r in json.loads((E / f'PANEL_s{s}' / 'rows.json').read_text()):
            rows[(s, r['layout'], r['episode'])] = r
    e7 = {}
    for s in SEEDS:
        for lay in LAYS:
            f = W / 'w2' / f'MIX_s{s}_{lay}' / 'rows.json'
            if f.exists():
                for r in json.loads(f.read_text()):
                    e7[(s, lay, r['episode'], r['arm'])] = r['queue_sum']
    n_exp = len(SEEDS) * len(LAYS) * NEP
    if miss or len(rows) != n_exp:
        out.append(f'INCOMPLETE: missing actor seeds {miss}; rows {len(rows)}/{n_exp}'); (E / 'report.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out)); return
    res = {}
    for lay in LAYS + ('both',):
        R = [r for k, r in rows.items() if lay == 'both' or k[1] == lay]
        T = {c: sum(r['counts'][c] for r in R) for c in R[0]['counts']}
        ok = T['cov_neq'] == 0 and T['unc_eq'] == 0
        out.append(f"[{lay}] E12-b OLD agent-steps {T['agent_steps']}: covered & equal {T['cov_eq']}, covered & different {T['cov_neq']}, "
                   f"uncovered & equal {T['unc_eq']}, uncovered & different {T['unc_neq']} -> {'SUPPORTED' if ok else 'NOT SUPPORTED'}"
                   f"{' (the <= direction has ' + str(T['unc_neq'] + T['unc_eq']) + ' uncovered cases)' if ok else ''}")
        nunc = T['unc_eq'] + T['unc_neq']
        out.append(f"   E12-d failure rate {nunc / T['agent_steps']:.2e} per OLD agent-step; missing keys {T['missing']}/{T['keys']} "
                   f"(never {T['never']}, ambiguous {T['ambiguous']}); actor-visible view differs {T['actor_neq']}, input differs {T['input_neq']}, "
                   f"action differs {T['action_neq']} (covered {T['action_neq_cov']}, uncovered {T['action_neq_unc']}); "
                   f"P(action mismatch | failure) {T['action_neq_unc'] / nunc if nunc else float('nan'):.3f}")
        fe = [r for r in R if sum(r['fail_by_t']) > 0]
        bt = np.sum([r['fail_by_t'] for r in R], 0); nn = {}
        for r in R:
            for k, (a, b) in r['by_new_nbrs'].items():
                nn.setdefault(int(k), [0, 0]); nn[int(k)][0] += a; nn[int(k)][1] += b
        out.append(f"   episodes with >= 1 failure {len(fe)}/{len(R)}; failures by step t (nonzero) {[(t, int(x)) for t, x in enumerate(bt) if x]}; "
                   f"by number of NEW grid neighbours {{k: failures/steps}} {dict(sorted((k, f'{v[1]}/{v[0]}') for k, v in nn.items()))}")
        res[lay] = dict(T=T, failure_episodes=len(fe))
    # E12-c
    c1 = [(k, r['queue_sum'], e7.get((k[0], k[1], k[2], 'U2/EMU_OLD'))) for k, r in rows.items()]
    bad1 = [x for x in c1 if x[2] is None or abs(x[1] - x[2]) > 1e-6]
    out.append(f"E12-c(1) evaluator queue = E7 U2/EMU_OLD queue: {len(c1) - len(bad1)}/{len(c1)} -> {'SUPPORTED' if not bad1 else 'NOT SUPPORTED'} {bad1[:3]}")
    clean = [k for k, r in rows.items() if sum(r['fail_by_t']) == 0]
    c2 = [(k, e7.get((k[0], k[1], k[2], 'U2/EMU_OLD')), e7.get((k[0], k[1], k[2], 'U2/EXACT_PROTO_OLD'))) for k in clean]
    bad2 = [x for x in c2 if x[1] is None or x[2] is None or abs(x[1] - x[2]) > 1e-6]
    out.append(f"E12-c(2) no-failure episodes: E7 EMU_OLD = E7 EXACT_PROTO_OLD on {len(c2) - len(bad2)}/{len(c2)} -> {'SUPPORTED' if not bad2 else 'NOT SUPPORTED'} {bad2[:3]}")
    fail = [k for k, r in rows.items() if sum(r['fail_by_t']) > 0]
    d = [e7[(k[0], k[1], k[2], 'U2/EMU_OLD')] - e7[(k[0], k[1], k[2], 'U2/EXACT_PROTO_OLD')] for k in fail
         if (k[0], k[1], k[2], 'U2/EMU_OLD') in e7 and (k[0], k[1], k[2], 'U2/EXACT_PROTO_OLD') in e7]
    out.append(f"E12-d EMU - EXACT queue on failure episodes: n {len(d)}, mean {np.mean(d) if d else float('nan'):+.2f}, nonzero {sum(abs(x) > 1e-6 for x in d)}")
    res['c1_bad'] = len(bad1); res['c2'] = [len(c2), len(bad2)]
    txt = '\n'.join(out) + '\n'; (E / 'report.txt').write_text(txt); (E / 'report.json').write_text(json.dumps(res, indent=1, default=str)); print(txt)


if __name__ == '__main__':
    main()
