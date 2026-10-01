#!/usr/bin/env python3
"""Report for the DECISION-DEPTH PROBE (scripts/MARL_e3_decision_depth_probe.py; ledger L-192).

SELF-CHECKS (refuses to write if any fails; they transcribe proved or definitional facts):
  * minset <= min(depth[o], 3) for every order o and eps  (a prefix of length k is a subset of size k;
    LeanMarlDecisionDepthV1: the prefix condition is a hitting condition);
  * depth and minset are non-increasing in eps (acceptable sets are nested in eps);
  * depth[o] <= nN (the full view is acceptable by definition of A_eps).
Statistics: means over receiver-steps; 95% CIs by bootstrap over TRAFFIC SEEDS (the episode-level unit), paired for the
order contrasts.  Evidence class: ORACLE DIAGNOSTIC with a TEACHER-DEFINED acceptable set (not ground truth).
"""
from __future__ import annotations
import json, sys
from pathlib import Path
import numpy as np

E = Path('research/marl_budget/e3_decision_depth_20261001')
ORDERS = ('stream', 'reverse', 'random')
EPS = (0.0, 0.25, 1.0)


def boot(x_by_seed, B=2000, rng=np.random.default_rng(0)):
    seeds = sorted(x_by_seed)
    vals = np.array([np.mean(x_by_seed[s]) for s in seeds])
    w = np.array([len(x_by_seed[s]) for s in seeds], float)
    est = float(np.sum(vals * w) / w.sum())
    bs = []
    for _ in range(B):
        idx = rng.integers(0, len(seeds), len(seeds))
        bs.append(np.sum(vals[idx] * w[idx]) / w[idx].sum())
    return est, float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


def by_seed(seed, x):
    return {s: x[seed == s] for s in np.unique(seed)}


def main():
    global E
    smoke = len(sys.argv) > 1
    if smoke:
        E = Path(sys.argv[1])
    out = {}; lines = []
    for d in sorted(p for p in E.iterdir() if p.is_dir()):
        man = d / 'manifest.json'
        if not man.exists():
            lines.append(f'{d.name}: not complete'); continue
        m = json.loads(man.read_text())
        if m.get('self_check') != 'PASS' or m['parity_episodes'] != len(m['args']['traffic_seeds']) * len(m['args']['headways']):
            raise SystemExit(f'{d.name}: manifest self-check / parity incomplete')
        z = np.load(d / 'depth.npz'); dep = z['depth'].astype(int); ms = z['minset'].astype(int); nN = z['nN']; K = z['K']; seed = z['seed']
        for o in range(len(ORDERS)):
            if np.any(ms > np.minimum(dep[:, o, :], 3)):
                raise SystemExit(f'SELF-CHECK FAIL {d.name}: minset > depth for order {ORDERS[o]}')
            if np.any(dep[:, o, 1:] > dep[:, o, :-1]):
                raise SystemExit(f'SELF-CHECK FAIL {d.name}: depth increases with eps')
            if np.any(dep[:, o, :] > nN[:, None]):
                raise SystemExit(f'SELF-CHECK FAIL {d.name}: depth exceeds the number of senders')
        if np.any(ms[:, 1:] > ms[:, :-1]):
            raise SystemExit(f'SELF-CHECK FAIL {d.name}: minset increases with eps')
        r = dict(records=int(len(K)), K_counts={int(k): int(c) for k, c in zip(*np.unique(K, return_counts=True))}, eps={})
        for e, eps in enumerate(EPS):
            re = dict(minset_hist=[int(c) for c in np.bincount(ms[:, e], minlength=4)],
                      zero_message_share=boot(by_seed(seed, (ms[:, e] == 0).astype(float))))
            for o, name in enumerate(ORDERS):
                re[f'depth_{name}'] = boot(by_seed(seed, dep[:, o, e].astype(float)))
                re[f'within_K_{name}'] = boot(by_seed(seed, (dep[:, o, e] <= K).astype(float)))
            gap = (np.minimum(dep[:, 0, e], 3) - ms[:, e]).astype(float)
            re['nesting_gap_stream'] = boot(by_seed(seed, gap))
            re['nesting_gap_positive_share'] = boot(by_seed(seed, (gap > 0).astype(float)))
            re['stream_minus_reverse'] = boot(by_seed(seed, (dep[:, 0, e] - dep[:, 1, e]).astype(float)))
            re['stream_minus_random'] = boot(by_seed(seed, (dep[:, 0, e] - dep[:, 2, e]).astype(float)))
            for k in sorted(np.unique(K)):
                sel = K == k
                re[f'within_K_stream_at_K{int(k)}'] = boot(by_seed(seed[sel], (dep[sel, 0, e] <= k).astype(float)))
            r['eps'][str(eps)] = re
            f = lambda t: f'{t[0]:.3f} [{t[1]:.3f},{t[2]:.3f}]'
            lines.append(f'{d.name} eps={eps}: minset hist {re["minset_hist"]}; zero-msg share {f(re["zero_message_share"])}; '
                         f'depth stream {f(re["depth_stream"])} reverse {f(re["depth_reverse"])} random {f(re["depth_random"])}; '
                         f'within K: stream {f(re["within_K_stream"])} reverse {f(re["within_K_reverse"])}; '
                         f'nesting gap {f(re["nesting_gap_stream"])} (>0 on {f(re["nesting_gap_positive_share"])}); '
                         f'stream-reverse {f(re["stream_minus_reverse"])}')
        out[d.name] = r
    if not smoke:
        Path('research/marl_budget/e3_decision_depth_report_20261001.json').write_text(json.dumps(out, indent=1))
        Path('research/marl_budget/e3_decision_depth_report_20261001.txt').write_text('\n'.join(lines) + '\n')
    print('\n'.join(lines))


if __name__ == '__main__':
    main()
