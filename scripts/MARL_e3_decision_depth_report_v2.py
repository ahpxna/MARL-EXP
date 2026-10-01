#!/usr/bin/env python3
"""Report v2 for scripts/MARL_e3_decision_depth_probe_v2.py (ledger L-194): both bases, labelled.
  base 'cache' — fresh first-k senders on top of the receiver's direct (stale) cache (the v1 quantity);
  base 'empty' — fresh first-k senders and nothing else (the pure decision depth of LeanMarlDecisionDepthV1).

SELF-CHECKS (refuses to write if any fails; definitional or proved facts):
  * minset <= min(depth[o], 3) for every order o and eps (a prefix of length k is a subset of size k);
  * depth and minset are non-increasing in eps (acceptable sets are nested in eps);
  * depth[o] <= nN (the full view is acceptable by definition of A_eps);
  * the two bases agree on the FULL view by construction (checked inside the probe: the full view's logits are order-free).
Statistics: means over receiver-steps; 95 % CIs by bootstrap over traffic seeds, paired for contrasts.  Evidence class:
ORACLE DIAGNOSTIC with a TEACHER-DEFINED acceptable set (not ground truth).
Usage: python3 scripts/MARL_e3_decision_depth_report_v2.py [dir]   (a dir argument = smoke mode: prints, writes nothing)
"""
from __future__ import annotations
import json, sys
from pathlib import Path
import numpy as np

ORDERS = ('stream', 'reverse', 'random')
EPS = (0.0, 0.25, 1.0)


def boot(x_by_seed, B=2000, seed=0):
    rng = np.random.default_rng(seed)
    seeds = sorted(x_by_seed)
    vals = np.array([np.mean(x_by_seed[s]) for s in seeds]); w = np.array([len(x_by_seed[s]) for s in seeds], float)
    est = float(np.sum(vals * w) / w.sum()); bs = []
    for _ in range(B):
        idx = rng.integers(0, len(seeds), len(seeds)); bs.append(np.sum(vals[idx] * w[idx]) / w[idx].sum())
    return est, float(np.percentile(bs, 2.5)), float(np.percentile(bs, 97.5))


def by_seed(seed, x):
    return {s: x[seed == s] for s in np.unique(seed)}


def checks(name, dep, ms, nN):
    for o in range(len(ORDERS)):
        if np.any(ms > np.minimum(dep[:, o, :], 3)):
            raise SystemExit(f'SELF-CHECK FAIL {name}: minset > depth for order {ORDERS[o]}')
        if np.any(dep[:, o, 1:] > dep[:, o, :-1]):
            raise SystemExit(f'SELF-CHECK FAIL {name}: depth increases with eps')
        if np.any(dep[:, o, :] > nN[:, None]):
            raise SystemExit(f'SELF-CHECK FAIL {name}: depth exceeds the number of senders')
    if np.any(ms[:, 1:] > ms[:, :-1]):
        raise SystemExit(f'SELF-CHECK FAIL {name}: minset increases with eps')


def analyse(name, dep, ms, K, seed):
    f = lambda t: f'{t[0]:.3f} [{t[1]:.3f},{t[2]:.3f}]'
    r = {}; lines = []
    for e, eps in enumerate(EPS):
        re = dict(minset_hist=[int(c) for c in np.bincount(ms[:, e], minlength=4)],
                  zero_message_share=boot(by_seed(seed, (ms[:, e] == 0).astype(float))))
        for o, nm in enumerate(ORDERS):
            re[f'depth_{nm}'] = boot(by_seed(seed, dep[:, o, e].astype(float)))
            re[f'within_K_{nm}'] = boot(by_seed(seed, (dep[:, o, e] <= K).astype(float)))
        gap = (np.minimum(dep[:, 0, e], 3) - ms[:, e]).astype(float)
        re['nesting_gap_stream'] = boot(by_seed(seed, gap))
        re['nesting_gap_positive_share'] = boot(by_seed(seed, (gap > 0).astype(float)))
        re['stream_minus_reverse'] = boot(by_seed(seed, (dep[:, 0, e] - dep[:, 1, e]).astype(float)))
        re['stream_minus_random'] = boot(by_seed(seed, (dep[:, 0, e] - dep[:, 2, e]).astype(float)))
        r[str(eps)] = re
        lines.append(f'{name} eps={eps}: minset hist {re["minset_hist"]}; zero-msg share {f(re["zero_message_share"])}; '
                     f'depth stream {f(re["depth_stream"])} reverse {f(re["depth_reverse"])} random {f(re["depth_random"])}; '
                     f'within K stream {f(re["within_K_stream"])}; nesting gap {f(re["nesting_gap_stream"])} '
                     f'(>0 on {f(re["nesting_gap_positive_share"])}); stream-random {f(re["stream_minus_random"])}')
    return r, lines


def main():
    smoke = len(sys.argv) > 1
    E = Path(sys.argv[1]) if smoke else Path('research/marl_budget/e3_decision_depth_v2_20261001')
    out = {}; lines = []
    for d in sorted(p for p in E.iterdir() if p.is_dir()):
        man = d / 'manifest.json'
        if not man.exists():
            lines.append(f'{d.name}: not complete'); continue
        m = json.loads(man.read_text())
        if m.get('self_check') != 'PASS' or m['parity_episodes'] != len(m['args']['traffic_seeds']) * len(m['args']['headways']):
            raise SystemExit(f'{d.name}: manifest self-check / parity incomplete')
        z = np.load(d / 'depth.npz'); nN = z['nN']; K = z['K']; seed = z['seed']
        for base, dk, mk in (('cache', 'depth', 'minset'), ('empty', 'depth_empty', 'minset_empty')):
            dep = z[dk].astype(int); ms = z[mk].astype(int)
            checks(f'{d.name}|{base}', dep, ms, nN)
            r, ls = analyse(f'{d.name} [{base}]', dep, ms, K, seed)
            out[f'{d.name}|{base}'] = r; lines += ls
        # the stale-cache penalty, paired per receiver-step
        pen = (z['depth'][:, 0, 1].astype(float) - z['depth_empty'][:, 0, 1].astype(float))
        t = boot(by_seed(seed, pen)); out[f'{d.name}|stale_penalty_stream_eps0.25'] = t
        lines.append(f'{d.name}: stale-cache penalty (cache − empty, stream, eps 0.25) {t[0]:.3f} [{t[1]:.3f},{t[2]:.3f}]')
    print('\n'.join(lines))
    if not smoke:
        Path('research/marl_budget/e3_decision_depth_v2_report_20261001.json').write_text(json.dumps(out, indent=1))
        Path('research/marl_budget/e3_decision_depth_v2_report_20261001.txt').write_text('\n'.join(lines) + '\n')


if __name__ == '__main__':
    main()
