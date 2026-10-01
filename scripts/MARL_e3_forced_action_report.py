#!/usr/bin/env python3
"""Read MARL_e3_forced_action_probe.py outputs (read-only): message candidates vs forced single-agent action changes
at the same DEV states, 3-step gain vs the prefix (the stored label's scale).
Per state, then averaged (traffic-seed cluster bootstrap): oracle (max), mean, share > 0 for (a) all feasible message
candidates, (b) message candidates that change exactly one agent's action at t, (c) message candidates that change no
action at t, (d) forced single-agent changes; best-of-N matched (N = the number of message candidates in (b), random
subsets of (d), 200 draws); paired: each (b) candidate vs the forced change of the same agent to the same action.
Usage: MARL_e3_forced_action_report.py DIR... --out X.json
"""
from __future__ import annotations
import argparse, json, re, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_panel_report import boot_cluster


def main(a):
    out = {}; lines = []
    for D in map(Path, a.dirs):
        man = json.loads((D / 'manifest.json').read_text())
        if man.get('status') != 'COMPLETE' or man.get('self_check') != 'PASS':
            raise SystemExit(f'refusing: {D} not COMPLETE/PASS')
        per = []; rng = np.random.default_rng(0)
        for r in json.loads((D / 'rows.json').read_text()):
            j0 = r['prefix_joint']; fg = np.array([f['gain'] for f in r['forced']]); F = {(f['agent'], f['action']): f['gain'] for f in r['forced']}
            mg = np.array([m['gain'] for m in r['message']])
            nch = [sum(x != y for x, y in zip(m['joint'], j0)) for m in r['message']]
            one = [(m, [i for i, (x, y) in enumerate(zip(m['joint'], j0)) if x != y][0]) for m, n in zip(r['message'], nch) if n == 1]
            zero = np.array([m['gain'] for m, n in zip(r['message'], nch) if n == 0])
            og = np.array([m['gain'] for m, _ in one]); pair = [m['gain'] - F[(i, m['joint'][i])] for m, i in one if (i, m['joint'][i]) in F]
            N = len(og)
            matched = float(np.mean([fg[rng.choice(len(fg), size=min(N, len(fg)), replace=False)].max() for _ in range(200)])) if N else np.nan
            per.append(dict(seed=int(re.match(r'seed(\d+)_', r['episode']).group(1)),
                            msg_max=mg.max(), msg_mean=mg.mean(), msg_pos=np.mean(mg > 0),
                            one_max=og.max() if N else np.nan, one_mean=og.mean() if N else np.nan, one_n=N,
                            zero_max=zero.max() if len(zero) else np.nan, zero_mean=zero.mean() if len(zero) else np.nan,
                            forced_max=fg.max(), forced_mean=fg.mean(), forced_pos=np.mean(fg > 0), forced_matched_max=matched,
                            paired_msg_minus_forced=float(np.mean(pair)) if pair else np.nan,
                            paired_share_msg_better=float(np.mean(np.array(pair) > 0)) if pair else np.nan))
        res = {}
        for k in per[0]:
            if k == 'seed':
                continue
            cl = {}
            for p in per:
                if not np.isnan(p[k]):
                    cl.setdefault(p['seed'], []).append(p[k])
            res[k] = dict(mean=float(np.nanmean([p[k] for p in per])), ci=boot_cluster({s: np.array(x) for s, x in cl.items()}))
        out[str(D)] = dict(states=len(per), **res)
        f = lambda k: f"{res[k]['mean']:+.2f} [{res[k]['ci'][0]:+.2f},{res[k]['ci'][1]:+.2f}]"
        lines += [f"{D.name}: {len(per)} states",
                  f"  message (all feasible): max {f('msg_max')} mean {f('msg_mean')} share>0 {res['msg_pos']['mean']:.2f}",
                  f"  message, exactly 1 action changed (n/state {res['one_n']['mean']:.1f}): max {f('one_max')} mean {f('one_mean')}",
                  f"  message, no action changed at t: max {f('zero_max')} mean {f('zero_mean')}",
                  f"  forced single-agent action change (n/state 63): max {f('forced_max')} mean {f('forced_mean')} share>0 {res['forced_pos']['mean']:.2f} | best-of-N matched to the 1-action message set {f('forced_matched_max')}",
                  f"  paired, same agent + same action: message - forced {f('paired_msg_minus_forced')} (share message better {res['paired_share_msg_better']['mean']:.2f})"]
    Path(a.out).write_text(json.dumps(out, indent=1)); print('\n'.join(lines), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__); p.add_argument('dirs', nargs='+'); p.add_argument('--out', required=True)
    main(p.parse_args())
