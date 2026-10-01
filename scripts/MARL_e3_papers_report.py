#!/usr/bin/env python3
"""Consolidated report of the papers-prescribed E3 arms (PROTOCOL_E3_PAPERS_PRESCRIBED_20260929.md).  Read-only.

For every COMPLETE evaluation in research/marl_budget/e3_codesign_eval_20260929/<tag> and every rule in it: mean waiting,
accounted bytes per step and STREAM bytes per step (receiver-side rules rxq/rxold: the prefix stream, i.e. the same
actor's prefix-rule bytes on the same episode when evaluated, else the prefix system's), and paired comparisons over the
common episodes (bootstrap over traffic seeds, both headways kept together, 4000 resamples, seed 0) against:
  none(same arch)  the co-trained none actor of the same architecture (flat: none_s0; set actors: set_none_s0 if complete)
  maxq             the best heuristic (e3_mp2_message_check_20260929, kind maxq, rule none)
  prefix system    the mean of the 5 scratch prefix actors under the prefix (v3 truncation rows)
PASS iff the rule communicates (not 'none'), the upper bound vs none(same arch) is < 0 and stream bytes <= the prefix's
188.7 B/step (the pre-stated criterion).  Arms trained for more than 2000 iterations are flagged.
"""
from __future__ import annotations
import argparse, json
from collections import defaultdict
from pathlib import Path
import numpy as np

B = Path('research/marl_budget')


def boot(d, n=4000, seed=0):
    by = defaultdict(list)
    for e, v in d.items():
        by[e.split('_')[0]].append(v)
    k = sorted(by); r = np.random.default_rng(seed)
    bs = [np.mean(sum((by[x] for x in r.choice(k, len(k))), [])) for _ in range(n)]
    return float(np.mean(list(d.values()))), float(np.quantile(bs, 0.025)), float(np.quantile(bs, 0.975))


def rows_of(tag, rule):
    f = B / 'e3_codesign_eval_20260929' / tag / 'rows.json'
    return {r['episode']: (r['queue_sum'], r['bytes'] / 26.0) for r in json.loads(f.read_text()) if r['rule'] == rule}


def main(a):
    E = B / 'e3_codesign_eval_20260929'
    done = {d.name for d in E.iterdir() if d.is_dir() and (d / 'manifest.json').exists()}
    none_flat = rows_of('none_s0', 'none'); none_set = rows_of('set_none_s0', 'none') if 'set_none_s0' in done else None
    mq = {r['episode']: r['queue_sum'] for r in json.loads((B / 'e3_mp2_message_check_20260929/rows.json').read_text()) if r['kind'] == 'maxq' and r['rule'] == 'none'}
    pref = defaultdict(list)
    for t in ('scratch_s3', 'scratch_rs_s0', 'scratch_rs_s1', 'scratch_rs_s2', 'scratch_rs_s4'):
        for r in json.loads((B / 'e3_truncation_cl_v3_20260929' / t / 'rows.json').read_text()):
            if r['rule'] == 'prefix':
                pref[r['episode']].append((r['queue_sum'], r['bytes'] / 26.0))
    ps = {e: float(np.mean([x[0] for x in v])) for e, v in pref.items() if len(v) == 5}; psb = float(np.mean([x[1] for v in pref.values() for x in v]))
    lines = [f'prefix system {psb:.1f} B/step; none(flat) = none_s0; none(set) = ' + ('set_none_s0' if none_set else 'NOT COMPLETE (set arms compared with none_s0)'),
             f'{"arm/rule":30s} {"wait":>7s} {"acct B":>7s} {"strm B":>7s}  {"vs none(same arch)":>26s}  {"vs maxq":>9s}  {"vs prefix sys":>13s}  verdict']
    out = {}
    for tag in sorted(done):
        M = json.loads((E / tag / 'manifest.json').read_text()); dels = M['args']['deliveries']
        ck = json.loads((B / 'e3_delivery_actors_20260929' / tag / 'config.json').read_text()) if (B / 'e3_delivery_actors_20260929' / tag / 'config.json').exists() else {}
        is_set = bool(ck.get('set_actor')); ref = none_set if (is_set and none_set) else none_flat
        for rule in dels:
            R = rows_of(tag, rule)
            eps = sorted(set(R) & set(ref) & set(mq) & set(ps))
            if not eps:
                continue
            strm = {}
            if rule in ('rxq', 'rxold', 'nbr') and 'prefix' in dels:
                P = rows_of(tag, 'prefix'); sb = float(np.mean([P[e][1] for e in eps if e in P]))
            elif rule in ('rxq', 'rxold', 'nbr'):
                sb = psb
            else:
                sb = float(np.mean([R[e][1] for e in eps]))
            vn = boot({e: R[e][0] / ref[e][0] - 1 for e in eps}); vm = boot({e: R[e][0] / mq[e] - 1 for e in eps}); vp = boot({e: R[e][0] / ps[e] - 1 for e in eps})
            ok = vn[2] < 0 and sb <= psb + 1e-6 and rule != 'none'
            if rule == 'none':
                verdict = 'reference' if tag in ('none_s0', 'set_none_s0') else 'no-comm (not a comm claim)'
            else:
                verdict = 'PASS' if ok else ('tie' if vn[1] < 0 < vn[2] else ('worse' if vn[1] >= 0 else 'better, bytes>prefix'))
            if ck.get('iters', 2000) != 2000:
                verdict += f' [{ck.get("iters")} it vs the 2000-it reference]'
            out[f'{tag}/{rule}'] = dict(wait=float(np.mean([R[e][0] for e in eps])), acct_bytes=float(np.mean([R[e][1] for e in eps])), stream_bytes=sb,
                                       vs_none_same_arch=vn, vs_maxq=vm, vs_prefix_system=vp, verdict=verdict, set_actor=is_set, episodes=len(eps))
            lines.append(f'{tag + "/" + rule:30s} {out[f"{tag}/{rule}"]["wait"]:7.1f} {out[f"{tag}/{rule}"]["acct_bytes"]:7.1f} {sb:7.1f}  '
                         f'{vn[0]:+.4f} [{vn[1]:+.4f}, {vn[2]:+.4f}]  {vm[0]:+.4f}  {vp[0]:+.4f}        {verdict}')
    Path(a.out + '.json').write_text(json.dumps(out, indent=1)); Path(a.out + '.txt').write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--out', default='research/marl_budget/e3_papers_report_20260929')
    main(p.parse_args())
