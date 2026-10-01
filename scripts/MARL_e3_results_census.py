#!/usr/bin/env python3
"""CENSUS of every E3 evaluation in research/marl_budget written since 29/09 18:00 (user 01/10 08:5x: "đọc lại hết đống
kết quả mà m chạy hqua"). Read-only: it never writes inside an evaluation directory.

For every rows.json under a directory with a COMPLETE manifest: group rows by (actor, rule); identify the panel by its
episode keys (seedNNN_loadH) and the 3x3 / 4x4 map by the directory; pair each arm with the zero-byte student of the SAME
training seed on the SAME episodes (distill_none_s<s>, rule 'none'), looked up first in the same top directory, then in
the development reference e3_codesign_eval_20260929; effect = sum(waiting arm)/sum(waiting Z) - 1 over the shared
episodes, 95 % traffic-seed bootstrap (both headways together, 2000 draws, seed 0).  Arms without a same-seed Z on the
same episodes are listed with their mean waiting and NO effect (never paired across panels or seeds).
Also records per arm: capacity, order, relay, deliveries, quant, loss, bytes/episode, manifest self_check, evaluator
script hash prefix, and whether the actor checkpoint is newer than the evaluation (a provenance flag).
Output: research/marl_budget/e3_results_census_20261001.{json,md}
"""
from __future__ import annotations
import ast, json, os, re, time
from collections import defaultdict
import numpy as np

R = 'research/marl_budget'; SINCE = '0929_1800'
OUT = f'{R}/e3_results_census_20261001'


def lit(x):
    if isinstance(x, str):
        try:
            return ast.literal_eval(x)
        except Exception:
            return x
    return x


def mtime(p):
    return time.strftime('%m%d_%H%M', time.localtime(os.path.getmtime(p)))


def seed_of(actor):
    m = re.search(r'_s(\d+)(?:_|$)', actor)
    return (int(m.group(1)), False) if m else (0, True)


def boot(a, b, eps, draws=2000, seed=0):
    ts = sorted({e.split('_')[0] for e in eps}); idx = {t: [i for i, e in enumerate(eps) if e.startswith(t + '_')] for t in ts}
    A = np.array([a[e] for e in eps]); B = np.array([b[e] for e in eps]); rng = np.random.default_rng(seed); bs = []
    for _ in range(draws):
        ii = np.concatenate([idx[ts[k]] for k in rng.choice(len(ts), len(ts))])
        bs.append(A[ii].sum() / B[ii].sum() - 1)
    return float(A.sum() / B.sum() - 1), *map(float, np.percentile(bs, [2.5, 97.5]))


def main():
    arms = []          # one entry per (dir, actor, rule)
    for top in sorted(os.listdir(R)):
        tp = os.path.join(R, top)
        if not os.path.isdir(tp):
            continue
        for dp, dn, fn in os.walk(tp):
            if 'scenarios' in dn:
                dn.remove('scenarios')
            if 'rows.json' not in fn or 'manifest.json' not in fn:
                continue
            mp = os.path.join(dp, 'manifest.json')
            if mtime(mp) < SINCE:
                continue
            m = json.load(open(mp))
            if m.get('status') != 'COMPLETE':
                continue
            a = lit(m.get('args')) or {}; sh = lit(m.get('source_hashes')) or {}
            ev = next((k for k in sh if 'eval' in k or 'probe' in k), None)
            rows = json.load(open(os.path.join(dp, 'rows.json')))
            if not isinstance(rows, list) or not rows or 'queue_sum' not in rows[0]:
                continue
            g = defaultdict(dict); by = defaultdict(list)
            for r in rows:
                g[(r.get('actor', '?'), r.get('rule', '?'))][r['episode']] = r['queue_sum']
                by[(r.get('actor', '?'), r.get('rule', '?'))].append(r.get('bytes', 0))
            ck_newer = []
            for spec in a.get('actors', []) if isinstance(a.get('actors'), list) else []:
                path = spec.split('=', 1)[-1]
                if os.path.exists(path) and os.path.getmtime(path) > os.path.getmtime(mp):
                    ck_newer.append(path)
            for (actor, rule), d in g.items():
                arms.append(dict(top=top, dir=os.path.relpath(dp, R), actor=actor, rule=rule, eps=d,
                                 bytes=float(np.mean(by[(actor, rule)])), n=len(d), mt=mtime(mp),
                                 self_check=m.get('self_check'), capacity=a.get('capacity'), order=a.get('order'),
                                 relay=a.get('relay'), quant=a.get('quant'), loss=a.get('loss'),
                                 evaluator=(ev or '?').split('/')[-1], ev_hash=(sh.get(ev, '') or '')[:10] if ev else '',
                                 ckpt_newer_than_eval=ck_newer))
    # zero-byte references, keyed by (top, seed, episode-set)
    Zs = [x for x in arms if re.fullmatch(r'distill_none_s\d+', x['actor']) and x['rule'] == 'none']
    out = []
    for x in arms:
        s, guessed = seed_of(x['actor'])
        if guessed:   # rows without an actor field (probes): take the seed from the run directory name, else leave unpaired
            m = re.search(r'(?:^|_)s(\d+)(?:_|$)', os.path.basename(x['dir']))
            s, guessed = (int(m.group(1)), False) if m else (None, True)
        key = frozenset(x['eps'])
        cands = [] if s is None else [z for z in Zs if z['actor'] == f'distill_none_s{s}' and frozenset(z['eps']) == key and z is not x]
        z = next((c for c in cands if c['top'] == x['top']), None) or \
            next((c for c in cands if c['top'] == 'e3_codesign_eval_20260929'), None) or (cands[0] if cands else None)
        rec = {k: v for k, v in x.items() if k != 'eps'}
        rec['panel'] = f"{min(e.split('_')[0] for e in x['eps'])}..{max(e.split('_')[0] for e in x['eps'])}"
        rec['mean_wait'] = float(np.mean(list(x['eps'].values()))); rec['seed'] = s; rec['seed_guessed'] = guessed
        if z is not None and x['actor'] != z['actor']:
            e, lo, hi = boot(x['eps'], z['eps'], sorted(key))
            rec.update(Z=z['dir'], effect=100 * e, lo=100 * lo, hi=100 * hi)
        out.append(rec)
    out.sort(key=lambda r: (r['top'], r['dir'], r['rule']))
    json.dump(out, open(OUT + '.json', 'w'), indent=1)
    lines = ['# E3 results census (every COMPLETE evaluation since 29/09 18:00; read-only)', '',
             'effect = paired waiting ratio − 1 vs the same-seed zero-byte student on the same episodes (negative = better); '
             '95 % traffic-seed bootstrap.  "—" = no same-seed Z on the same episodes (not paired).', '']
    cur = None
    for r in out:
        if r['top'] != cur:
            cur = r['top']; lines += ['', f'## {cur}', '',
                                      '| run | actor | rule | cap | order | panel | n | wait | bytes/ep | effect % [95 %] | sc | flags |',
                                      '|---|---|---|---|---|---|---|---|---|---|---|---|']
        eff = f"{r['effect']:+.2f} [{r['lo']:+.2f}, {r['hi']:+.2f}]" if 'effect' in r else '—'
        flags = ('seed?' if r['seed_guessed'] else '') + (' CKPT-NEWER' if r['ckpt_newer_than_eval'] else '') + \
                ('' if r['n'] in (128, 64) else f" n={r['n']}")
        lines.append(f"| {r['dir'].split('/', 1)[-1]} | {r['actor']} | {r['rule']} | {r['capacity']} | {r['order']} | "
                     f"{r['panel']} | {r['n']} | {r['mean_wait']:.0f} | {r['bytes']:.0f} | {eff} | {r['self_check']} | {flags.strip()} |")
    open(OUT + '.md', 'w').write('\n'.join(lines) + '\n')
    print(f'{len(out)} arms; paired {sum("effect" in r for r in out)}; unpaired {sum("effect" not in r for r in out)}; '
          f'ckpt-newer flags {sum(bool(r["ckpt_newer_than_eval"]) for r in out)}')


if __name__ == '__main__':
    main()
