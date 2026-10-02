#!/usr/bin/env python3
"""Report of PROTOCOL_E3_COMPAT_MAP_20261001.md Part A (written before the full run).  Usage: <probe out dir>.
r_now = w_now(j, t, ep) - mu(j, t, load), mu = mean over the traffic seeds of the same (j, t, load), from the UNIQUE
(ep, t, j) truths (the world is common to all cells: asserted).  S(a, cell) = mean r_now over entries of age bin a;
95 % CI by episode bootstrap.  SM1 / SM2 / SM3 as in the protocol."""
from __future__ import annotations
import json, sys
from pathlib import Path
import numpy as np

ORDERS = ('agefirst', 'prefix'); CAPS = ('iid', 'cap4', 'low', 'const1', 'const2')
BINS = [('0', 0, 0), ('1-2', 1, 2), ('3-4', 3, 4), ('5-8', 5, 8), ('>=9', 9, 99)]
OLD = ('3-4', '5-8', '>=9'); MIN_N = 200


def main(d):
    d = Path(d); eps = json.loads((d / 'episodes.json').read_text()); load_of = np.array([e['load'] for e in eps])
    Z = {(o, c): dict(np.load(d / f'{o}_{c}.npz')) for o in ORDERS for c in CAPS}
    truth = {}
    for z in Z.values():
        for ep, t, j, w in zip(z['ep'], z['t'], z['sender'], z['w_now']):
            k = (int(ep), int(t), int(j))
            if truth.setdefault(k, int(w)) != int(w):
                raise SystemExit(f'SELF-CHECK FAIL: truth differs across cells at {k}')
    acc = {}
    for (ep, t, j), w in truth.items():
        acc.setdefault((j, t, load_of[ep]), []).append(w)
    mu = {k: float(np.mean(v)) for k, v in acc.items()}
    r_all = np.array([w - mu[(j, t, load_of[ep])] for (ep, t, j), w in truth.items()]); sw = float(r_all.std())
    rng = np.random.default_rng(0); n_ep = len(eps); B = [rng.integers(0, n_ep, n_ep) for _ in range(1000)]
    S = {}; L = [f'sigma_w (pooled SD of r_now) = {sw:.2f}; unique truths {len(truth)}; episodes {n_ep}',
                 'order | capacity | ' + ' | '.join(f'S(a {b[0]}) [n]' for b in BINS) + ' | drift beyond content a>=3']
    for (o, c), z in Z.items():
        r = z['w_now'] - np.array([mu[(int(j), int(t), load_of[int(ep)])] for ep, t, j in zip(z['ep'], z['t'], z['sender'])])
        tc = z['t'] - z['age']; okc = tc >= 0
        rc = np.full(len(r), np.nan)
        rc[okc] = z['w_copy'][okc] - np.array([mu.get((int(j), int(t), load_of[int(ep)]), np.nan)
                                               for ep, t, j in zip(z['ep'][okc], tc[okc], z['sender'][okc])])
        cells = []
        for name, lo, hi in BINS:
            sel = (z['age'] >= lo) & (z['age'] <= hi); n = int(sel.sum())
            if n < MIN_N:
                S[(o, c, name)] = None; cells.append(f'  -  [{n}]'); continue
            m = float(r[sel].mean()); per = np.array([r[sel & (z['ep'] == e)].sum() for e in range(n_ep)]); cnt = np.array([(sel & (z['ep'] == e)).sum() for e in range(n_ep)])
            bs = [per[b].sum() / max(cnt[b].sum(), 1) for b in B]; lo95, hi95 = np.percentile(bs, [2.5, 97.5])
            S[(o, c, name)] = (m, float(lo95), float(hi95), n); cells.append(f'{m:+.2f} [{lo95:+.2f}, {hi95:+.2f}] [{n}]')
        old = z['age'] >= 3; dr = np.nanmean((r - rc)[old]) if old.sum() else np.nan
        L.append(f'{o} | {c} | ' + ' | '.join(cells) + f' | {dr:+.2f}')
    sm1 = all(v is None or v[1] <= 0 <= v[2] or abs(v[0]) < 0.05 * sw for (o, c, b), v in S.items() if o == 'agefirst')
    sm2 = {}
    for c in ('iid', 'cap4', 'low'):
        z = Z[('prefix', c)]; sel = z['age'] >= 3
        r = z['w_now'][sel] - np.array([mu[(int(j), int(t), load_of[int(ep)])] for ep, t, j in zip(z['ep'][sel], z['t'][sel], z['sender'][sel])])
        sm2[c] = (float(r.mean()) if sel.sum() >= MIN_N else None, int(sel.sum()))
    SM2 = all(v[0] is not None and v[0] < 0 for v in sm2.values())

    def rms(o):
        dif = [S[(o, c, b)][0] - S[(o, 'iid', b)][0] for c in ('cap4', 'low', 'const1') for b in OLD
               if S[(o, c, b)] is not None and S[(o, 'iid', b)] is not None and S[('agefirst' if o == 'prefix' else 'prefix', c, b)] is not None
               and S[('agefirst' if o == 'prefix' else 'prefix', 'iid', b)] is not None]
        return (float(np.sqrt(np.mean(np.square(dif)))) if dif else None), len(dif)
    rp, n_p = rms('prefix'); ra, n_a = rms('agefirst')
    SM3 = rp is not None and ra is not None and rp >= 2 * ra and rp >= 0.05 * sw
    L += [f'SM1 age-first S = 0 within CI or |S| < 0.05 sigma in every bin and capacity: {"SUPPORTED" if sm1 else "NOT SUPPORTED"}',
          f'SM2 congestion S(a >= 3) < 0 at iid / cap4 / low: ' + ', '.join(f'{c} {v[0]:+.2f} (n {v[1]})' if v[0] is not None else f'{c} - (n {v[1]})'
                                                                       for c, v in sm2.items()) + f' -> {"SUPPORTED" if SM2 else "NOT SUPPORTED"}',
          f'SM3 RMS shift vs iid over a >= 3 bins (cap4 / low / const1): congestion {rp} (n {n_p}) vs age-first {ra} (n {n_a}); '
          f'need >= 2x and >= {0.05 * sw:.2f} -> {"SUPPORTED" if SM3 else "NOT SUPPORTED"}']
    text = '\n'.join(L); print(text); (d / 'report.txt').write_text(text + '\n')
    (d / 'report.json').write_text(json.dumps(dict(sigma_w=sw, S={'|'.join(k): v for k, v in S.items()}, SM1=sm1, SM2=SM2, SM3=SM3,
                                                   sm2=sm2, rms_prefix=rp, rms_agefirst=ra), indent=1))


if __name__ == '__main__':
    main(sys.argv[1])
