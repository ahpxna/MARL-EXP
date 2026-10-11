#!/usr/bin/env python3
"""F1-B B0 offline checks (exit 1 on failure) on recorded grid4 RL-H traces, provider c2 (= CITY_spat_forecast_k logic on the augmented table):
  KB0-1  convention with TRUE switch times (true remaining green, true run lengths of intermediate greens): 0 error in every branch
  KB0-2  negative controls fail in the RIGHT branch: (i) no first +1 -> green->next fails (C-71); (ii) no chain +1 -> nongreen->after-next fails (C-84)
  KB0-4  causality: forecasts at t unchanged when the trace after t is replaced by shuffled future phases
Usage: CITY_f1b_b0_check.py <out txt> <npz files>"""
import sys
from collections import Counter
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_spat_forecast as FC  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
import scripts.CITY_spat_forecast_c2 as C2  # noqa: E402


class NoFirst(FK.ForecastK):
    def ttg(self, tid, ph, spent, serve, rem_fn=None, full_fn=None):
        gs = self.G[tid]
        if ph in gs:
            c = gs.index(ph); return self.chain(tid, (c + 1) % len(gs), (rem_fn or self.rem)(tid, ph, spent) + self.NG[tid][c], serve, full_fn=full_fn)
        return super().ttg(tid, ph, spent, serve, rem_fn, full_fn)


class NoChain(FK.ForecastK):
    def chain(self, tid, c, t0, serve, rem_fn=None, full_fn=None):
        gs = self.G[tid]; k = len(gs); t = t0
        for m in range(k):
            g = gs[(c + m) % k]
            if g in serve:
                return t + FK.OBS
            t += (full_fn or self.full)(tid, g) + self.NG[tid][(c + m) % k]
        return None


def conv(F, files):
    err = {}
    for f in files:
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P, S = z['phases'], z['spent']
        for j, tid in enumerate(ids):
            gs = F.G[tid]; runs = FC.runs(P[:, j])
            for r_i, (ph, st, ln, complete) in enumerate(runs):
                if not complete:
                    continue
                seq = [rr for rr in runs[r_i + 1:] if rr[0] in gs]
                for i in range(st, st + ln):
                    t = i + 1; s = float(S[i, j])
                    if ph in gs:
                        err.setdefault('ttr', Counter())[round((ln - s) + FK.OBS - ((st + ln + 1) - t), 6)] += 1
                    for m, tgt in enumerate(seq[:len(gs) - (1 if ph in gs else 0)]):
                        if not tgt[3] or any(not x[3] for x in seq[:m]):
                            break
                        lens = {x[0]: x[2] for x in seq[:m]}
                        fc = F.ttg(tid, ph, s, {tgt[0]}, rem_fn=lambda a, b, c, ln=ln: ln - c, full_fn=lambda a, g, lens=lens: lens.get(g, np.nan))
                        err.setdefault(f'ttg_{"green" if ph in gs else "nongreen"}_ahead{m + 1}', Counter())[round(fc - ((tgt[1] + 1) - t), 6)] += 1
    return err


def ok_all(err):
    return all(c.get(0.0, 0) == sum(c.values()) for c in err.values())


if __name__ == '__main__':
    out_f, files = sys.argv[1], sys.argv[2:]; T = C2.augment(FC.fit(files)); out = [f'== F1-B B0 offline checks on {len(files)} grid4 traces']; ok = True
    e = conv(FK.ForecastK(T, 0.5), files); g = ok_all(e); ok &= g
    out += [f'  KB0-1 {k:22s} n {sum(c.values()):8d}: error 0 on {100 * c.get(0.0, 0) / sum(c.values()):6.2f} %' for k, c in sorted(e.items())] + [f'  KB0-1: {"PASS" if g else "FAIL"}']
    e1 = conv(NoFirst(T, 0.5), files); f1 = e1['ttg_green_ahead1'].get(0.0, 0) == 0 and all(ok_all({k: v}) for k, v in e1.items() if k != 'ttg_green_ahead1' and not k.startswith('ttg_green'))
    e2 = conv(NoChain(T, 0.5), files); f2 = e2['ttg_nongreen_ahead2'].get(0.0, 0) == 0 and ok_all({k: v for k, v in e2.items() if k in ('ttr', 'ttg_green_ahead1', 'ttg_nongreen_ahead1')})
    ok &= f1 and f2
    out.append(f'  KB0-2 (i) no first +1: green->next {dict(e1["ttg_green_ahead1"].most_common(2))}; fails ONLY there: {"PASS" if f1 else "FAIL"}')
    out.append(f'  KB0-2 (ii) no chain +1: nongreen->after-next {dict(e2["ttg_nongreen_ahead2"].most_common(2))}; other branches intact: {"PASS" if f2 else "FAIL"}')
    rng = np.random.default_rng(0); F = FK.ForecastK(T, 0.1); diff = 0; n = 0
    for f in files[:3]:
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P, S = z['phases'], z['spent']
        for i in range(100, len(P) - 1, 97):
            P2 = P.copy(); P2[i + 1:] = rng.permutation(P2[i + 1:])
            for j, tid in enumerate(ids):
                for g in F.G[tid]:
                    if int(P[i, j]) != g:
                        n += 1; diff += F.ttg(tid, int(P[i, j]), float(S[i, j]), {g}) != F.ttg(tid, int(P2[i, j]), float(S[i, j]), {g})
    c4 = diff == 0 and n > 0; ok &= c4; out.append(f'  KB0-4 causality: {n} forecasts at t with the future shuffled, {diff} changed: {"PASS" if c4 else "FAIL"}')
    out.append(f'F1-B B0 OFFLINE: {"PASS" if ok else "FAIL"}'); t = '\n'.join(out) + '\n'; Path(out_f).write_text(t); print(t); sys.exit(0 if ok else 1)
