#!/usr/bin/env python3
"""F3 (PROTOCOL_FIELD_F2_F3T_F4_20261008, Amendments A3 / A3b): the paper's quantile forecaster on real Hamburg traffic lights.
Data: research/field_data/hamburg/<thing>_{primary_signal,detector_car}.csv.gz (state-change / occupancy-change events), 2026-10-01..07 UTC.
States: 1 red, 2 amber, 3 green, 4 red-amber.  Per connection a 1-Hz grid; red = {1, 4} -> target seconds to the next green (3);
green = 3 -> target seconds to the next amber or red.  A phase longer than 300 s, or one whose end lies beyond the window, is censored
(change-event data: a missing end means a missing stream, not a long phase).
Features (18): red, green, time in state / 60, last three completed green and red durations / 60, detector occupancy mean over the last 10 s
and 60 s / 100, hour sin / cos, weekend, system one-hot (4).
Model: CITY_n2_fit.QNet (MLP 64-64, monotone quantiles 0.1 / 0.5), CITY_n2_fit.pinball, Adam 1e-3, batch 1024, <= 40 epochs, early stop on
10 % of training seconds; training = Oct 1-5 (every 2nd second), test = Oct 6-7 (every second).
Baselines: B1 = the connection's last completed duration of that phase minus elapsed (>= 0); B2 = per connection and state, empirical 0.1 /
0.5 quantile of the remaining duration given elapsed (1-s bins; training days).
H1 coverage P(realized < predicted q), q = 0.1 / 0.5, per state; H2 MAE of q0.5 vs B1 / B2; H3 green q0.1 'unsafe early' share.
Bootstrap (B 2000) clustered by connection-day.  Output research/field_data/results/f3_report.txt.   W_SMOKE=1: hamburg_smoke, 1 day."""
import gzip, json, os, sys
from pathlib import Path
import numpy as np
import pandas as pd
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_n2_fit as NF  # noqa: E402
SM = os.environ.get('W_SMOKE') == '1'; H = ROOT / ('research/field_data/hamburg_smoke' if SM else 'research/field_data/hamburg')
OUT = ROOT / 'research/field_data/results'; T0 = pd.Timestamp('2026-10-01T00:00:00Z'); NDAY = 1 if SM else 7; T1 = T0 + pd.Timedelta(days=NDAY)
TRAIN_DAYS = {0} if SM else {0, 1, 2, 3, 4}
man = json.loads((H / ('manifest_smoke.json' if SM else 'manifest.json')).read_text()); SYS = [p['sid'] for p in man['systems']]
torch.manual_seed(0); np.random.seed(0)


def load(fn):
    d = pd.read_csv(fn); d['t'] = ((pd.to_datetime(d.time, utc=True) - T0).dt.total_seconds()).round().astype(int); return d.sort_values('t')


rows = []
for p in man['systems']:
    si = SYS.index(p['sid'])
    for c in p['conns']:
        th = c['thing']; ps = load(H / f'{th}_primary_signal.csv.gz'); de = load(H / f'{th}_detector_car.csv.gz'); n = NDAY * 86400
        st = np.full(n, -1, int); occ = np.zeros(n); ch = ps[(ps.t >= 0) & (ps.t < n)]
        for (t, r), (t2, _) in zip(ch[['t', 'result']].values, list(ch[['t', 'result']].values[1:]) + [(n, 0)]):
            st[int(t):int(t2)] = int(r)
        dd = de[(de.t >= 0) & (de.t < n)]
        for (t, r), (t2, _) in zip(dd[['t', 'result']].values, list(dd[['t', 'result']].values[1:]) + [(n, 0)]):
            occ[int(t):int(t2)] = float(r)
        cs = np.concatenate([[0], np.cumsum(occ)]); idx = np.arange(n)
        m10 = (cs[idx + 1] - cs[np.maximum(0, idx - 9)]) / np.minimum(10, idx + 1); m60 = (cs[idx + 1] - cs[np.maximum(0, idx - 59)]) / np.minimum(60, idx + 1)
        cls = np.where(np.isin(st, [1, 4]), 0, np.where(st == 3, 1, np.where(st == 2, 2, -1)))   # 0 red, 1 green, 2 amber, -1 unknown
        # runs of the red / green classes (amber is part of neither; a red run ends at green, a green run at amber or red)
        brk = np.flatnonzero(np.diff(cls)) + 1; starts = np.concatenate([[0], brk]); ends = np.concatenate([brk, [n]])
        runs = [(int(cls[a]), int(a), int(b)) for a, b in zip(starts, ends)]
        last = {0: [], 1: []}
        for k, (c_, a, b) in enumerate(runs):
            if c_ not in (0, 1):
                continue
            end_ok = b < n and (b - a) <= 300 and (k + 1 < len(runs)) and runs[k + 1][0] != -1
            if end_ok and len(last[0]) >= 3 and len(last[1]) >= 3:
                t = np.arange(a, b); day = t // 86400; hr = (t % 86400) / 3600.0; L = len(t); one = np.ones(L)
                we = np.array([float((T0 + pd.Timedelta(days=int(dd))).weekday() >= 5) for dd in day])
                rows.append(pd.DataFrame(dict(conn=th, sys=si, day=day, cls=c_, el=t - a, y=b - t, g1=last[1][-1] * one, g2=last[1][-2] * one,
                                              g3=last[1][-3] * one, r1=last[0][-1] * one, r2=last[0][-2] * one, r3=last[0][-3] * one, o10=m10[t],
                                              o60=m60[t], hs=np.sin(2 * np.pi * hr / 24), hc=np.cos(2 * np.pi * hr / 24), we=we)))
            if end_ok:
                last[c_].append(b - a)
R = pd.concat(rows, ignore_index=True)
print('rows', len(R), 'connections', R.conn.nunique(), 'by class', R.cls.value_counts().to_dict(), flush=True)


def X(D):
    f = [D.cls.eq(0).astype(float), D.cls.eq(1).astype(float), D.el / 60] + [D[c] / 60 for c in ('g1', 'g2', 'g3', 'r1', 'r2', 'r3')] + \
        [D.o10 / 100, D.o60 / 100, D.hs, D.hc, D.we] + [(D.sys == s).astype(float) for s in range(4)]
    return torch.tensor(np.stack([np.asarray(v, np.float32) for v in f], 1))


tr = R[R.day.isin(TRAIN_DAYS)].iloc[::2]; te = R[~R.day.isin(TRAIN_DAYS)] if not SM else R.iloc[1::2]
va = tr.sample(frac=0.1, random_state=0); tr = tr.drop(va.index)
net = NF.QNet(18); opt = torch.optim.Adam(net.parameters(), 1e-3); Xt, yt = X(tr), torch.tensor(tr.y.values, dtype=torch.float32)
Xv, yv = X(va), torch.tensor(va.y.values, dtype=torch.float32); best = (1e9, None); bad = 0
for ep in range(40):
    perm = torch.randperm(len(Xt))
    for i in range(0, len(Xt), 1024):
        b = perm[i:i + 1024]; loss = NF.pinball(net(Xt[b]), yt[b], torch.ones(len(b))); opt.zero_grad(); loss.backward(); opt.step()
    with torch.no_grad():
        lv = float(NF.pinball(net(Xv), yv, torch.ones(len(yv))))
    if lv < best[0] - 1e-4:
        best = (lv, {k: v.clone() for k, v in net.state_dict().items()}); bad = 0
    else:
        bad += 1
        if bad >= 5:
            break
net.load_state_dict(best[1])
with torch.no_grad():
    P = net(X(te)).numpy()
te = te.assign(q1=P[:, 0], q5=P[:, 1])
te = te.assign(b1=np.maximum(0, np.where(te.cls == 1, te.g1, te.r1) - te.el))
emp = {}                                                               # B2: conditional empirical quantiles from training days
trall = R[R.day.isin(TRAIN_DAYS)]
for (cn, c_), g in trall.groupby(['conn', 'cls']):
    emp[(cn, c_)] = {e: (np.percentile(gg.y, 10), np.percentile(gg.y, 50)) for e, gg in g.groupby('el') if len(gg) >= 20}
b2 = [emp.get((r.conn, r.cls), {}).get(r.el, (np.nan, np.nan)) for r in te.itertuples()]
te = te.assign(b2q1=[x[0] for x in b2], b2q5=[x[1] for x in b2]); te = te.assign(cd=te.conn + ':' + te.day.astype(str))
rng = np.random.default_rng(2026); out = [f'== F3 Hamburg: the paper forecaster (QNet 64-64, q 0.1 / 0.5) on real signals; systems {SYS}; '
                                          f'{R.conn.nunique()} connections; train days {sorted(TRAIN_DAYS)}, test {len(te)} seconds']
for c_, nm in ((0, 'red (time to green)'), (1, 'green (time to red)')):
    g = te[te.cls == c_]; cds = g.cd.unique(); by = {k: gg for k, gg in g.groupby('cd')}

    def boot(fn):
        o = fn(g); bs = [fn(pd.concat([by[k] for k in rng.choice(cds, len(cds))])) for _ in range(200 if SM else 2000)]
        lo, hi = np.nanpercentile(bs, [2.5, 97.5]); return o, lo, hi
    c1 = boot(lambda d: float((d.y < d.q1).mean())); c5 = boot(lambda d: float((d.y < d.q5).mean()))
    m = boot(lambda d: float((d.y - d.q5).abs().mean())); mb1 = boot(lambda d: float((d.y - d.b1).abs().mean()))
    gg = g.dropna(subset=['b2q5']); mb2 = float((gg.y - gg.b2q5).abs().mean()); cb2 = float((gg.y < gg.b2q1).mean())
    out.append(f'{nm}: n {len(g)}; H1 coverage q0.1 {c1[0]:.3f} [{c1[1]:.3f}, {c1[2]:.3f}] (nominal 0.10), q0.5 {c5[0]:.3f} [{c5[1]:.3f}, {c5[2]:.3f}] '
               f'(nominal 0.50); H2 MAE q0.5 {m[0]:.2f} s [{m[1]:.2f}, {m[2]:.2f}] vs B1 {mb1[0]:.2f} [{mb1[1]:.2f}, {mb1[2]:.2f}], B2 {mb2:.2f} '
               f'(B2 coverage q0.1 {cb2:.3f}, n {len(gg)}); median realized {g.y.median():.1f} s')
out.append('H3 (green): the published q0.1 time to red is "unsafe early" (realized earlier) at the green q0.1 coverage above; Tampa minEndTime: about 0.12.')
sfx = '_smoke' if SM else ''; (OUT / f'f3_report{sfx}.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
