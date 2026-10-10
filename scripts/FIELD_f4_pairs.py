#!/usr/bin/env python3
"""F4 data preparation (PROTOCOL_FIELD_F2_F3T_F4_20261008 + A1): NGSIM Peachtree leader-follower pairs and free approaches to a stop.
  units: feet -> metres; window = session, keyed by Global_Time - 100 * Frame_ID (two bases); vehicle key (window, Vehicle_ID).
  smoothing: symmetric exponential moving average of Local_Y per vehicle, Delta = 10 frames (1 s), kernel truncated at 3 Delta;
             speed = forward difference of the smoothed position (so a scripted leader at that speed reproduces the position).
  pairs: follower and leader both through (Movement 1), northbound or southbound, same Lane_ID, follower's Preceding = leader, consecutive
         frames; cut into non-overlapping windows of 150-300 frames; keep windows with 0 < gap < 80 m throughout and without a follower
         stop (v < 1 m/s) at gap > 25 m.  Split train / test by sha1(follower key) (60 / 40).
  free approaches: through vehicles with no leader within 80 m from v >= 8 m/s down to v < 0.5 m/s.
Output research/field_data/results/f4_pairs.npz (+ f4_pairs_summary.json).  KF4-1 (signal-log alignment) is reported in f4_kf41.txt."""
import hashlib, json, sys
from pathlib import Path
import numpy as np
import pandas as pd
ROOT = Path(__file__).resolve().parents[1]; F = ROOT / 'research/field_data'; OUT = F / 'results'; OUT.mkdir(exist_ok=True)
FT = 0.3048; DEL = 10
d = pd.read_csv(F / 'ngsim/peachtree/NGSIM_Peachtree_Vehicle_Trajectories.csv')
base = d.Global_Time - 100 * d.Frame_ID                               # two sessions share Vehicle_ID / Frame_ID ranges; their base time differs
d['win'] = base.map({v: i for i, v in enumerate(sorted(base.unique()))}); assert d.win.nunique() == 2, base.value_counts().head()
d = d[d.Direction.isin([2, 4])].copy()
d['y'] = d.Local_Y * FT * np.where(d.Direction == 2, 1.0, -1.0); d['len'] = d.v_length * FT
d = d.sort_values(['win', 'Vehicle_ID', 'Frame_ID']).drop_duplicates(['win', 'Vehicle_ID', 'Frame_ID'], keep='first')
k = np.arange(-3 * DEL, 3 * DEL + 1); w = np.exp(-np.abs(k) / DEL)


def smooth(y):
    n = len(y); out = np.empty(n)
    for i in range(n):
        lo, hi = max(0, i - 3 * DEL), min(n, i + 3 * DEL + 1); ww = w[(lo - i) + 3 * DEL:(hi - i) + 3 * DEL]
        out[i] = np.dot(ww, y[lo:hi]) / ww.sum()
    return out


ys = np.empty(len(d)); vs = np.empty(len(d)); pos = 0; idx = {}
for (wn, vid), g in d.groupby(['win', 'Vehicle_ID'], sort=False):
    y = smooth(g.y.to_numpy()); fr = g.Frame_ID.to_numpy()
    v = np.empty_like(y); v[:-1] = np.diff(y) / (np.diff(fr) * 0.1); v[-1] = v[-2] if len(v) > 1 else 0.0
    ys[pos:pos + len(g)] = y; vs[pos:pos + len(g)] = v; pos += len(g)
d['ys'] = ys; d['vs'] = vs
lut = {(r.win, r.Vehicle_ID, r.Frame_ID): (r.ys, r.vs, r.len, r.Lane_ID, r.Movement) for r in d.itertuples(index=False)}
pairs = []; drop = dict(short=0, gap=0, stop=0)
for (wn, vid), g in d[(d.Movement == 1) & (d.Preceding > 0)].groupby(['win', 'Vehicle_ID'], sort=False):
    rows = []
    for r in g.itertuples(index=False):
        L = lut.get((wn, r.Preceding, r.Frame_ID))
        ok = L is not None and L[4] == 1 and L[3] == r.Lane_ID
        rows.append((r.Frame_ID, r.Preceding, r.ys, r.vs, (L[0] - L[2] - r.ys) if ok else np.nan, L[0] if ok else np.nan, L[1] if ok else np.nan, L[2] if ok else np.nan, r.len) if ok else None)
    seg = []
    def flush(seg):
        for s0 in range(0, len(seg) - 149, 300):
            S = seg[s0:s0 + 300]
            if len(S) < 150:
                drop['short'] += 1; continue
            gap = np.array([x[4] for x in S]); vf = np.array([x[3] for x in S])
            if not (np.all(gap > 0) and np.all(gap < 80)):
                drop['gap'] += 1; continue
            if np.any((vf < 1.0) & (gap > 25)):
                drop['stop'] += 1; continue
            pairs.append(dict(key=f'{wn}:{vid}:{S[0][0]}', fol=f'{wn}:{vid}', lead=int(S[0][1]), yf=[x[2] for x in S], vf=list(vf), gap=list(gap),
                              yl=[x[5] for x in S], vl=[x[6] for x in S], ll=S[0][7], lf=S[0][8]))
    for x in rows:
        if x is None or (seg and (x[0] != seg[-1][0] + 1 or x[1] != seg[-1][1])):
            flush(seg); seg = []
        if x is not None:
            seg.append(x)
    flush(seg)
split = {p['key']: ('test' if int(hashlib.sha1(p['fol'].encode()).hexdigest(), 16) % 10 >= 6 else 'train') for p in pairs}
free = []
for (wn, vid), g in d[d.Movement == 1].groupby(['win', 'Vehicle_ID'], sort=False):
    v = g.vs.to_numpy(); y = g.ys.to_numpy(); fr = g.Frame_ID.to_numpy(); pre = g.Preceding.to_numpy()
    stops, armed, last8 = [], False, -1
    for t in range(len(v)):                                          # hysteresis: an approach starts above 8 m/s, ends below 0.5 m/s
        if v[t] >= 8.0:
            armed, last8 = True, t
        elif armed and v[t] < 0.5 and t + 10 < len(v) and np.all(v[t:t + 10] < 0.5) and t - last8 <= 300:
            stops.append((last8, t)); armed = False
    for j, s in stops:
        lead_close = False
        for t in range(j, s + 1):
            if pre[t] > 0:
                L = lut.get((wn, pre[t], fr[t]))
                if L is not None and L[0] - y[t] < 80:
                    lead_close = True; break
        if lead_close:
            continue
        lo = max(0, s - 300); free.append(dict(key=f'{wn}:{vid}:{fr[s]}', v=[float(x) for x in v[lo:s + 11]], x=[float(x) for x in y[lo:s + 11]]))
np.savez_compressed(OUT / 'f4_pairs.npz', pairs=np.array(pairs, dtype=object), split=np.array([split[p['key']] for p in pairs]), free=np.array(free, dtype=object))
summ = dict(n_pairs=len(pairs), train=sum(1 for p in pairs if split[p['key']] == 'train'), test=sum(1 for p in pairs if split[p['key']] == 'test'),
            followers=len({p['fol'] for p in pairs}), drop=drop, n_free=len(free), mean_len_s=float(np.mean([len(p['gap']) for p in pairs]) * 0.1),
            raw_vs_smooth_speed_rmse=float(np.sqrt(np.nanmean((d.vs - d.v_Vel * FT) ** 2))))
(OUT / 'f4_pairs_summary.json').write_text(json.dumps(summ, indent=1)); print(json.dumps(summ, indent=1))
