#!/usr/bin/env python3
"""F3t (PROTOCOL_FIELD_F2_F3T_F4_20261008): what a deployed SPaT broadcast announces, and how early (Tampa CV Pilot sample).
Units (established from the data before analysis): spat_timestamp = J2735 MinuteOfTheYear; spat_intersections_4 = DSecond (ms within the
minute); minEndTime / maxEndTime = J2735 TimeMark (0.1 s since the start of the hour; 36000 = unknown).  Message time in 0.1 s of the
hour: t = (moy - moy0) * 600 + DSecond / 100, moy0 = the first minute of the hour (all messages are in one hour).
Per (RSU, signal group) the state timeline is rebuilt; a state change is observed when consecutive messages (gap <= 1.0 s) differ in
state; its time is the first message of the new state.  For every message inside a phase whose end is observed, realized remaining
r = t_change - t_msg, announced a = minEndTime - t_msg (next-hour wrap handled).
  T1 share of messages with r >= a - 0.1 s, per state;  T2 r - a quantiles per state;  T3 shares carrying maxEndTime / likelyTime.
  KF3-1 realized yellow durations per (RSU, group): spread (max - min) <= 0.2 s, else reported.
Output research/field_data/results/f3t_tampa.{json,txt}.   W_SMOKE=1: first 5000 messages of one RSU."""
import ast, json, os, sys
from collections import defaultdict
from pathlib import Path
import numpy as np
import pandas as pd
ROOT = Path(__file__).resolve().parents[1]; F = ROOT / 'research/field_data'; OUT = F / 'results'; OUT.mkdir(exist_ok=True)
SM = os.environ.get('W_SMOKE') == '1'
d = pd.read_csv(F / 'tampa_spat/tampa_spat_sample.csv', low_memory=False)
if SM:
    d = d[d.metadata_rsuid == 'thea22'].head(5000)
moy0 = int(d.spat_timestamp.min()); assert int(d.spat_timestamp.max()) - moy0 < 60, 'not one hour'
d['t'] = (d.spat_timestamp.astype(int) - moy0) * 600 + (d.spat_intersections_4.astype(int) // 100)
ev = defaultdict(list); keys = defaultdict(int); n_msg = 0
for r in d.itertuples(index=False):
    try:
        L = ast.literal_eval(r.spat_intersections_2)
    except Exception:
        keys['parse_fail'] += 1; continue
    n_msg += 1
    for m in L:
        me = m['state-time-speed']['MovementEvent']; st = list(me['eventState'])[0]; tm = me.get('timing', {}) or {}
        for k in ('minEndTime', 'maxEndTime', 'likelyTime', 'confidence', 'startTime', 'nextTime'):
            keys[k] += k in tm
        keys['movements'] += 1
        mn = int(tm['minEndTime']) if 'minEndTime' in tm else None; mx = int(tm['maxEndTime']) if 'maxEndTime' in tm else None
        ev[(r.metadata_rsuid, m['signalGroup'])].append((int(r.t), st, mn, mx))
rows, yel = [], defaultdict(list)
for key, L in ev.items():
    L.sort(); i = 0
    # segment into runs of equal state with gaps <= 10 (1.0 s)
    runs = []; cur = [L[0]]
    for a, b in zip(L, L[1:]):
        if b[1] == a[1] and b[0] - a[0] <= 10:
            cur.append(b)
        else:
            runs.append((cur, b if b[0] - a[0] <= 10 and b[1] != a[1] else None)); cur = [b]
    runs.append((cur, None))
    for k, (run, nxt) in enumerate(runs):
        if nxt is None:
            continue                                                   # end not observed (gap or end of data)
        tc = nxt[0]; st = run[0][1]
        prev_ok = k > 0 and runs[k - 1][1] is not None                 # start observed too
        if prev_ok and 'clearance' in st:
            yel[key].append((tc - run[0][0]) / 10.0)
        for (t, s, mn, mx) in run:
            if mn is None or mn >= 36000:
                continue
            a = mn - t
            if a < -18000:
                a += 36000
            rows.append(dict(rsu=key[0], grp=key[1], state=s, r=(tc - t) / 10.0, a=a / 10.0, mx=None if mx is None else (mx - t) / 10.0))
R = pd.DataFrame(rows); out = [f'== F3t Tampa CV Pilot SPaT sample ({len(d)} messages, {n_msg} parsed, RSUs {sorted(d.metadata_rsuid.unique())}, '
                               f'one hour from MinuteOfTheYear {moy0})']
tot = keys['movements']
out.append('T3 timing fields per movement event: ' + ', '.join(f'{k} {keys[k] / max(1, tot):.3f}' for k in ('minEndTime', 'maxEndTime', 'likelyTime',
                                                                                                         'confidence', 'startTime', 'nextTime')))
spread = {f'{k[0]}:{k[1]}': (round(min(v), 1), round(max(v), 1), len(v)) for k, v in yel.items()}
bad = {k: v for k, v in spread.items() if v[1] - v[0] > 0.2}
out.append(f'KF3-1 yellow durations (min, max, n) per RSU:group: {spread}; spread > 0.2 s: {bad if bad else "none"} -> '
           f'{"PASS" if not bad else "REPORTED (not constant)"}')
res = dict(n_messages=len(d), keys={k: v for k, v in keys.items()}, yellow=spread, by_state={})
for st, g in R.groupby('state'):
    diff = g.r - g.a; t1 = float((g.r >= g.a - 0.1).mean())
    q = np.percentile(diff, [5, 25, 50, 75, 90, 95])
    res['by_state'][st] = dict(n=len(g), T1=t1, diff_q=[float(v) for v in q], r_med=float(g.r.median()), a_med=float(g.a.median()),
                               share_a_eq_r=float((diff.abs() <= 0.2).mean()))
    out.append(f'{st}: n {len(g)}; T1 P(realized >= announced minEnd) {t1:.3f}; realized - announced [s] q5 {q[0]:+.1f} q25 {q[1]:+.1f} '
               f'median {q[2]:+.1f} q75 {q[3]:+.1f} q90 {q[4]:+.1f} q95 {q[5]:+.1f}; |diff| <= 0.2 s {res["by_state"][st]["share_a_eq_r"]:.3f}; '
               f'median realized {g.r.median():.1f} s, median announced {g.a.median():.1f} s')
sfx = '_smoke' if SM else ''
(OUT / f'f3t_tampa{sfx}.json').write_text(json.dumps(res, indent=1)); (OUT / f'f3t_tampa{sfx}.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
