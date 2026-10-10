#!/usr/bin/env python3
"""F2 (PROTOCOL_FIELD_F2_F3T_F4_20261008 + A2): SUMO emission models against fuel measured on VED ICE vehicles (MAF-based, labelled).
  table   one emissionsDrivingCycle run per class on the (v, a) grid v 0..40 m/s step 0.05, a -6..5 m/s^2 step 0.01 (slope 0) -> f2_tables.npz;
          KF2-1: constant-speed check and 3 real trips, table vs direct run (|rel diff| <= 1 %).
  extract stream the VED weekly CSVs (bsdtar, nothing extracted); ICE vehicles; per trip a 1 Hz grid (speed, MAF, load, trims interpolated
          from their own samples; seconds farther than 3 s from a speed sample are gaps); measured fuel g/s: M0 = MAF/14.7*(1+(STFT+LTFT)/100)
          (upper bound on glide fuel), M1 = M0 with deceleration fuel cut-off masked (a < -0.3, v > 15 km/h, load < 20 %; lower bound);
          model fuel per class from the tables (a = central difference); events (stop, roll, cruise, idle runs) -> f2_events.npz.
          KF2-2: per trip, sum of 1 Hz M0 vs trapezoid integral of M0 over the raw MAF samples (|rel diff| <= 1 % on the median trip).
  report  per-vehicle scale k on cruise, S0 (idle / cruise ratio), S1 (relative error by event class), S2 (roll / stop ratio on matched
          entry-speed bins), S3 (roll - stop fuel per event), vehicle-clustered bootstrap (B 2000) -> f2_report.txt
W_SMOKE=1: one weekly file, the first 5 ICE vehicles with MAF."""
import json, os, subprocess, sys, tempfile
from pathlib import Path
import numpy as np
import pandas as pd
ROOT = Path(__file__).resolve().parents[1]; F = ROOT / 'research/field_data'; OUT = F / 'results'; OUT.mkdir(exist_ok=True)
SM = os.environ.get('W_SMOKE') == '1'; SFX = '_smoke' if SM else ''; BIN = ROOT / 'external_envs/city_runtime/bin'
CLS = ['HBEFA4/PC_petrol_Euro-4', 'PHEMlight5/PC_EU4_G', 'HBEFA4/PC_petrol_Euro-6ab']   # SUMO 1.27.1 ships no PHEMlight5 Euro-6 petrol class
DV, DA = 0.05, 0.01; VG = np.round(np.arange(0, 40.0001, DV), 4); AG = np.round(np.arange(-6, 5.0001, DA), 4)


def edc(rows, cls, tmp):
    t = Path(tmp) / 'tl.csv'; o = Path(tmp) / 'o.csv'
    t.write_text(''.join(f'{i};{v:.4f};{a:.4f}\n' for i, (v, a) in enumerate(rows)))
    subprocess.run([str(BIN / 'emissionsDrivingCycle'), '-t', str(t), '-e', cls, '-o', str(o), '--timeline-file.separator', ';'],
                   check=True, capture_output=True)
    return np.array([float(l.split(';')[9]) for l in o.read_text().splitlines() if l.strip()])     # fuel mg/s


def table():
    tmp = tempfile.mkdtemp(dir=str(OUT)); T = {}
    rows = [(v, a) for v in VG for a in AG]
    for c in CLS:
        T[c] = edc(rows, c, tmp).reshape(len(VG), len(AG)); print('table', c, T[c].shape, flush=True)
    np.savez_compressed(OUT / 'f2_tables.npz', **{c.replace('/', '__'): T[c] for c in CLS}, VG=VG, AG=AG)
    chk = []
    for c in CLS:                                                     # KF2-1 constant speed and a few (v, a) off-grid points
        pts = [(13.89, 0.0), (8.33, 0.0), (0.0, 0.0), (11.11, 0.73), (6.07, -0.21), (17.3, 1.37)]
        d = edc(pts, c, tmp); t = np.array([interp(T[c], v, a) for v, a in pts])
        chk.append((c, [float(x) for x in d], [float(x) for x in t]))
    (OUT / 'f2_kf21_points.json').write_text(json.dumps(chk, indent=1)); print(json.dumps(chk))


def interp(T, v, a):
    v = np.clip(np.asarray(v, float), VG[0], VG[-1]); a = np.clip(np.asarray(a, float), AG[0], AG[-1])
    iv = np.clip(((v - VG[0]) / DV).astype(int), 0, len(VG) - 2); ia = np.clip(((a - AG[0]) / DA).astype(int), 0, len(AG) - 2)
    fv = (v - VG[iv]) / DV; fa = (a - AG[ia]) / DA
    return (T[iv, ia] * (1 - fv) * (1 - fa) + T[iv + 1, ia] * fv * (1 - fa) + T[iv, ia + 1] * (1 - fv) * fa + T[iv + 1, ia + 1] * fv * fa)


def ice_ids():
    inv = json.loads((F / 'ved_inventory.json').read_text())
    return sorted(int(k) for k, v in inv.items() if v['type'] == 'ICE' and v['maf'] > 0.5 * v['rows'])


def trip_1hz(g):
    ts = g['Timestamp(ms)'].to_numpy() / 1000.0; t0, t1 = ts.min(), ts.max()
    if t1 - t0 < 60:
        return None
    grid = np.arange(np.ceil(t0), np.floor(t1) + 1)
    out = dict(t=grid)
    for k, col in (('v', 'Vehicle Speed[km/h]'), ('maf', 'MAF[g/sec]'), ('load', 'Absolute Load[%]'),
                   ('st', 'Short Term Fuel Trim Bank 1[%]'), ('lt', 'Long Term Fuel Trim Bank 1[%]')):
        m = g[col].notna().to_numpy()
        if m.sum() < 2:
            out[k] = np.full(len(grid), np.nan if k in ('v', 'maf') else 0.0); continue
        tt = ts[m]; yy = g[col].to_numpy()[m]; out[k] = np.interp(grid, tt, yy)
        if k == 'v':
            near = np.abs(tt[np.clip(np.searchsorted(tt, grid), 0, len(tt) - 1)] - grid)
            near = np.minimum(near, np.abs(tt[np.clip(np.searchsorted(tt, grid) - 1, 0, len(tt) - 1)] - grid)); out['gap'] = near > 3.0
    if np.isnan(out['v']).all() or np.isnan(out['maf']).all():
        return None
    v = out['v'] / 3.6; a = np.gradient(v); a[out['gap']] = 0.0
    m0 = out['maf'] / 14.7 * (1 + (np.nan_to_num(out['st']) + np.nan_to_num(out['lt'])) / 100.0)
    m1 = np.where((a < -0.3) & (out['v'] > 15) & (out['load'] < 20), 0.0, m0)
    # KF2-2 raw integral of M0 over the MAF samples
    mm = g['MAF[g/sec]'].notna().to_numpy(); tr = ts[mm]
    st = np.interp(tr, grid, np.nan_to_num(out['st'])); lt = np.interp(tr, grid, np.nan_to_num(out['lt']))
    raw = float(np.trapz(g['MAF[g/sec]'].to_numpy()[mm] / 14.7 * (1 + (st + lt) / 100.0), tr)) if mm.sum() > 1 else np.nan
    return dict(v=v, a=a, m0=m0, m1=m1, gap=out['gap'], raw=raw)


def events(tr, mod):
    v = tr['v']; a = tr['a']; gap = tr['gap']; n = len(v); E = []
    kmh = v * 3.6; nxt = 0
    for i in range(30, n - 30):
        if i < nxt or gap[i - 30:i + 31].any() or kmh[i] >= 15:
            continue
        lo, hi = max(0, i - 10), min(n, i + 11)
        if kmh[i] > kmh[lo:hi].min() + 1e-9 or (kmh[lo:hi] == kmh[i]).nonzero()[0][0] + lo != i:
            continue
        ent = kmh[i - 30:i].max()
        if ent < 30:
            continue
        cls = 'stop' if kmh[i] < 2 else 'roll'; s = slice(i - 30, i + 31); nxt = i + 31   # one event per approach
        E.append(dict(kind=cls, ent=float(ent), vmin=float(kmh[i]), m0=float(tr['m0'][s].sum()), m1=float(tr['m1'][s].sum()),
                      **{f'p{j}': float(mod[j][s].sum() / 1000.0) for j in range(len(CLS))}))
    i = 0
    while i + 60 <= n:                                                   # cruise windows, non-overlapping
        s = slice(i, i + 60)
        if not gap[s].any() and (kmh[s] >= 30).all() and (kmh[s] <= 70).all() and (np.abs(a[s]) < 0.5).all():
            E.append(dict(kind='cruise', ent=float(kmh[s].mean()), vmin=float(kmh[s].min()), m0=float(tr['m0'][s].sum()), m1=float(tr['m1'][s].sum()),
                          **{f'p{j}': float(mod[j][s].sum() / 1000.0) for j in range(len(CLS))})); i += 60
        else:
            i += 1
    run = 0                                                              # idle runs: v == 0, |a| < 0.1, >= 5 s
    for k in range(n + 1):
        ok = k < n and not gap[k] and kmh[k] < 0.5 and abs(a[k]) < 0.1
        if ok:
            run += 1; continue
        if run >= 5:
            s = slice(k - run, k)
            E.append(dict(kind='idle', ent=0.0, vmin=0.0, m0=float(tr['m0'][s].sum()), m1=float(tr['m1'][s].sum()),
                          **{f'p{j}': float(mod[j][s].sum() / 1000.0) for j in range(len(CLS))}, dur=run))
        run = 0
    return E


def extract():
    Tz = np.load(OUT / 'f2_tables.npz'); T = [Tz[c.replace('/', '__')] for c in CLS]; ids = set(ice_ids())
    if SM:
        ids = set(sorted(ids)[:5])
    rec = []; kf22 = []; nsec = 0; kf21 = []; tmp = tempfile.mkdtemp(dir=str(OUT))
    arcs = sorted((F / 'ved').glob('VED_DynamicData_Part*.7z'))
    for arc in arcs:
        names = [l.split()[-1] for l in subprocess.run(['bsdtar', '-tvf', str(arc)], capture_output=True, text=True).stdout.splitlines()]
        for nm in (names[:1] if SM else names):
            pr = subprocess.Popen(['bsdtar', '-xOf', str(arc), nm], stdout=subprocess.PIPE)
            df = pd.read_csv(pr.stdout, low_memory=False); pr.wait()
            df = df[df.VehId.isin(ids)]
            for (vid, trip), g in df.groupby(['VehId', 'Trip']):
                tr = trip_1hz(g.sort_values('Timestamp(ms)'))
                if tr is None:
                    continue
                v = tr['v']; a = tr['a']; mod = [interp(Tt, v, a) for Tt in T]; nsec += len(v)
                if len(kf21) < 3 and len(v) > 300:                           # KF2-1 on real trips: table vs direct run, same (v, a)
                    for j, c in enumerate(CLS[:2]):
                        dr = edc(list(zip(v, a)), c, tmp); kf21.append((int(vid), int(trip), c, float(mod[j].sum() / dr.sum() - 1)))
                if np.isfinite(tr['raw']) and tr['raw'] > 0:
                    kf22.append(float(tr['m0'].sum() / tr['raw'] - 1))
                for e in events(tr, mod):
                    e.update(veh=int(vid), trip=int(trip)); rec.append(e)
            print('done', nm, len(rec), flush=True)
            if SM:
                break
    np.savez_compressed(OUT / f'f2_events{SFX}.npz', rec=np.array(rec, dtype=object), kf22=np.array(kf22), kf21=np.array(kf21, dtype=object))
    print('KF2-1 real trips (table / direct - 1):', kf21, '->', 'PASS' if all(abs(x[3]) <= 0.01 for x in kf21) else 'FAIL')
    print(f'seconds {nsec}; events {len(rec)}; KF2-2 median rel diff {np.median(kf22):+.4f} (|.| <= 0.01 -> {"PASS" if abs(np.median(kf22)) <= 0.01 else "FAIL"})')


def report():
    Z = np.load(OUT / f'f2_events{SFX}.npz', allow_pickle=True); R = pd.DataFrame(list(Z['rec'])); kf22 = Z['kf22']
    out = [f'== F2 VED (ICE, MAF-based fuel; M0 = no cut-off mask, upper bound on glide fuel; M1 = masked, lower bound) vs SUMO 1.27.1 tables',
           f'events: ' + ', '.join(f'{k} {v}' for k, v in R.kind.value_counts().items()) + f'; vehicles {R.veh.nunique()}; '
           f'KF2-2 median rel diff {np.median(kf22):+.4f} ({"PASS" if abs(np.median(kf22)) <= 0.01 else "FAIL"})']
    cru = R[R.kind == 'cruise'].groupby('veh')[['m0', 'm1'] + [f'p{j}' for j in range(len(CLS))]].sum()
    cnt = R[R.kind == 'cruise'].groupby('veh').size(); keep = cnt[cnt >= (1 if SM else 5)].index; R = R[R.veh.isin(keep)]; cru = cru.loc[keep]
    out.append(f'vehicles with >= 5 cruise windows: {len(keep)}')
    vehs = np.array(sorted(keep)); rng = np.random.default_rng(2026); B = 200 if SM else 2000
    by = {v: R[R.veh == v] for v in vehs}

    def safe(fn, vs):
        try:
            return fn(vs)
        except ValueError:                                                 # no events of a kind in a resample
            return np.nan

    def stat(fn):
        obs = safe(fn, vehs); bs = [safe(fn, rng.choice(vehs, len(vehs))) for _ in range(B)]
        lo, hi = np.nanpercentile(bs, [2.5, 97.5]) if np.isfinite(bs).any() else (np.nan, np.nan); return obs, lo, hi

    for mv in ('m0', 'm1'):
        out.append(f'-- measurement {mv.upper()}')
        for j, c in enumerate(CLS):
            k = cru[mv] / cru[f'p{j}']
            # S0 idle / cruise ratio, per vehicle log(measured ratio / model ratio)
            def s0(vs, j=j, mv=mv):
                L = []
                for v in vs:
                    g = by[v]; idl = g[g.kind == 'idle']; cr = g[g.kind == 'cruise']
                    if len(idl) == 0 or len(cr) == 0:
                        continue
                    mr = (idl[mv].sum() / idl.dur.sum()) / (cr[mv].sum() / (60 * len(cr))); pr_ = (idl[f'p{j}'].sum() / idl.dur.sum()) / (cr[f'p{j}'].sum() / (60 * len(cr)))
                    L.append(np.log(mr / pr_))
                return float(np.median(L)) if L else np.nan
            o, lo, hi = stat(s0)
            line = f'{c}: S0 idle/cruise log(meas/model) median {o:+.3f} [{lo:+.3f}, {hi:+.3f}] (x{np.exp(o):.2f})'
            for kind in ('stop', 'roll'):                               # S1 relative error with per-vehicle cruise scale
                def s1(vs, j=j, mv=mv, kind=kind):
                    x = pd.concat([by[v][by[v].kind == kind].assign(k=float(cru.loc[v, mv] / cru.loc[v, f'p{j}'])) for v in vs])
                    return float(((x.k * x[f'p{j}'] - x[mv]) / x[mv]).median()) if len(x) else np.nan
                o, lo, hi = stat(s1); line += f' | S1 {kind} rel.err median {o:+.3f} [{lo:+.3f}, {hi:+.3f}]'
            out.append(line)
        for j, c in enumerate(CLS):                                      # S2 roll / stop ratio on matched entry-speed bins; S3 difference
            def s2(vs, j=j, mv=mv, col=None):
                x = pd.concat([by[v][by[v].kind.isin(['roll', 'stop'])].assign(k=float(cru.loc[v, mv] / cru.loc[v, f'p{j}'])) for v in vs])
                x = x.assign(b=(x.ent // 5).astype(int)); rr = []
                for b, gb in x.groupby('b'):
                    r_, s_ = gb[gb.kind == 'roll'], gb[gb.kind == 'stop']
                    if len(r_) >= 5 and len(s_) >= 5:
                        val = (r_[col].mean() / s_[col].mean()) if col is not None else ((r_.k * r_[f'p{j}']).mean() / (s_.k * s_[f'p{j}']).mean())
                        rr.append((val, min(len(r_), len(s_))))
                return float(np.average([r for r, _ in rr], weights=[w for _, w in rr])) if rr else np.nan
            om, lom, him = stat(lambda vs, j=j, mv=mv: s2(vs, j, mv, col=mv)); op, lop, hip = stat(lambda vs, j=j, mv=mv: s2(vs, j, mv))
            od, lod, hid = stat(lambda vs, j=j, mv=mv: s2(vs, j, mv, col=mv) - s2(vs, j, mv))
            out.append(f'{c}: S2 roll/stop fuel ratio measured {om:.3f} [{lom:.3f}, {him:.3f}] vs model {op:.3f} [{lop:.3f}, {hip:.3f}]; '
                       f'measured - model {od:+.3f} [{lod:+.3f}, {hid:+.3f}]')
        for (a_, b_) in ((0, 1), (2, 1)):                                # which class is closer on S2 (HBEFA4 vs PHEMlight5, same Euro level)
            def dd(vs, a_=a_, b_=b_, mv=mv):
                return abs(s2(vs, a_, mv, col=mv) - s2(vs, a_, mv)) - abs(s2(vs, b_, mv, col=mv) - s2(vs, b_, mv))
            o, lo, hi = stat(dd)
            out.append(f'S2 |meas - {CLS[a_]}| - |meas - {CLS[b_]}| = {o:+.3f} [{lo:+.3f}, {hi:+.3f}] -> '
                       f'{CLS[b_] + " closer" if lo > 0 else (CLS[a_] + " closer" if hi < 0 else "no difference detected")}')
    (OUT / f'f2_report{SFX}.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    {'table': table, 'extract': extract, 'report': report}[sys.argv[1]]()
