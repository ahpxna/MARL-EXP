#!/usr/bin/env python3
"""F1-A1 self-checks (Amendment F1-A1; exit 1 on failure).
  conv    KA-2: the KF-0 convention procedure on the new RL-H:t4..t8 TRAIN traces (f1a1/traces/rlh<t>_s*.npz): the true-duration ttr,
          CORRECTED green-branch ttg and yellow-branch ttg must have error 0 on every observation; negative control: the
          UNcorrected green-branch ttg must be wrong on every observation (C-71), so the check can fail.
  tables  KA-1: light_spec patch (RL-H:0..3 unchanged, RL-H:4..8 -> m3_lights files, sha recorded); KA-3: every open-loop and closed-loop
          table of t4..t8 covers all 16 grid4 lights and was fitted from 8 files.
Writes f1a1_20261004/check/<mode>.txt."""
import hashlib, json, sys
from collections import Counter
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_xplay2 as X2  # noqa: E402
_unpatched = X2.light_spec
import scripts.CITY_f1a1_run as RUN  # noqa: E402
import scripts.CITY_spat_forecast as FC  # noqa: E402
D = ROOT / 'research/city_sim/f1a1_20261004'; NEW = (4, 5, 6, 7, 8); OBS, Y = FC.OBS, FC.YELLOW
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()


def conv(out):
    ok = True
    for t in NEW:
        files = sorted((D / 'traces').glob(f'rlh{t}_s*.npz')); err = dict(ttr=Counter(), ttg_green_corrected=Counter(), ttg_yellow=Counter()); unc = Counter()
        if len(files) != 8:
            out.append(f'KA-2 t{t}: {len(files)} trace files (need 8)'); ok = False; continue
        for f in files:
            z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P, S = z['phases'], z['spent']; G = FC.greens_of(ids)
            for j, tid in enumerate(ids):
                runs = FC.runs(P[:, j]); gs = G[tid]
                for r_i, (ph, st, ln, complete) in enumerate(runs):
                    if not complete or r_i + 2 >= len(runs):
                        continue
                    end_obs = st + ln
                    for i in range(st, st + ln):
                        tt = i + 1; s = float(S[i, j])
                        if ph in gs:
                            err['ttr'][round((ln - s) + OBS - ((end_obs + 1) - tt), 6)] += 1
                            err['ttg_green_corrected'][round((ln - s) + Y + OBS + 1 - ((runs[r_i + 2][1] + 1) - tt), 6)] += 1
                            unc[round((ln - s) + Y + OBS - ((runs[r_i + 2][1] + 1) - tt), 6)] += 1
                        else:
                            err['ttg_yellow'][round((Y - s) + OBS - ((runs[r_i + 1][1] + 1) - tt), 6)] += 1
        for k, c in err.items():
            n = sum(c.values()); z0 = c.get(0.0, 0); good = n > 0 and z0 == n; ok &= good
            out.append(f'KA-2 t{t} {k}: n {n}, error 0 on {z0} ({100 * z0 / max(1, n):.2f} %) -> {"ok" if good else "FAIL"}')
        neg = sum(unc.values()) > 0 and unc.get(0.0, 0) == 0; ok &= neg
        out.append(f'KA-2 t{t} negative control (UNcorrected green ttg must be wrong, C-71): {dict(unc.most_common(2))} -> {"ok" if neg else "FAIL"}')
    return ok


def tables(out):
    ok = True
    for k in (0, 1, 2, 3):
        same = RUN.light_spec(f'RL-H:{k}') == _unpatched(f'RL-H:{k}'); ok &= same; out.append(f'KA-1 RL-H:{k} unchanged: {same}')
    for t in NEW:
        net, ck, mg = X2.light_spec(f'RL-H:{t}'); good = Path(ck).exists() and Path(ck).parent.name == 'm3_lights_20261004' and mg is None; ok &= good
        out.append(f'KA-1 RL-H:{t} -> {ck} sha {sha(ck)[:16] if Path(ck).exists() else None}: {good}')
        for name in (f'm2b/forecast_rlh{t}.json', f'prep/prov_rlh{t}_cl.json'):
            p = D / name
            if not p.exists():
                out.append(f'KA-3 {name}: missing'); ok = False; continue
            T = json.loads(p.read_text()); good = len(T['per']) == 16 and T['n_files'] == 8; ok &= good
            out.append(f'KA-3 {name}: lights {len(T["per"])}, files {T["n_files"]}, sha {sha(p)[:16]} -> {"ok" if good else "FAIL"}')
    return ok


if __name__ == '__main__':
    mode = sys.argv[1]; out = [f'== F1-A1 check {mode}']; ok = conv(out) if mode == 'conv' else tables(out)
    out.append(f'F1-A1 CHECK {mode}: {"PASS" if ok else "FAIL"}'); t = '\n'.join(out) + '\n'; (D / 'check').mkdir(exist_ok=True); (D / 'check' / f'{mode}.txt').write_text(t); print(t)
    sys.exit(0 if ok else 1)
