"""G1 (iii) on C0 v3: per-car split of regret under a new light into the Bayes floor of the car's information set on that light
(exact table Z*_L / M*_L, same panel) + excess.  Read-only from research/city_sim/c0_v3_20261002/seed_*/regrets.npz and panels."""
import json
from pathlib import Path
import numpy as np
O = Path('/Users/phanan/cig-amf-main/research/city_sim/c0_v3_20261002')
R = {s: dict(np.load(O / f'seed_{s}' / 'regrets.npz')) for s in range(5)}
topt = {L: float(np.load(O / 'panels' / f'{L}_eval.npz')['topt'].mean()) for L in ['FT', 'ACT', 'EXT', 'CUT', 'A1', 'A2', 'A3', 'A4', 'A5', 'A6']}
# exact tables are seed-independent: check
for k in ['Z*_ACT|EXT|plain', 'Z*_EXT|EXT|plain', 'M*_ACT|CUT|plain']:
    assert all(np.array_equal(R[0][k], R[s][k]) for s in range(1, 5)), k
rng = np.random.default_rng(0)
def boot2(D, B=2000):   # D: seeds x episodes; resample seeds and episodes (the testbed's boot())
    S, E = D.shape; return np.percentile([D[np.ix_(rng.integers(0, S, S), rng.integers(0, E, E))].mean() for _ in range(B)], [2.5, 97.5])
rows = []
print('regret units (cost - privileged per-episode optimum); columns: n seeds | R_f(L) car on L | floor R*(L) | excess E_f(L) [95%] | '
      'of which: specialist approx R(Z_L)-R* | mismatch Delta=R(Z_ACT)-R(Z_L) | exact-frozen table E*=R(Z*_ACT on L)-R* | '
      'upgrade split  dR_f = dFloor + dExcess')
for kind in ('Z', 'M'):
    base_f = {s: R[s][f'{kind}_ACT|ACT|plain'] for s in range(5)}; base_star = R[0][f'{kind}*_ACT|ACT|plain']
    for L in ['FT', 'EXT', 'CUT', 'A1', 'A2', 'A3', 'A4', 'A5', 'A6']:
        S = [s for s in range(5) if f'{kind}_ACT|{L}|plain' in R[s] and f'{kind}_{L}|{L}|plain' in R[s]]
        f = np.array([R[s][f'{kind}_ACT|{L}|plain'] for s in S]); star = R[0][f'{kind}*_{L}|{L}|plain']; sp = np.array([R[s][f'{kind}_{L}|{L}|plain'] for s in S])
        froz = R[0][f'{kind}*_ACT|{L}|plain']
        E = f - star[None]; lo, hi = boot2(E)
        dfloor = star.mean() - base_star.mean(); dexc = E.mean() - np.mean([(base_f[s] - base_star).mean() for s in S]); dtot = f.mean() - np.mean([base_f[s].mean() for s in S])
        per_seed_dexc = [ (f[i].mean() - star.mean()) - (base_f[s].mean() - base_star.mean()) for i, s in enumerate(S)]
        rows.append(dict(kind=kind, L=L, n=len(S), Rf=f.mean(), floor=star.mean(), excess=E.mean(), ci=[lo, hi], spec=(sp - star[None]).mean(), mism=(f - sp).mean(),
                         frozen_table=(froz - star).mean(), dfloor=dfloor, dexc=dexc, dtot=dtot, dexc_seeds=per_seed_dexc, topt=topt[L]))
        print(f'{kind}_ACT -> {L:3s} n={len(S)} | R_f {f.mean():7.2f} | floor {star.mean():6.2f} | excess {E.mean():7.2f} [{lo:6.2f},{hi:6.2f}] | spec {(sp - star[None]).mean():6.2f} | '
              f'mismatch {(f - sp).mean():7.2f} | frozen-table {(froz - star).mean():7.2f} | dR {dtot:+7.2f} = dFloor {dfloor:+6.2f} + dExcess {dexc:+7.2f} (dExcess>0 seeds {sum(v > 0 for v in per_seed_dexc)}/{len(S)})')
print('reference on ACT (trained light): ' + '; '.join(f'{k}_ACT regret {np.mean([R[s][f"{k}_ACT|ACT|plain"].mean() for s in range(5)]):.2f}, floor {R[0][f"{k}*_ACT|ACT|plain"].mean():.2f}' for k in ('Z', 'M')))
print('privileged optimum (mean cost) per panel:', {k: round(v, 2) for k, v in topt.items()})
json.dump(rows, open(Path(__file__).with_suffix('.json'), 'w'), default=float, indent=0)
