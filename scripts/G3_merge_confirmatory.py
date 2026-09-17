#!/usr/bin/env python3
"""G3 confirmatory analysis: exactly the endpoint sealed in the preregistration.

Primary endpoint, and only the primary endpoint, carries alpha.  Secondary
quantities are reported with the same interval and are explicitly labelled; no
secondary result may be promoted.  C_extrema_oracle is a diagnostic: it sees the
truth, so it is neither a ceiling nor a baseline and never enters a comparison.
"""
import argparse, json, hashlib
from pathlib import Path
import numpy as np

PRE = Path('research/G3_prereg_20260915/preregistration.json')
SEEDS = (811, 821, 823, 827, 829, 839, 853, 857, 859, 863)
H = 131072
RESAMPLES, ALPHA = 4000, 0.05
PRIMARY = ('C_lucb', 'uniform')
SECOND_DEPLOY = ('C_anytime',)
DIAGNOSTIC = ('C_extrema_oracle',)


def restricted(rows):
    """Restricted N_certificate truncated at H, keyed by (seed, instance_id)."""
    out = {}
    for x in rows:
        out[(x['seed'], x['instance_id'])] = (
            min(float(x['censored_N_certificate']), float(H)),
            bool(x['certificate_emitted']),
            x['false_safe'])
    return out


def boot(diff, rng):
    n = len(diff)
    idx = rng.integers(0, n, size=(RESAMPLES, n))
    means = diff[idx].mean(axis=1)
    lo, hi = np.percentile(means, [100*ALPHA/2, 100*(1-ALPHA/2)])
    return float(lo), float(hi), means


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--per-seed', default='research/G3_confirmatory_20260915/per_seed')
    ap.add_argument('--out', default='research/G3_confirmatory_20260915/G3_result.json')
    a = ap.parse_args()
    out = Path(a.out)
    if out.exists():
        raise SystemExit(f'Refusing to overwrite {out}')

    per = {}
    for s in SEEDS:
        p = Path(a.per_seed) / f'seed_{s}.json'
        if not p.exists():
            raise SystemExit(f'missing {p}: the panel is incomplete, refusing to analyse')
        per[s] = json.loads(p.read_text())

    # The reported comparator set is the SEALED one, not whatever the runner emitted.
    # The runner produces eight variants; four of them (C_split, C_pilot, C_shrink,
    # C_known_sigma) appear nowhere in the preregistration, and reporting them here
    # would put unregistered comparative quantities in a confirmatory artifact.
    variants = list(PRIMARY) + list(SECOND_DEPLOY) + list(DIAGNOSTIC)
    emitted_by_runner = sorted({v for d in per.values() for v in d['runs_by_variant']})
    dropped = [v for v in emitted_by_runner if v not in variants]
    tab, emitted, falsesafe = {}, {}, {}
    for v in variants:
        rows = [r for s in SEEDS for r in per[s]['runs_by_variant'][v]]
        m = restricted(rows)
        tab[v] = m
        emitted[v] = float(np.mean([e for _, e, _ in m.values()]))
        fs = [f for _, e, f in m.values() if e and f is not None]
        falsesafe[v] = float(np.mean(fs)) if fs else None

    units = sorted(set.intersection(*(set(tab[v]) for v in variants)))
    if len(units) != 1000 * len(SEEDS):
        raise SystemExit(f'expected {1000*len(SEEDS)} paired units, got {len(units)}')
    rng = np.random.default_rng(np.random.SeedSequence([20260915, 3]))

    lucb = np.array([tab[PRIMARY[0]][u][0] for u in units])
    unif = np.array([tab[PRIMARY[1]][u][0] for u in units])
    diff = lucb - unif
    lo, hi, _ = boot(diff, rng)
    point = float(diff.mean())
    result = {
        'gate': 'G3', 'kind': 'confirmatory_result',
        'preregistration_sha256': hashlib.sha256(PRE.read_bytes()).hexdigest(),
        'registration_utc': '2026-09-15T20:00:17Z',
        'launch_receipt': 'research/G3_confirmatory_20260915/launch_receipt.json',
        'paired_units': len(units), 'seeds': list(SEEDS), 'horizon_H': H,
        'comparators_reported': variants,
        'variants_emitted_by_runner_but_not_sealed': dropped,
        'why_dropped': 'These carry no registration; reporting them would place '
                       'unregistered comparative quantities in a confirmatory artifact.',
        'PRIMARY': {
            'estimand': 'paired mean of (C_lucb - Uniform) restricted N_certificate at H',
            'point_estimate': point,
            'ci_percentile_bootstrap': [lo, hi],
            'resamples': RESAMPLES, 'alpha': ALPHA, 'sided': 'two-sided',
            'hypothesis': 'C_lucb certifies at strictly lower restricted mean cost',
            'directional_conclusion': (
                'SUPPORTED: C_lucb strictly cheaper' if hi < 0 else
                'CONTRADICTED: C_lucb strictly more expensive' if lo > 0 else
                'NOT SUPPORTED: interval contains zero'),
            'restricted_mean_C_lucb': float(lucb.mean()),
            'restricted_mean_uniform': float(unif.mean()),
        },
        'SECONDARY_no_alpha_spent': {
            'certificate_fraction': emitted,
            'false_safe_rate_among_emitted': falsesafe,
            'censored_fraction': {v: 1.0 - emitted[v] for v in variants},
            'warning': 'Secondary. No alpha is spent here and none of these may be '
                       'promoted to a primary claim after the fact.',
        },
        'DIAGNOSTIC_not_a_baseline': {
            v: {'restricted_mean': float(np.mean([tab[v][u][0] for u in units])),
                'certificate_fraction': emitted[v]} for v in DIAGNOSTIC if v in tab},
        'additional_deployable_reported_not_tested': {
            v: {'restricted_mean': float(np.mean([tab[v][u][0] for u in units])),
                'certificate_fraction': emitted[v]} for v in SECOND_DEPLOY if v in tab},
        'world_audit': {str(s): per[s]['world_audit'] for s in SEEDS},
        'runner_label_is_wrong_here': {
            'runner_says': {str(s): per[s]['admissibility']['class'] for s in SEEDS},
            'why': "The runner's FROZEN_CONFIRMATORY_SEEDS belongs to "
                   'config/ieee_benchmark_protocol_v1.json (701..769), a different '
                   'protocol. G3 sealed a fresh seed set. Confirmatory status for '
                   'THIS run rests on the sealed preregistration and the launch '
                   'receipt, not on the runner field.'},
        'not_established': [
            'This tests ONE endpoint on ONE panel; it is not a general claim about '
            'C_lucb.',
            'The bootstrap interval is a percentile interval over instances, not an '
            'exact test.',
            'Nothing here bears on the group-range Functional theory (F5); the panel '
            'is a simulation with Gaussian reads.'],
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open('x') as f:
        json.dump(result, f, indent=1)
    p = result['PRIMARY']
    print(f"paired units : {len(units)}")
    print(f"C_lucb  mean : {p['restricted_mean_C_lucb']:.1f}")
    print(f"uniform mean : {p['restricted_mean_uniform']:.1f}")
    print(f"difference   : {point:.2f}  CI95 [{lo:.2f}, {hi:.2f}]")
    print(f"PRIMARY      : {p['directional_conclusion']}")
    print(f"artifact     : {out}")


if __name__ == '__main__':
    main()
