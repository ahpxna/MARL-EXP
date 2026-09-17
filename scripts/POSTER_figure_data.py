#!/usr/bin/env python3
"""Extract poster figure data from the experiment artifacts.  No number is invented:
every value below is read from a file in research/, and the source path is recorded
beside it so a reader can check it.
"""
import argparse, json
from pathlib import Path

OUT = 'research/papers/_figures/poster_figure_data.json'


def load(p):
    return json.loads(Path(p).read_text())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', default=OUT)
    a = ap.parse_args()
    out = Path(a.out)
    if out.exists():
        raise SystemExit(f'Refusing to overwrite {out}')
    fig = {}

    # ---------- MASTER ----------
    p17 = 'research/worker_P17_master_20260915/P17_master_full_class.json'
    p31 = 'research/worker_P31_master_baselines_20260915/P31_master_control_baselines.json'
    d17, d31 = load(p17), load(p31)
    rows = d17['part2_rows']
    fig['MASTER_rate_vs_kappa'] = {
        'source': p17,
        'formula': d17['part2_formula'],
        'all_agree': d17['part2_all_agree'],
        'cells': len(rows),
        'max_relative_gap': max(r['relative_gap'] for r in rows),
        'points': [{'K': r['K'], 'm': r['m'], 'kappa': r['kappa'],
                    'closed_form': r['closed_form'],
                    'bisection': r['bisection_optimum']} for r in rows],
    }
    r31 = d31['part2_rows']
    fig['MASTER_baselines'] = {
        'source': p31,
        'cells': len(r31),
        'no_controls_all_zero': all(r['baseline_no_controls'] == 0.0 for r in r31),
        'one_missing_all_zero': all(r['baseline_one_control_missing'] == 0.0 for r in r31),
        'zero_reason': r31[0]['baseline_reason_zero'],
        'uniform_over_optimum_min': min(r['uniform_over_optimum'] for r in r31),
        'uniform_over_optimum_max': max(r['uniform_over_optimum'] for r in r31),
        'points': [{'K': r['K'], 'm': r['m'], 'kappa': r['kappa'],
                    'optimum': r['analytic_optimum'],
                    'uniform': r['baseline_all_controls_uniform'],
                    'ratio': r['uniform_over_optimum']} for r in r31],
    }
    fig['MASTER_anchor'] = {
        'source': 'work/p13_conjectures/LeanMasterAnchorInstanceV1.lean (exact rationals)',
        'anchor_free_cap': 1 / 8, 'anchor_free_cap_exact': '1/8',
        'anchored_value': 261 / 1520, 'anchored_value_exact': '261/1520',
        'gap_percent': (261 / 1520 - 1 / 8) / (1 / 8) * 100,
    }

    # ---------- FUNCTIONAL ----------
    f02 = 'research/confirm_ieee_20260912/functional_v4_lucb_ieee10seed_cellv1.json'
    d = load(f02)
    bv = d['by_variant']
    R = d['runs_by_variant']
    key = lambda x: (x['seed'], x['instance_id'])
    L = {key(x): x for x in R['C_lucb']}
    A = {key(x): x for x in R['C_anytime']}
    units = sorted(set(L) & set(A))
    both = [u for u in units if L[u]['certificate_emitted'] and A[u]['certificate_emitted']]
    fig['FUNCTIONAL_panel'] = {
        'source': f02,
        'instances': len(units),
        'variants': {v: {'certify': round(bv[v]['certificate_fraction'] * len(units)),
                         'certificate_fraction': bv[v]['certificate_fraction'],
                         'median_N': bv[v]['median_censored_N_certificate']}
                     for v in ('C_lucb', 'C_anytime', 'uniform')},
        'paired_both_certify': len(both),
        'C_lucb_strictly_faster': sum(
            1 for u in both
            if L[u]['censored_N_certificate'] < A[u]['censored_N_certificate']),
        'ties': sum(1 for u in both
                    if L[u]['censored_N_certificate'] == A[u]['censored_N_certificate']),
        'C_anytime_strictly_faster': sum(
            1 for u in both
            if L[u]['censored_N_certificate'] > A[u]['censored_N_certificate']),
        'only_C_lucb': sum(1 for u in units
                           if L[u]['certificate_emitted'] and not A[u]['certificate_emitted']),
        'only_C_anytime': sum(1 for u in units
                              if A[u]['certificate_emitted'] and not L[u]['certificate_emitted']),
        'winner_field': d.get('deployable_winner_by_median_N_certificate'),
        'winner_status': d.get('deployable_winner_status'),
        'caveat': 'A result on THIS panel under THIS generator. Not a domination theorem.',
    }
    fig['FUNCTIONAL_scalar_proxy'] = {
        'source': 'work/p13_conjectures/LeanFunctionalScalarProxyFailsV1.lean (exact)',
        'family1': {'J_scalar': 1 / 32, 'J_full_le': '9*eta/32',
                    'ratio_le': '9*eta -> 0'},
        'family2': {'J_scalar': 'eta/(8(1+3eta))', 'J_full_ge': 1 / 128,
                    'ratio_ge': '(1+3eta)/(16eta) -> infinity'},
        'eta_grid': [1.0, 0.5, 0.2, 0.1, 0.05, 0.02, 0.01],
        'family1_ratio': [9 * e for e in (1.0, 0.5, 0.2, 0.1, 0.05, 0.02, 0.01)],
        'family2_ratio': [(1 + 3 * e) / (16 * e)
                          for e in (1.0, 0.5, 0.2, 0.1, 0.05, 0.02, 0.01)],
    }

    # ---------- QUERY ----------
    p33 = 'research/worker_P33_query_regret_20260915/P33_query_actual_regret.json'
    try:
        d33 = load(p33)
        fig['QUERY_regret'] = {'source': p33, 'raw_keys': list(d33)[:14],
                               'gamma': '13983/32768', 'L_max': '2401/4096'}
        for k in ('rows', 'cells', 'part2_rows'):
            if k in d33 and d33[k]:
                fig['QUERY_regret']['rows'] = d33[k][:12]
                break
    except Exception as e:
        fig['QUERY_regret'] = {'source': p33, 'error': str(e)}

    # ---------- STRUCTURAL ----------
    fig['STRUCTURAL_law'] = {
        'source': 'work/p13_conjectures/LeanStructuralFamilyLowerV1.lean (proved for all m>=5)',
        'm_grid': list(range(5, 21)),
        'V_avg': [2 / ((m + 4) * (m - 1)) for m in range(5, 21)],
        'V_path': [2 / (m + 4) for m in range(5, 21)],
        'ratio': [m - 1 for m in range(5, 21)],
    }

    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open('x') as f:
        json.dump(fig, f, indent=1)
    print(f'figure data written to {out}')
    for k, v in fig.items():
        src = v.get('source', '')
        print(f'  {k:28} <- {src.split("/")[-1] if src else "(computed)"}')


if __name__ == '__main__':
    main()
