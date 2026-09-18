"""MASTER: regenerate the 32-cell design table from the proved constraint.

The table in the paper matched the closed form multiplied by four, on all
thirty-two cells and to five digits.  Two readings reproduce that exactly and
the table alone cannot separate them: the sweep ran at $v=\\nu=4$ with the
grid's stated $\\Delta=1$, or it ran at $v=\\nu=1$ with an effective separation
of $\\Delta/2$.  Since the script that produced it is not in the repository,
the ambiguity cannot be resolved by reading; it can only be removed by
regenerating the table from a stated convention.

That convention is the one the Lean theorem uses, transcribed here rather than
paraphrased.  `calibration_rate_upper` carries

    (hbudget : sum_g (sm^2 x_g + sk^2 z_g) <= 1)
    (hinfo   : forall g, 2 V / D^2 * (x_g + z_g) <= x_g * z_g)
    |- V <= D^2 / (2 K (sm + sk)^2)

so x and z are PRECISIONS, the price of a unit of precision is sm^2 = v*m and
sk^2 = nu*kappa, and a group's information is the harmonic x z / (x + z).  The
grid below fixes v = nu = 1 and Delta = 1 and says so, which makes the printed
law, the table and the Lean statement the same object.

Three things are computed per cell and two of them are checks, not results: the
closed form; an independent optimiser that is given only the budget and the
information constraint; and the uniform design that keeps every calibration
query but splits each group's budget evenly.

Self-check: the optimiser must not beat the closed form anywhere, and the
uniform design's share of the optimum must equal (sqrt m + sqrt kappa)^2 /
(2 (m + kappa)) -- a ratio in which the noise levels cancel, so it is the one
column the old table already had right. The sweep is not reported otherwise.
"""
import argparse
import json
import math
import os
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.optimize import minimize_scalar

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import EXP_provenance as _P

KS = [1, 2, 4, 8]
MS = [2, 4]
KAPS = [Fraction(1, 4), Fraction(2, 3), Fraction(1), Fraction(4)]
DELTA = 1.0
V_NOISE = 1.0      # ordinary-observation variance, declared
NU_NOISE = 1.0     # calibration-observation variance, declared


def prices(m, kap):
    """(s_m, s_kappa): the square roots of the per-unit precision prices."""
    return math.sqrt(V_NOISE * m), math.sqrt(NU_NOISE * kap)


def closed_form(K, m, kap, D=DELTA):
    sm, sk = prices(m, kap)
    return D * D / (2.0 * K * (sm + sk) ** 2)


def uniform_value(K, m, kap, D=DELTA):
    """Every group keeps a calibration query; each group splits its budget evenly."""
    sm, sk = prices(m, kap)
    x = 1.0 / (2 * K * sm ** 2)
    z = 1.0 / (2 * K * sk ** 2)
    h = x * z / (x + z)
    return D * D * h / 2.0


def optimiser_value(K, m, kap, D=DELTA):
    """Largest V a search reaches that is given the constraints, not the answer.

    Independent of the closed form in the way that matters: the outer step
    bisects on V, and the inner step finds each group's cheapest way to deliver
    the required information by one-dimensional minimisation.  Neither knows the
    optimal split sqrt(m/kappa) nor the price (s_m + s_kappa)^2, which is what
    the cross-check is for.
    """
    sm, sk = prices(m, kap)

    def group_cost(h):
        """Cheapest s_m^2 x + s_k^2 z with the harmonic x z/(x+z) equal to h."""
        if h <= 0:
            return 0.0
        r = minimize_scalar(lambda x: sm ** 2 * x + sk ** 2 * h * x / (x - h),
                            bounds=(h * (1 + 1e-12), h * 1e6), method='bounded',
                            options={'xatol': 1e-15})
        return float(r.fun)

    def spend(V):
        return K * group_cost(2.0 * V / (D * D))

    lo, hi = 0.0, 1.0
    while spend(hi) < 1.0:
        hi *= 2.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if spend(mid) <= 1.0:
            lo = mid
        else:
            hi = mid
    return lo


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--tex', default=None)
    a = ap.parse_args()
    t0 = time.time()

    # ---------------- self-check ----------------------------------------
    worst_ratio, worst_unif = 0.0, 0.0
    for K in KS:
        for m in MS:
            for kap in KAPS:
                kf = float(kap)
                g = closed_form(K, m, kf)
                worst_ratio = max(worst_ratio, optimiser_value(K, m, kf) / g)
                want = (math.sqrt(m) + math.sqrt(kf)) ** 2 / (2 * (m + kf))
                worst_unif = max(worst_unif, abs(uniform_value(K, m, kf) / g - want))
    ok = worst_ratio <= 1 + 1e-6 and worst_unif < 1e-12
    print(f'self-check: optimiser/closed-form at most {worst_ratio:.9f}; '
          f'uniform share matches the noise-free ratio to {worst_unif:.1e} '
          f'-> {"PASS" if ok else "FAIL"}', flush=True)
    if not ok:
        raise SystemExit('self-check failed; table not written')

    rows = []
    for K in KS:
        for m in MS:
            for kap in KAPS:
                kf = float(kap)
                g = closed_form(K, m, kf)
                b = optimiser_value(K, m, kf)
                u = uniform_value(K, m, kf)
                rows.append(dict(K=K, m=m, kappa=str(kap), kappa_float=kf,
                                 gamma_star=g, bisection=b,
                                 gap=abs(b - g) / g, uniform=u,
                                 uniform_pct=100.0 * u / g))

    gaps = [r['gap'] for r in rows]
    pcts = [r['uniform_pct'] for r in rows]
    out = dict(provenance=_P.stamp(__file__), script='EXP_master_cells.py',
               design='32-cell design table regenerated from the constraint the Lean '
                      'theorem carries, with v and nu declared rather than implicit',
               delta=DELTA, v=V_NOISE, nu=NU_NOISE,
               grid=dict(K=KS, m=MS, kappa=[str(k) for k in KAPS]),
               law='Delta^2 / (2 K (sqrt(v m) + sqrt(nu kappa))^2)',
               self_check=dict(worst_optimiser_ratio=worst_ratio,
                               worst_uniform_deviation=worst_unif, passed=bool(ok)),
               cells=len(rows), max_gap=max(gaps),
               uniform_min_pct=min(pcts), uniform_max_pct=max(pcts),
               uniform_median_pct=float(np.median(pcts)),
               rows=rows, wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print(f'wrote {a.out}: {len(rows)} cells, worst gap {max(gaps):.1e}, '
          f'uniform {min(pcts):.1f}-{max(pcts):.1f}% (median {np.median(pcts):.1f}%)')

    if a.tex:
        Path(a.tex).write_text(table_tex(rows, max(gaps), min(pcts)))
        print('wrote', a.tex)


def _fmt_gap(g):
    return '0e+00' if g == 0 else f'{g:.0e}'.replace('e-0', 'e-')


def table_tex(rows, maxgap, minpct):
    KAPTEX = {'1/4': r'$\frac14$', '2/3': r'$\frac23$', '1': '$1$', '4': '$4$'}
    half = len(rows) // 2
    L = [r'\begin{table*}[t]',
         r'\caption{The closed form \eqref{eq:pricelaw} against an independent optimiser, and '
         r'against the uniform baseline, on all 32 parameter cells of the grid '
         r'$K\in\{1,2,4,8\}$, $m\in\{2,4\}$, $\kappa\in\{\frac14,\frac23,1,4\}$ at $\Delta=1$ '
         r'and $v=\nu=1$. Both noise levels are stated because the law is written in the '
         r'noise-weighted prices $s_{m}=\sqrt{vm}$ and $s_{\kappa}=\sqrt{\nu\kappa}$, so a '
         r'table that leaves them implicit does not determine the numbers. The ``gap'' column '
         r'is the relative difference between the closed form and the optimiser; the largest '
         r'anywhere in the sweep is $' + _fmt_gap(maxgap) + r'$, i.e.\ floating-point '
         r'agreement. The last column is the uniform design as a percentage of the optimum, '
         r'which never falls below $' + f'{minpct:.1f}' + r'\%$---in sharp contrast with the '
         r'two control-free baselines, which return exactly zero on every cell. That '
         r'percentage is independent of $v$ and $\nu$, which cancel in the ratio.}',
         r'\label{tab:cells}', r'\centering', r'\footnotesize',
         r'\setlength{\tabcolsep}{4pt}',
         r'\begin{tabular}{@{}rrrrrrrr@{\hspace{10pt}}|@{\hspace{10pt}}rrrrrrrr@{}}',
         r'\toprule',
         r'$K$ & $m$ & $\kappa$ & $\Gamma^{*}$ & optim. & gap & unif. & \% & '
         r'$K$ & $m$ & $\kappa$ & $\Gamma^{*}$ & optim. & gap & unif. & \% \\',
         r'\midrule']
    for a_, b_ in zip(rows[:half], rows[half:]):
        cells = []
        for r in (a_, b_):
            cells += [str(r['K']), str(r['m']), KAPTEX[r['kappa']],
                      f"{r['gamma_star']:.6f}", f"{r['bisection']:.6f}",
                      _fmt_gap(r['gap']), f"{r['uniform']:.6f}",
                      f"{r['uniform_pct']:.1f}"]
        L.append(' & '.join(cells) + r' \\')
    L += [r'\bottomrule', r'\end{tabular}', r'\end{table*}']
    return '\n'.join(L) + '\n'


if __name__ == '__main__':
    main()
