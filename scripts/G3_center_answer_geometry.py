#!/usr/bin/env python3
"""G3: does the CENTRAL answer B = A always win the D6 approximate-answer game?

Model (identical to research/worker_distinct_research_acceptance_20260913/
approximate_game.py, re-derived independently here):
  coords 0..2q, extra coordinate j = 2q+1, true label A = {0..q}, |A| = q+1.
  Answer of shell h: B = (first q+1-h of A) + (h coordinates outside A).
  Legal queries: every scalar coordinate and every (G,h) with j not in G,
  |G| <= q and (h = false -> |G| >= 2).  Unit-variance Gaussians, unit cost.
  mean(label, nu) = offset + slope * nu with
      scalar i: (1,0) if i in label, (-1,1) if i = j, (1,-1) otherwise
      group (G,h): (1-2h+k, -(k-h)) with k = |G \\ label|
  information of alternative (A', nu) on query e = (mean_true - mean_alt)^2 / 2
  (A', nu) is BAD for the answer B iff nu in [0,1] and (2-nu)|A'\\B|/2 > eps.
  J_B(theta,eps) = sup_{w in simplex} inf_{(A',nu) bad} sum_e w_e * info_e.

WHAT THIS DOES NOT ESTABLISH: every number below is floating-point LP output.
"lower" is the exact value of one explicit allocation (a valid LOWER certificate
on J), "upper" is the maximal per-query information of one explicit mixture over
bad alternatives (a valid UPPER certificate on J); both up to LP/float error.
Nothing here is a proof, and nothing here covers q > 5 or non-uniform costs.
"""
import itertools, json, math, sys, time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

ROOT = Path('/Users/phanan/cig-amf-main')
OUT = ROOT / 'research' / 'worker_goi3_center_answer_20260913'
PUBLISHED = ROOT / 'research' / 'worker_distinct_research_acceptance_20260913' / 'approximate_game.json'


class ProbeError(RuntimeError):
    """Raised on any mismatch between prediction and computation."""


# ----------------------------------------------------------------- model ----
def layout(q, shell):
    coords = list(range(2 * q + 1))
    j = 2 * q + 1
    A = frozenset(range(q + 1))
    if not 0 <= shell <= q:
        raise ProbeError(f'shell {shell} outside 0..{q}')
    B = frozenset(list(range(q + 1 - shell)) + list(range(q + 1, q + 1 + shell)))
    if len(B) != len(A):
        raise ProbeError('answer must have the cardinality of the true label')
    if len(A - B) != shell:
        raise ProbeError('shell is |A \\ B| by construction')
    return coords, j, A, B


def affine(label, e, j):
    """(offset, slope) of the query mean as a function of the nuisance."""
    if e[0] == 's':
        i = e[1]
        if i in label:
            return (1.0, 0.0)
        return (-1.0, 1.0) if i == j else (1.0, -1.0)
    k = len(e[1] - label)
    h = int(e[2])
    return (1.0 - 2 * h + k, -(k - h))


def build(q, shell, mu, orbit=True):
    coords, j, A, B = layout(q, shell)
    groups = [sorted(A & B), sorted(A - B), sorted(B - A), sorted(set(coords) - (A | B))]
    queries = [('s', i) for i in coords + [j]]
    queries += [('g', frozenset(G), h)
                for r in range(q + 1)
                for G in itertools.combinations(coords, r)
                for h in (False, True) if h or r >= 2]

    def key(e):
        if e[0] == 's':
            if e[1] == j:
                return ('s', 4)
            return ('s', next(i for i, g in enumerate(groups) if e[1] in g))
        return ('g', e[2], *(len(e[1] & set(g)) for g in groups))

    if orbit:
        keys = list(dict.fromkeys(key(e) for e in queries))
        index = {k: i for i, k in enumerate(keys)}
        col = np.array([index[key(e)] for e in queries])
    else:
        keys = list(range(len(queries)))
        col = np.arange(len(queries))
    counts = np.bincount(col, minlength=len(keys))

    true = np.array([a + b * mu for a, b in (affine(A, e, j) for e in queries)])
    alts = []
    if orbit:
        # One canonical label per stabilizer orbit of the pair (A,B).
        alt_labels = []
        for nc in itertools.product(*(range(len(g) + 1) for g in groups)):
            if sum(nc) == q + 1:
                alt_labels.append(frozenset(x for g, c in zip(groups, nc) for x in g[:c]))
    else:
        # The unreduced game must contain every label.  Keeping only the
        # canonical orbit representatives here would let a nonsymmetric design
        # exploit the missing permuted alternatives and is not a valid check.
        alt_labels = [frozenset(c) for c in itertools.combinations(coords, q + 1)]
    for alt in alt_labels:
        off, slope = np.array([affine(alt, e, j) for e in queries]).T
        diff = true - off
        coeff = np.array([np.bincount(col, weights=t, minlength=len(keys)) / counts
                          for t in (diff ** 2 / 2, -diff * slope, slope ** 2 / 2)])
        alts.append((alt, len(alt - B), coeff))
    return queries, keys, counts, alts


def solve(q, shell, mu, eps, orbit=True, tol=2e-8, max_iter=200):
    if not (isinstance(q, int) and q >= 2):
        raise ProbeError('q must be an integer >= 2')
    if not (0.0 <= mu <= 1.0):
        raise ProbeError('mu must lie in [0,1]')
    if not (0.0 <= eps < q):
        raise ProbeError('epsilon must lie in [0,q)')
    if (2 - mu) * shell / 2 > eps + 1e-12:
        raise ProbeError(f'shell {shell} is not epsilon-good at mu={mu}, eps={eps}')
    queries, keys, counts, alts = build(q, shell, mu, orbit=orbit)
    alts = [(a, d, c, min(1.0, 2 - 2 * eps / d)) for a, d, c in alts if d > eps]
    if not alts:
        raise ProbeError('empty bad set needs extended-real treatment')
    coeff = np.array([x[2] for x in alts])
    upper = np.array([x[3] for x in alts])
    dim = len(keys)

    def rows(nu):
        return coeff[:, 0, :] + nu[:, None] * coeff[:, 1, :] + nu[:, None] ** 2 * coeff[:, 2, :]

    cuts = list(rows(np.zeros(len(alts)))) + list(rows(upper))
    meta = [(i, 0.0) for i in range(len(alts))] + [(i, float(u)) for i, u in enumerate(upper)]
    for iteration in range(max_iter):
        mat = np.array(cuts)
        lp = linprog(np.r_[np.zeros(dim), -1.0], A_ub=np.c_[-mat, np.ones(len(mat))],
                     b_ub=np.zeros(len(mat)), A_eq=np.array([np.r_[np.ones(dim), 0.0]]),
                     b_eq=[1.0], bounds=[(0, None)] * dim + [(None, None)], method='highs',
                     options={'dual_feasibility_tolerance': 1e-9,
                              'primal_feasibility_tolerance': 1e-9})
        if not lp.success:
            raise ProbeError(f'LP failed: {lp.message}')
        w = lp.x[:-1]
        polys = coeff @ w
        nu = np.zeros(len(alts))
        pos = polys[:, 2] > 1e-15
        nu[pos] = np.clip(-polys[pos, 1] / (2 * polys[pos, 2]), 0, upper[pos])
        nu[~pos] = np.where(polys[~pos, 1] < 0, upper[~pos], 0)
        oracle = rows(nu)
        values = oracle @ w
        lower = float(values.min())
        dual = np.maximum(0.0, -lp.ineqlin.marginals)
        if dual.sum() <= 0:
            raise ProbeError('degenerate dual: no mixture over bad alternatives')
        dual = dual / dual.sum()
        ub = float((dual @ mat).max())
        gap = ub - lower
        if gap <= tol:
            break
        violated = np.where(values < ub - tol / 3)[0]
        if not len(violated):
            raise ProbeError('no violated cut although the gap is open')
        for i in violated:
            cuts.append(oracle[i])
            meta.append((int(i), float(nu[i])))
    else:
        raise ProbeError(f'cutting planes did not converge: q={q} shell={shell} '
                         f'mu={mu} eps={eps} gap={gap}')
    support = []
    for row, p in enumerate(dual):
        if p > 1e-10:
            i, u = meta[row]
            a, d, c, up = alts[i]
            support.append({'probability': float(p), 'distance_from_answer': d,
                            'swaps_from_true_label': len(frozenset(range(q + 1)) - a),
                            'same_label_as_truth': bool(a == frozenset(range(q + 1))),
                            'nu': u, 'nu_sup_of_bad_set': float(up),
                            'at_excluded_endpoint': bool(abs(u - up) < 1e-10)})
    return {'q': q, 'mu': mu, 'epsilon': eps, 'answer_shell': shell, 'orbit_reduced': orbit,
            'dimension': dim, 'alternative_orbits': len(alts), 'iterations': iteration + 1,
            'lower': lower, 'upper': ub, 'gap': gap,
            'simplex_residual': float(abs(w.sum() - 1)),
            'min_weight': float(w.min()),
            'dual_support': sorted(support, key=lambda s: -s['probability'])[:6]}


# --------------------------------------------------------------- analysis ---
def same_label_bound(q, mu, eps, h):
    """Upper bound on J_B from the SAME-LABEL alternative (A, nu), nu < mu.

    Valid only when the true label A is itself a bad alternative for B, i.e.
    eps < h.  U = min(1, 2-2eps/h) is the supremum of the bad nuisances and the
    information of (A,nu) is curvature*(mu-nu)^2/2 <= q^2 (mu-U)^2/2.
    """
    if not (0 < h and eps < h):
        return None
    U = min(1.0, 2 - 2 * eps / h)
    if U > mu + 1e-12:
        raise ProbeError('an epsilon-good answer cannot have U > mu')
    return q ** 2 * (mu - U) ** 2 / 2


def good_shells(q, mu, eps):
    return [h for h in range(q + 1) if (2 - mu) * h / 2 <= eps + 1e-12]


def breakpoints(q, mu):
    pts = {0.0}
    for d in range(1, q + 1):
        pts.add((2 - mu) * d / 2)   # shell d becomes epsilon-good
        pts.add(float(d))           # the true label stops being bad for shell d
    return sorted(p for p in pts if p < q)


# ------------------------------------------------------------------ checks --
def check_reproduction(report, tol=1e-6):
    """Independent re-derivation must reproduce the published cells."""
    pub = json.loads(PUBLISHED.read_text())
    if pub.get('status') != 'complete':
        raise ProbeError('published approximate_game.json is not complete')
    checked = []
    for r in pub['results']:
        for cell in r['shells']:
            mine = solve(r['q'], cell['answer_shell'], r['mu'], r['epsilon'])
            dl = abs(mine['lower'] - cell['lower'])
            du = abs(mine['upper'] - cell['upper'])
            if dl > tol or du > tol:
                raise ProbeError(f"reproduction mismatch q={r['q']} shell={cell['answer_shell']} "
                                 f"eps={r['epsilon']}: dlower={dl} dupper={du}")
            checked.append({'q': r['q'], 'mu': r['mu'], 'epsilon': r['epsilon'],
                            'shell': cell['answer_shell'], 'delta_lower': dl, 'delta_upper': du})
    report['reproduction'] = {'cells': len(checked), 'max_delta':
                              max(max(c['delta_lower'], c['delta_upper']) for c in checked),
                              'source': str(PUBLISHED)}
    print(f'reproduction: {len(checked)} published cells matched', flush=True)


def check_orbit_reduction(report, tol=1e-6):
    """Orbit-reduced and full-dimensional games must give the same certificates."""
    trials = [(3, 1, 0.5, 0.8), (3, 0, 0.5, 0.8), (3, 1, 1.0, 1.2), (2, 1, 0.6, 0.9)]
    out = []
    for q, shell, mu, eps in trials:
        a = solve(q, shell, mu, eps, orbit=True)
        b = solve(q, shell, mu, eps, orbit=False)
        d = max(abs(a['lower'] - b['lower']), abs(a['upper'] - b['upper']))
        if d > tol:
            raise ProbeError(f'orbit reduction mismatch at q={q} shell={shell} '
                             f'mu={mu} eps={eps}: {d}')
        out.append({'q': q, 'shell': shell, 'mu': mu, 'epsilon': eps, 'delta': d,
                    'reduced_dimension': a['dimension'], 'full_dimension': b['dimension']})
    report['orbit_reduction'] = out
    print(f'orbit reduction: {len(out)} cells agree with the unreduced game', flush=True)


def check_opening_lemma(report, tol=1e-7):
    """At eps = (2-mu)h/2 with mu > 0 the shell-h answer must have J = 0."""
    out = []
    for q in (2, 3, 4):
        for mu in (0.25, 0.5, 0.75, 1.0):
            for h in range(1, q + 1):
                eps = (2 - mu) * h / 2
                if eps >= q:
                    continue
                cell = solve(q, h, mu, eps)
                if cell['upper'] > tol or cell['lower'] > tol:
                    raise ProbeError(f'opening lemma violated q={q} mu={mu} h={h}: '
                                     f"lower={cell['lower']} upper={cell['upper']}")
                out.append({'q': q, 'mu': mu, 'h': h, 'epsilon': eps,
                            'lower': cell['lower'], 'upper': cell['upper'],
                            'dual_is_same_label': all(s['same_label_as_truth']
                                                      for s in cell['dual_support'])})
    report['opening_lemma'] = out
    print(f'opening lemma: J_B = 0 on {len(out)} boundary cells', flush=True)


def check_mu_zero(report):
    """mu = 0: the argument of the opening lemma must be unavailable."""
    out = []
    for q in (2, 3, 4):
        for h in range(1, q + 1):
            eps = float(h)             # the smallest epsilon that makes shell h good at mu=0
            if eps >= q:
                continue
            if same_label_bound(q, 0.0, eps, h) is not None:
                raise ProbeError('same-label kill must be unavailable at mu=0')
            cell = solve(q, h, 0.0, eps)
            centre = solve(q, 0, 0.0, eps)
            out.append({'q': q, 'h': h, 'epsilon': eps,
                        'shell_lower': cell['lower'], 'shell_upper': cell['upper'],
                        'centre_lower': centre['lower'], 'centre_upper': centre['upper'],
                        'centre_dominates_certified': centre['lower'] >= cell['upper'] - 1e-9})
    report['mu_zero'] = out
    print(f'mu = 0 boundary: {len(out)} cells computed', flush=True)


def check_quantitative_bound(report, slack=1e-9):
    """J_B <= q^2 (mu-U)^2/2 whenever the true label is bad for B (eps < h)."""
    out = []
    for q in (3, 4):
        for mu in (0.25, 0.5, 1.0):
            for h in range(1, q + 1):
                lo = (2 - mu) * h / 2
                for frac in (0.05, 0.35, 0.7, 0.99):
                    eps = lo + frac * (h - lo)
                    if not (lo <= eps < min(h, q)):
                        continue
                    bound = same_label_bound(q, mu, eps, h)
                    cell = solve(q, h, mu, eps)
                    if cell['lower'] > bound + slack + 10 * cell['gap']:
                        raise ProbeError(f'quantitative bound violated q={q} mu={mu} h={h} '
                                         f"eps={eps}: lower={cell['lower']} bound={bound}")
                    out.append({'q': q, 'mu': mu, 'h': h, 'epsilon': eps, 'bound': bound,
                                'lower': cell['lower'], 'upper': cell['upper'],
                                'tightness': cell['lower'] / bound if bound > 0 else None})
    report['quantitative_bound'] = out
    print(f'quantitative same-label bound: {len(out)} cells respected', flush=True)


def dominance_sweep(report):
    """Certificate-sandwiched hunt: is there B != A with lower(B) > upper(A)?"""
    cells, counterexamples, ties = [], [], []
    for q in (2, 3, 4):
        for mu in (0.0, 0.1, 0.25, 1 / 3, 0.5, 0.75, 0.9, 1.0):
            pts = breakpoints(q, mu)
            grid = []
            for a, b in zip(pts, pts[1:] + [float(q)]):
                grid += [a, a + 0.01 * (b - a), a + 0.5 * (b - a), a + 0.99 * (b - a)]
            grid = sorted({round(min(max(e, 0.0), q - 1e-6), 9) for e in grid if e < q})
            for eps in grid:
                shells = good_shells(q, mu, eps)
                if len(shells) < 2:
                    continue
                try:
                    got = {h: solve(q, h, mu, max(eps, (2 - mu) * h / 2)) for h in shells}
                except ProbeError as exc:
                    raise ProbeError(f'sweep failure q={q} mu={mu} eps={eps}: {exc}')
                centre = got[0]
                for h in shells[1:]:
                    rec = {'q': q, 'mu': mu, 'epsilon': eps, 'shell': h,
                           'centre_lower': centre['lower'], 'centre_upper': centre['upper'],
                           'shell_lower': got[h]['lower'], 'shell_upper': got[h]['upper'],
                           'true_label_is_bad_for_shell': eps < h,
                           'margin_lower_shell_minus_upper_centre':
                               got[h]['lower'] - centre['upper']}
                    cells.append(rec)
                    if got[h]['lower'] > centre['upper'] + 1e-9:
                        counterexamples.append(rec)
                    elif got[h]['lower'] > centre['upper'] - 1e-9:
                        ties.append(rec)
    worst = max(cells, key=lambda c: c['margin_lower_shell_minus_upper_centre'])
    report['dominance_sweep'] = {
        'cells': len(cells), 'counterexamples': counterexamples, 'near_ties': ties,
        'worst_margin_cell': worst,
        'max_ratio_shell_over_centre': max(
            c['shell_upper'] / c['centre_lower'] for c in cells if c['centre_lower'] > 0)}
    print(f"dominance sweep: {len(cells)} (answer, cell) pairs, "
          f'{len(counterexamples)} certified counterexamples, '
          f"worst margin {worst['margin_lower_shell_minus_upper_centre']:.6g}", flush=True)
    if counterexamples:
        print('COUNTEREXAMPLE FOUND', json.dumps(counterexamples[0], indent=2), flush=True)
    return counterexamples


def radius_law(report):
    """Combinatorial structure: swap radius from the true label to the bad set."""
    out = []
    for q in (2, 3, 4, 5):
        coords = set(range(2 * q + 1))
        A = frozenset(range(q + 1))
        for h in range(0, q + 1):
            _, _, _, B = layout(q, h)[0], None, None, layout(q, h)[3]
            for eps10 in range(0, 10 * q):
                eps = eps10 / 10
                if (2 - 1.0) * h / 2 > eps:      # not epsilon-good even at mu=1
                    continue
                best = None
                for k in range(0, q + 2):        # k = |A \ A'| swaps
                    found = False
                    for out_set in itertools.combinations(sorted(A), k):
                        for in_set in itertools.combinations(sorted(coords - A), k):
                            alt = (A - set(out_set)) | set(in_set)
                            if len(alt - B) > eps:
                                found = True
                                break
                        if found:
                            break
                    if found:
                        best = k
                        break
                predicted = max(0, math.floor(eps) + 1 - h)
                if best != predicted:
                    raise ProbeError(f'swap radius law broken q={q} h={h} eps={eps}: '
                                     f'{best} != {predicted}')
                out.append({'q': q, 'h': h, 'epsilon': eps, 'swap_radius': best})
    report['swap_radius_law'] = {'checked': len(out),
                                 'law': 'radius(h, eps) = max(0, floor(eps)+1-h)'}
    print(f'swap radius law: verified on {len(out)} (q,h,eps) triples', flush=True)


def main():
    t0 = time.time()
    OUT.mkdir(parents=True, exist_ok=True)
    report = {'generated_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()),
              'model': 'D6 approximate-answer game, all legal queries, unit variance and cost',
              'certificates': 'lower = explicit allocation value, upper = explicit bad mixture',
              'not_established': 'floating point only; no proof; q <= 5; uniform cost'}
    radius_law(report)
    check_reproduction(report)
    check_orbit_reduction(report)
    check_opening_lemma(report)
    check_quantitative_bound(report)
    check_mu_zero(report)
    counter = dominance_sweep(report)
    report['seconds'] = round(time.time() - t0, 1)
    report['verdict'] = ('COUNTEREXAMPLE' if counter else
                         'no certified counterexample in the swept region')
    (OUT / 'center_answer_geometry.json').write_text(json.dumps(report, indent=2) + '\n')
    print('wrote', OUT / 'center_answer_geometry.json', flush=True)
    return 0


if __name__ == '__main__':
    sys.exit(main())
