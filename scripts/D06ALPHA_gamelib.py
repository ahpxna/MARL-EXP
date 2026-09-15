"""D06ALPHA shared library: exact rational D6 reference-construction objects
and an exact rational matrix-game (minimax) solver.

Every closed form here is transcribed from the Lean corpus, NOT assumed:

  I n            = Fin (n+1)                 [LeanD6ThresholdConstructionV1:13]
  others A j     = (univ \\ A).erase j        [LeanD6ThresholdConstructionV1:24]
  positiveGround = univ.erase j, card 2q+1   [LeanD6ThresholdConstructionV1:454]
  worlds q j     = positiveGround.powersetCard (q+1)
  tailFactor t B = (1-t)^|B| + |B| t (1-t)^(|B|-1)   [ResponseJoinV1:63]
  gateMass t A j = (1-t)^|A| * tailFactor t (others A j)              [:68]
  slopeBval      = (|B|-1) t (1-t)^(|A|+|B|-1)      [CenteredCompensatedV1:70]
  upperCount, countLoss                             [FullCountLossV1:37,41]
  countMinimum  = min over u<=|T∩A|, v<=|T∩B| of countLoss  [LegalCountMinimumV1:69]
  regret M A S  = actualLoss - legalMinimum         [EndpointWorldsV1:41]
  phaseValueFull k p c e r
        = max(0, k r - e) * (p (k-1) + max(0, e-r)) / (4 (c (k-1)))   [PhaseValueV1:154]

With |A| = k = q+1 and |others A j| = k-1 = q this gives exactly the package's
closed forms:  b=(q-1)t(1-t)^(2q), a=(1-t)^(2q+1)+q t(1-t)^(2q), c=a-b=(1-t)^(2q).
"""

from fractions import Fraction as F
from itertools import combinations
from math import comb


# ---------------------------------------------------------------- parameters

def slopes(k, t):
    """(a, b, c) at |A| = k, |others A j| = k-1, reference t. Exact in Fraction."""
    nA, nB = k, k - 1
    one_t = 1 - t
    tail = one_t ** nB + nB * t * (one_t ** (nB - 1))
    a = (one_t ** nA) * tail
    b = (nB - 1) * t * (one_t ** (nA + nB - 1))
    return a, b, a - b


def region_scalars(k, t, rho):
    a, b, c = slopes(k, t)
    p = rho - 2 * b
    r = 2 * a - rho
    e = min(a, 2 * b)
    return dict(a=a, b=b, c=c, p=p, r=r, e=e, k=k)


def phase_value_full(k, p, c, e, r):
    """PhaseValueV1.phaseValueFull, verbatim."""
    kk = F(k) if not isinstance(k, F) else k
    num = max(0 * r, kk * r - e) * (p * (kk - 1) + max(0 * e, e - r))
    den = 4 * (c * (kk - 1))
    return num / den


# ------------------------------------------------------------- the count loss

def upper_count(a, b, rho, u, v):
    corr = min(a, 2 * b) if (u == 0 and v == 0) else (b if (u == 0 and v == 1) else 0 * a)
    return 1 + (rho - a) * u + (rho - b) * v - corr


def count_loss(a, b, rho, na, nb, u, v):
    """FullCountLossV1.countLoss. This IS the actual retained loss
    (actual_full_count_loss, PROVED, needs only 0<=t<=1, rho>=1, |B|>=2)."""
    up = upper_count(a, b, rho, u, v)
    low1 = (1 - a) - a * (na - u) - b * (nb - v)
    low2 = -b if v < nb else 0 * b
    return (up - min(low1, low2)) / 2


def legal_minimum(a, b, rho, k, h):
    """countMinimum for a world with |T∩A| = h (so |T∩others A j| = k-h).
    = legalMinimum by actual_legal_minimum_eq_count_minimum (PROVED)."""
    na, nb = k, k - 1
    best = None
    for u in range(h + 1):
        for v in range(k - h + 1):
            val = count_loss(a, b, rho, na, nb, u, v)
            if best is None or val < best:
                best = val
    return best


# --------------------------------------------------- reduced symmetric game
# Symmetry group Sym(T) x Sym(positiveGround \ T) fixes j, acts on worlds A
# (orbit invariant: h = |T∩A|, range 1..k) and on decisions D ⊆ T (orbit
# invariant: d = |D|, range 0..k). Symmetrising a MINIMISER's strategy never
# hurts, so the reduced game has the same value.  (Verified against the full
# unreduced game in D06ALPHA_full_vs_reduced.py.)

def reduced_payoff_matrix(k, t, rho):
    """rows h=1..k (worlds), cols d=0..k (decisions). Entry = expected regret."""
    a, b, c = slopes(k, t)
    na, nb = k, k - 1
    lmin = {h: legal_minimum(a, b, rho, k, h) for h in range(1, k + 1)}
    M = []
    for h in range(1, k + 1):
        row = []
        for d in range(0, k + 1):
            tot = F(0) if isinstance(a, F) else 0.0
            denom = comb(k, d)
            for m in range(max(0, d - (k - h)), min(d, h) + 1):
                w = F(comb(h, m) * comb(k - h, d - m), denom)
                tot += w * count_loss(a, b, rho, na, nb, m, d - m)
            row.append(tot - lmin[h])
        M.append(row)
    return M


# ---------------------------------------------------- exact simplex + game

def _simplex_max(A, bvec, cvec):
    """max c^T x  s.t.  A x <= b (b >= 0), x >= 0.  Exact Fractions, Bland's rule.
    Returns (objective, x)."""
    m, n = len(A), len(A[0])
    tab = [[F(A[i][j]) for j in range(n)] + [F(1) if s == i else F(0) for s in range(m)]
           + [F(bvec[i])] for i in range(m)]
    obj = [-F(cvec[j]) for j in range(n)] + [F(0)] * m + [F(0)]
    basis = [n + i for i in range(m)]
    it = 0
    while True:
        it += 1
        if it > 200000:
            raise RuntimeError("simplex did not terminate")
        enter = -1
        for j in range(n + m):
            if obj[j] < 0:
                enter = j
                break
        if enter < 0:
            break
        leave, best = -1, None
        for i in range(m):
            if tab[i][enter] > 0:
                ratio = tab[i][-1] / tab[i][enter]
                if best is None or ratio < best or (ratio == best and basis[i] < basis[leave]):
                    best, leave = ratio, i
        if leave < 0:
            raise RuntimeError("unbounded LP")
        piv = tab[leave][enter]
        tab[leave] = [x / piv for x in tab[leave]]
        for i in range(m):
            if i != leave and tab[i][enter] != 0:
                f = tab[i][enter]
                tab[i] = [tab[i][j] - f * tab[leave][j] for j in range(n + m + 1)]
        if obj[enter] != 0:
            f = obj[enter]
            obj = [obj[j] - f * tab[leave][j] for j in range(n + m + 1)]
        basis[leave] = enter
    x = [F(0)] * n
    for i in range(m):
        if basis[i] < n:
            x[basis[i]] = tab[i][-1]
    dual = [obj[n + i] for i in range(m)]   # reduced costs of the slacks = dual optimum
    return obj[-1], x, dual


def solve_game(M):
    """M[i][j]: payoff to the MAXIMISING row player (adversary/world) when the
    MINIMISING column player (learner) plays j.  Returns (value, col_strategy,
    row_strategy) with exact Fractions."""
    nr, nc = len(M), len(M[0])
    lo = min(min(row) for row in M)
    shift = 1 - lo                     # every shifted entry >= 1 > 0
    Mp = [[M[i][j] + shift for j in range(nc)] for i in range(nr)]
    # max sum y  s.t.  sum_i Mp[i][j] y_i <= 1  for every column j
    # Learner (column, MINIMISER) LP, all shifted entries >= 1 > 0:
    #   max sum_j xh_j  s.t.  sum_j Mp[i][j] xh_j <= 1  for every row i,  xh >= 0
    #   value' = 1 / optimum,  x = xh * value'
    # Its dual  min sum_i yh_i  s.t.  sum_i yh_i Mp[i][j] >= 1  gives the
    # adversary's optimum  y = yh * value'.
    obj, xh, yh = _simplex_max(Mp, [F(1)] * nr, [F(1)] * nc)
    vshift = 1 / obj
    value = vshift - shift
    colstrat = [xj * vshift for xj in xh]         # learner mixed strategy
    rowstrat = [yi * vshift for yi in yh]         # adversary mixed strategy
    return value, colstrat, rowstrat


def verify_game(M, value, colstrat, rowstrat, tol=0):
    """Independent certificate check: colstrat guarantees <= value against every
    row, rowstrat guarantees >= value against every column, both are
    distributions.  Returns (ok, worst_row_excess, worst_col_deficit)."""
    nr, nc = len(M), len(M[0])
    ok = True
    ok &= all(x >= 0 for x in colstrat) and sum(colstrat) == 1
    ok &= all(y >= 0 for y in rowstrat) and sum(rowstrat) == 1
    worst_up = max(sum(M[i][j] * colstrat[j] for j in range(nc)) - value for i in range(nr))
    worst_lo = max(value - sum(M[i][j] * rowstrat[i] for i in range(nr)) for j in range(nc))
    ok &= worst_up <= tol and worst_lo <= tol
    return ok, worst_up, worst_lo
