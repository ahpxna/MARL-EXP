"""D06ALPHA control probe: does the SYMMETRY-REDUCED game have the same exact
minimax value as the full unreduced game over all worlds A in `worlds q j` and
all legal decisions?

This exists so that the later large-k results are not resting on an unchecked
symmetrisation step.  Full enumeration: worlds = every (q+1)-subset of
positiveGround (card 2q+1); decisions = every D ⊆ T (every such D is realised by
a legal S with |S| = |T|, because |T^c| = |T| = q+1 -- the `hroom` condition).

Everything exact (fractions.Fraction).  No floating point anywhere.
"""

import sys
from fractions import Fraction as F
from itertools import combinations

sys.path.insert(0, "/Users/phanan/cig-amf-main/scripts")
from D06ALPHA_gamelib import (slopes, legal_minimum, count_loss,
                              reduced_payoff_matrix, solve_game, verify_game)


def full_payoff_matrix(q, t, rho):
    k = q + 1
    n = 2 * q + 2                      # I (2q+1) = Fin (2q+2)
    j = 0
    pg = list(range(1, n))             # positiveGround = univ.erase j, card 2q+1
    T = frozenset(pg[:k])              # any (q+1)-subset; all are equivalent
    a, b, c = slopes(k, t)
    worlds = [frozenset(A) for A in combinations(pg, k)]
    decisions = []
    for d in range(k + 1):
        for D in combinations(sorted(T), d):
            decisions.append(frozenset(D))
    lmin = {h: legal_minimum(a, b, rho, k, h) for h in range(0, k + 1)}
    M = []
    for A in worlds:
        B = frozenset(pg) - A          # others A j = (univ \ A).erase j
        h = len(T & A)
        row = []
        for D in decisions:
            u = len(D & A)
            v = len(D & B)
            row.append(count_loss(a, b, rho, k, k - 1, u, v) - lmin[h])
        M.append(row)
    return M, worlds, decisions


def main():
    grid_t = [F(0), F(1, 100), F(1, 10), F(1, 4), F(1, 3), F(1, 2), F(3, 4), F(9, 10), F(1)]
    grid_rho = [F(1), F(5, 4), F(3, 2), F(7, 4), F(2), F(5, 2), F(4)]
    print("q  t        rho    full_value        reduced_value     agree  cert_ok")
    bad = 0
    for q in (2, 3, 4):
        for t in grid_t:
            for rho in grid_rho:
                Mf, _, _ = full_payoff_matrix(q, t, rho)
                vf, cf, rf = solve_game(Mf)
                okf, _, _ = verify_game(Mf, vf, cf, rf)
                Mr = reduced_payoff_matrix(q + 1, t, rho)
                vr, cr, rr = solve_game(Mr)
                okr, _, _ = verify_game(Mr, vr, cr, rr)
                agree = (vf == vr)
                if not (agree and okf and okr):
                    bad += 1
                print(f"{q}  {str(t):8s} {str(rho):6s} {str(vf):17s} {str(vr):17s} "
                      f"{agree}  {okf and okr}")
    print()
    print(f"mismatches / certificate failures: {bad}")
    print("t grid:", [str(x) for x in grid_t])
    print("rho grid:", [str(x) for x in grid_rho])
    print("NOTE rho > 2 is outside Region.hr2 but actual_full_count_loss still")
    print("     applies (it needs only 0<=t<=1 and rho>=1), so the full-game")
    print("     value is still the true minimax there.")


if __name__ == "__main__":
    main()
