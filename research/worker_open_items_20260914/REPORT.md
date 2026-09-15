# The open items, closed or advanced.

## 1. MASTER — the exact threshold. CLOSED.

`work/p13_conjectures/LeanMasterAnchorCertificateV1.lean`, **14 audits, 0
nonstandard, accepted**.

The previous version left a band of prices where neither direction fired. The
band is gone, and the reason is structural: the gain factors as

    gain(x0) = x0 * gfac / (2 K A),      gfac AFFINE in t = c0 x0,

with endpoints `g0 = c0 K (M^2 - 2 D K) + M^2/sig0` at `t = 0` and
`g1 = (M^2 - 2 D K)/sig0` at `t = 1`. **An affine function on `[0,1]` is
non-positive as soon as both endpoints are** — so there is no escape at small
`x0` and none at large `x0`, and the one-sided argument becomes two-sided with no
extra work.

Verified exactly on 400 random rationals before formalising: both the
factorisation and the affine identity, zero mismatches.

With `M^2 < 2 D K` the critical price is

    c0* = M^2 / (sig0 * K * (2 D K - M^2))

and `anchor_threshold_exact` carries both halves in one statement:

* `c0 < c0*` — the anchor strictly helps, at the EXPLICIT exposure
  `x0 = g0/(2 c0 (g0 - g1))`, where `gfac = g0/2 > 0`;
* `c0 >= c0*` — the anchor never helps, at ANY exposure inside the budget.

STILL NOT ESTABLISHED. `D, M, K` are given reals, not derived from the
compensated world's actual query means, so the tie to the real instrument is an
interface. The threshold is for ONE alternative; the game's value is an infimum
over many and which alternative is active at the optimum is not determined here.
The case `M^2 >= 2 D K` is excluded, not covered.

## 2. D6 — the two-curve reduction. TESTED, and it survives.

`scripts/D4_two_curve_reduction.py`. The closed-form phase boundary rests on the
hypothesis that after group averaging the blind optimum needs only the ordinary
scalar and the width-`q` off-query. "The LP only put mass on two classes" is not
an argument — a dominated class carries no mass either way.

The test that matters: does the width-`q` off-query POINTWISE DOMINATE every
other joint class, over every alternative and every nuisance value? If so, moving
mass onto it raises the information against EVERY alternative, hence raises the
value, which is exactly the reduction. One violation refutes it.

    q=3,4,5   mu=0.25,0.5,0.75   6-10 joint classes   6384 comparisons
    -> DOMINATES in every cell, 0 violations, worst margin at float epsilon

The worst margins sitting at `1e-16` mean there are TIES, which is consistent
with domination and shows the bound is attained.

### A defect in MY OWN test, found by tightening it

Removing the grid and adding the scalar classes, the first version reported 13
violations and printed "REFUTED". That verdict was wrong, and the fault was in the
test, not the hypothesis: it asked whether the width-`q` class dominates the
ORDINARY SCALAR as well. It does not — and it should not, because the scalar is
one of the TWO survivors the reduction names, not a class to be eliminated. The
failures appeared only at `mu = 0.75`, which is ABOVE the phase boundary
`mu*(q) = 0.5636, 0.6019, 0.6279` for `q = 3,4,5` — exactly where the scalar is
supposed to enter. The wrong test was reporting the mechanism as a refutation.

Corrected test: every class OUTSIDE the two survivors is dominated by one of them.

    q=3,4,5   mu=0.25,0.5,0.75   372 comparisons over ALL nu in [0,1]
    -> DOMINATES in all 9 cells, 0 violations, worst margin at machine epsilon

The grid is gone: the difference of two class informations is a QUADRATIC in the
nuisance, so its minimum on `[0,1]` is attained at an endpoint or the vertex, and
all three are checked. That is a strictly stronger statement than the gridded one.

STILL NOT A PROOF. Float arithmetic with a `-1e-12` tolerance, not an exact
rational certificate, and only the `(q, mu)` cells listed. The coefficient matrix
comes from the solver module rather than being re-derived. So the boundary
equation is supported over the full nuisance range, not derived.

## 3. Support — the posterior identity, by double counting.

The `choose` absorption identity had no matching spelling in this Mathlib, so
instead of forcing it the identity is obtained by counting the pairs `(W, j)`
with `|W| = b`, `S ⊆ W`, `j ∈ W \ S` in two orders:

* over `W` first, each admissible world contributes `|W \ S| = b - s`;
* over `j` first, each unseen `j` contributes the number of admissible worlds
  containing it.

Equating them gives `Pr(j in W | S) = (b-s)/(m-s)` with the denominators cleared
— no `choose` identity anywhere, and no positivity side condition.
`posterior_double_count` and `posterior_ratio_cleared`.

STILL NOT ESTABLISHED. `hsym` — that the count is the same for every unseen `j` —
is a hypothesis here, discharged in the model by a transposition but not proved
in the file. And this is one step of U1-U5: the sample law, the Bayes lower bound
and the policy's risk are still outside, so `R_N^* = E[L_N/(a+L_N)]` remains
unproved, as `LeanSupportPassiveAnswerMultiplicityV1` says of itself.
