# Four flagged defects, fixed. Plus both sides of the MASTER threshold.

## 1. MASTER decision rule — a real logic bug, fixed with regression tests

`scripts/M1_certified_acquisition.py`. The REJECT branch compared the DESIGN'S
LOWER bound with the OPTIMUM'S LOWER bound:

    if lo_w < (1 - zeta) * gamma_lo: return "REJECT"

That is the wrong direction of certification — a low lower bound does not make a
design bad. The corrected rule gives the design two bounds of its own:

    ACCEPT   if  L_w >= (1 - zeta) * U_Gamma
    REJECT   if  U_w <  (1 - zeta) * L_Gamma
    else     UNDECIDED

Two regression tests now run on every invocation and both reproduce the flagged
failures:

* an OPTIMAL design bounded only into `[0,1]` with `Gamma = 1`, `zeta = 0.05`:
  corrected rule returns **UNDECIDED**, the previous rule returned **REJECT**;
* `J = 1 - 2^-60`, `Gamma = 1`, `zeta = 0`: exact gives **REJECT**, deciding in
  floats gives **ACCEPT**. So the claim "no rule picks a side from a float" was
  FALSE; verdicts are now computed on `Fraction`s and the test asserts the two
  disagree, so the defect cannot silently return.

The `dual_ok` field inspected the dual of a `g.solve(...)` call while the interval
came from a different `d1.solve_value(...)` call, so it certified nothing about
the reported ceiling. The claim is withdrawn; no dual certificate is asserted for
D6.

The four Functional verdicts are unchanged when recomputed exactly.

## 2. A wrong statement of mine about the direction of the bounds

The docstring said the floor of every interval is obtained by EVALUATING real
alternatives. That is backwards. `J(w) = inf over Alt of E_w(lambda)`, so
evaluating one alternative bounds `J(w)` ABOVE. A floor needs a statement
covering EVERY alternative:

* Functional — `energy_ge_pairV` (proved) gives the minimum over ordered pairs as
  a genuine floor;
* D6 — the exact minimisation over the whole finite alternative set.

Corrected in the script and recorded in the artifact.

## 3. Structural — independent checker, and the stronger result confirmed

`scripts/S3_avg_path_certificate.py` calls no optimizer in its checking path. It
verifies, exactly: `P >= 0`, `sum P = 1`, **all 30 prefix marginals recomputed
from `P`** (the previous checker rationalised and recomputed objectives but never
re-verified the marginals), `max_k E_P[r] = 4/15`, `E_P[max_k r] = 7/15`.

A dual candidate is taken from an LP and then **verified feasible in exact
rational arithmetic**, with objective `7/15` — equal to the primal, so

    V_avg = 4/15   and   V_path = 7/15   are the OPTIMA, not merely bounds,

attained by the uniform distribution on `(0,2,3,1,4)`, `(1,0,4,2,3)`,
`(1,4,3,2,0)`. The dual's `||y||_1 = 17/5`, which upgrades the point separation to
a robust one: widening every marginal constraint by `tau` leaves dual feasibility
intact and lowers the dual objective by at most `tau ||y||_1`, while `P` stays
feasible, so

    V_path(tau) - V_avg(tau) >= 1/5 - (17/5) tau > 0   for   0 <= tau < 1/17.

The artifact now carries the matrix, `x`, `P`, the dual and `||y||_1`.

PHRASING CORRECTED: the ratio `7/4` says the EXPECTED WORST-BUDGET regret is 75%
higher than the WORST-BUDGET EXPECTED regret. It does NOT say every drawn ranking
is 75% worse.

## 4. D6 — "exactly constant" withdrawn, and two conclusions separated

A float LP on a grid cannot show a ratio is EXACTLY constant on an interval. What
the data supports is that every measured point below `mu*` agrees within the
solver's tolerance and the first point above it does not. Reworded.

The range `0.21`-`0.38` was the six original cells, not all 28; the wider sweep
reaches `0.17065` at `q = 4, mu = 0.65`. Recorded.

`V_blind < Gamma` says no single fixed allocation is oracle-optimal in every
world. It does **not** establish a separately-payable discovery cost: an
algorithm can learn while it deploys. The step that would establish a cost is
`L_zeta` plus the information lower bound, and neither is done.

## 5. B1 — certified enclosures, both directions

`scripts/certified_pow.py` (new, self-tested) replaces

    cz = Fraction(2 ** z).limit_denominator(10**12);  czup = cz * (1 + 1e-9)

which certifies nothing. Two observations make a real certificate cheap:

* `2**(z*) = 2 (g/mu)^2` is EXACT and rational — but `r**z` for `r != 2` is not,
  so the EXPONENT itself must be bracketed, exactly as flagged.
* `z_lo <= z* <= z_hi` is certified by the integer comparison
  `2**a <= (g/mu)**(2 den)`, and `c_lo <= r**(num/den) <= c_hi` by
  `c_lo**den <= r**num <= c_hi**den`. Floats seed the search and never appear in
  a certificate.

Both call sites are fixed with the correct end: `dual_upper` divides by a
certified LOWER bound `c_lo` (a smaller charge can only raise an upper bound),
the primal uses the certified UPPER bound `c_hi` (a larger charge can only lower
a lower bound), and the `eta` cap uses `c_lo` to stay inside the domain.

The self-test exhibits the gap: on one case the old pattern returns
`18.000000018` while the certified bracket is `[17.99969, 18.00094]`. The old
value lands inside — but that is luck, not proof, and nothing about which side it
falls on was established.

### B1 re-run under the certified charges: the result SURVIVES

`z*` is bracketed to width `1e-4` and every charge is a certified enclosure, so
the primal is charged more and the dual less than before — the sandwich can only
widen. It stays tight and the conclusion holds:

* **24 of 24 rows keep a strictly positive certified gain `L - V0`**, so the
  design still strictly beats the B-scalar value below the boundary;
* the sandwich stays narrow: `max U/L = 1.00329`;
* the `h^2` law survives: at `q=3, mu=1/4` the gain runs
  `1.474e-04, 4.400e-05, 8.025e-06, 2.098e-06` for `h = 1/10, 1/20, 1/50, 1/100`,
  with successive ratios approaching the `4` and `2.5` that `h^2` predicts.

So the earlier numbers were not an artefact of the uncertified rounding. They are
now backed by enclosures proved with integer comparisons, with the primal using
the upper end of each charge and the dual the lower end.

## 6. Both sides of the MASTER threshold — now PROVED

`work/p13_conjectures/LeanMasterAnchorCertificateV1.lean`, **8 audits, 0
nonstandard, accepted**. The previous version had only the "no anchor needed"
half. Added:

* `gain_identity` — the gain, with the anchor term `s = x0/sig0` abstract so no
  division by `sig0` enters the algebra;
* `anchor_strictly_helps` — BELOW the price, scaling the anchor-free design by
  `1 - c0 x0` and spending the freed budget on exposure STRICTLY increases the
  profiled information, exactly when
  `2 c0 D K ((1-t)K + x0/sig0) < M^2 (K c0 (1-t) + 1/sig0)`, `t = c0 x0`. No
  calculus: the difference is that inequality multiplied by `x0`;
* `anchor_cheap_suffices` — an explicit price bound implying it;
* `anchor_threshold_two_sided` — both directions in the same variables.

### The two sides now MEET, at an explicit price

The earlier version left a band of prices where neither direction fired. That
band is gone. The reason is that the gain factors as

    gain(x0) = x0 * gfac / (2 K A),     gfac AFFINE in t = c0 x0,

with endpoints `g0 = c0 K (M^2 - 2 D K) + M^2/sig0` at `t = 0` and
`g1 = (M^2 - 2 D K)/sig0` at `t = 1`. An affine function on `[0,1]` is
non-positive as soon as BOTH endpoints are — so there is no small-`x0` escape and
no large-`x0` escape, and the one-sided argument becomes two-sided for free.
Verified exactly on 400 random rationals before formalising: the factorisation
and the affine identity both hold with zero mismatches.

With `M^2 < 2 D K` the critical price is

    c0* = M^2 / (sig0 K (2 D K - M^2))

and `anchor_threshold_exact` proves BOTH halves in one statement:

* `c0 K (2 D K - M^2) < M^2/sig0`  (i.e. `c0 < c0*`) — the anchor strictly helps,
  at the EXPLICIT exposure `x0 = g0/(2 c0 (g0 - g1))`, where `gfac = g0/2 > 0`;
* `M^2/sig0 <= c0 K (2 D K - M^2)`  (i.e. `c0 >= c0*`) — the anchor never helps,
  at ANY exposure in the budget.

STILL NOT ESTABLISHED: `D, M, K` are given reals, not derived from the
compensated world's actual query means, so the link to the real instrument is an
interface. The threshold is for ONE alternative; the game's value is an infimum
over many, and which alternative is active at the optimum is not determined here.
The case `M^2 >= 2 D K` is excluded, not covered.
