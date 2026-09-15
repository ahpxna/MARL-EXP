# F05: the full-extrema alternative oracle, and a retraction
Date: 2026-09-12. Append-only. This supersedes the INTERPRETATION in
`F05_FULL_EXTREMA_FINDINGS_20260912.md`; that file stays as the historical record.

## 0. Retraction of the earlier F05 numbers

The earlier probe reported ratios `J_true/J_pairflip` of A 1.000, B 0.349,
C 1.091, D 0.113. Those numbers are WITHDRAWN as evidence. Four defects:

1. The "generator-drawn" probe wrote its own `draw_world` instead of calling
   v4's `_draw_world`. v4 sorts capacities and subtracts `arange*1e-3`, draws
   `center ~ N(0,.3^2)`, and PINS the extrema (`random_extrema`); sigma is per
   ACTION, shared across relations. The probe's population was a different one.
2. It examined only the weakest Top-k relation against the strongest outside
   relation. With unequal precisions the cheapest crossing pair need not be the
   boundary pair.
3. It read "extrema changed" off `np.argmax` index changes. Under exact ties the
   index moves without the old extrema ceasing to be optimal (case C).
4. It compared a scalar formula against a fixed-extrema QP as if they were the
   same problem.

## 1. The three quantities, kept distinct

    J_scalar : pair-flip at the CURRENT extrema, ordering constraints dropped
    J_old    : QP in the CURRENT extrema region (ordering constraints kept)
    J_full   : the whole alternative set (any extrema in either relation)

Proved order (by inclusion of feasible sets): `J_scalar ≤ J_old` and
`J_full ≤ J_old`. There is NO general order between `J_scalar` and `J_full`.

MEASURED (600 random worlds, R=3, K=4, k=1, precisions log-uniform on
`10^[-2.5, 2.5]`):

| relation | count |
|---|---|
| `J_full < J_scalar` | 119 |
| `J_full > J_scalar` | 69 |
| equal | 412 |

extreme ratios `J_full / J_scalar`: **0.000300** and **7.120977**. Both extremes
were re-solved with the independent exhaustive-region oracle and agreed.
So pair-flip is a bound in NEITHER direction, and the gap is not a small
constant: it reached three orders of magnitude here.

## 2. The oracle: shrink an interval, open a pair

Model: independent Gaussian, known variance, FREE response table (no
realizability coupling). `alpha[r,a] = w[r,a]/sigma[a]^2`. Capacity is the range
`max_a theta[r,a] - min_a theta[r,a]`; Top-k by capacity, `T` unique.

    J(w) = min over i in T, j not in T, inf over z >= 0 of  S_i(z) + E_j(z)

    S_i(z) = min over l of (1/2) * sum_a alpha[i,a] * dist(theta[i,a],[l,l+z])^2
    E_j(z) = min over ordered pairs a != b of
             [ z - (theta[j,a]-theta[j,b]) ]_+^2 / (2*(1/alpha[j,a] + 1/alpha[j,b]))

PROOF (three steps, all elementary):

* **Decomposition.** The Top-k set changes iff some `j` outside overtakes some
  `i` inside, i.e. `c'_j >= c'_i`, iff there exists `z` with `c'_i <= z <= c'_j`.
  Relations `i` and `j` occupy disjoint coordinate blocks and every other
  relation stays put at zero cost, so the cost separates and the infimum over
  the alternative set equals `min_{i,j} inf_z [ cost_i(<=z) + cost_j(>=z) ]`.
  This is an equality, not a relaxation.
* **Shrink.** `range(theta') <= z` iff all cells of relation `i` lie in a common
  interval of length `z`. For a fixed interval the separable quadratic is
  minimised coordinate-wise by projection, giving `S_i(z)`.
* **Open.** `range(theta') >= z` iff some ordered pair satisfies
  `theta'_a - theta'_b >= z`. Minimising a separable quadratic under one linear
  constraint gives `g_+^2 / (2*(1/alpha_a + 1/alpha_b))` with
  `g = z - (theta_a - theta_b)`; no third cell needs to move.

`S_i` is convex nonincreasing in `z`, `E_j^{ab}` convex nondecreasing, so each
`(i,j,a,b)` subproblem is a 1-D convex minimisation. That replaces the
`O(K^2 * K^2)` extrema-region enumeration per relation pair by `O(K^2)` convex
1-D problems. This is a count of SUBPROBLEMS, not a runtime claim: the cost of
solving each one is not included.

## 3. Certificate

`J_decomp` versus an INDEPENDENT exhaustive-region oracle (every ordered
`(argmax,argmin)` choice for both relations, each region solved as its own
constrained QP, feasibility of the returned point re-checked against the
original nonsmooth constraint):

* 4 worlds from v4's own `_draw_world` (R=4, K=4, k=2, uniform allocation),
* 4 adversarial worlds: exact tie in the Top-k gap, exact tie between two
  relations, precision `1e4` on one cell, `sigma = 0.1` on one cell,
* plus the two extreme worlds of the 600-world search above.

Result: **10/10 agree**, maximum relative difference `6.6e-14`.

EVIDENCE CLASS: the three-step argument in section 2 is a PROOF SKETCH in prose,
not machine-checked; nothing here is PROVED in the Lean sense. The agreement in
section 3 is NUMERICAL EVIDENCE for that sketch. Formalisation has not started.

## 4. Scope that must travel with any citation

* Free-table model only. Under realizability coupling the cost no longer
  separates across relations and the decomposition is not claimed.
* `T` unique; ties in the Top-k boundary are handled by taking the closed
  alternative set (`>=`), the usual convention.
* Says nothing about which allocator to use. The next question -- what an
  allocator built on this oracle buys over C_lucb -- is open, and the comparator
  must be C_lucb, not uniform.
