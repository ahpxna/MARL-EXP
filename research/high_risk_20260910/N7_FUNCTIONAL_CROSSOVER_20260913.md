# Package 1 (Functional): extrema-exploration vs capacity-gap crossover

First deliverable of the assignment: the three finite witnesses, the finite upper
bound they give, and the two limit laws checked against a full-extrema oracle.

## 1. Statement

Family exactly as assigned: incumbent `theta_I = (-1/2, 1/2)` (capacity 1),
outsider `theta_O = (-rho/2, rho/2, 0^n)` (capacity `rho < 1`), Gaussian variance
1, unit cost per cell, all means free, allocation `w` of total mass 1 over the
`4 + n` cells, alternatives constrained by `range(lambda_O) >= range(lambda_I)`.

**(A) PROVED (Lean, 7 clean audits).** `work/p13_conjectures/LeanFunctionalExtremaCrossoverV1.lean`

- `witness_EE` — moving all four endpoints to `±(1+rho)/4` flips, with energy
  *exactly* `(wI0 + wI1 + wO(e0) + wO(e1)) (1-rho)^2 / 32`.
- `witness_MM` — moving two middle cells to `±1/2` flips, energy exactly
  `(w_a + w_b)/8`.
- `witness_EM` — moving one middle cell to `1 - rho/2` flips, energy exactly
  `w_a (1-rho/2)^2 / 2`.
- `exists_light_one`, `exists_light_pair` — order statistics: some middle cell
  has `n w_a <= u`, and some middle pair has `n (w_a + w_b) <= 2u`, where `u` is
  the mass on the middle cells (`card_middles : |middles n| = n`).
- **`crossover_upper`** — for EVERY allocation with total mass 1 there exists a
  flipping alternative of energy at most

      kappa(rho) (1-rho)^2 / (32 kappa(rho) + n (1-rho)^2),
      kappa(rho) = min{ 1/4 , (1-rho/2)^2 / 2 }.

  Hypotheses: `0 <= rho`, `rho < 1`, `2 <= n`, `wI0 + wI1 + sum wO = 1`. No sign
  condition on the individual weights is needed.

**(B) NUMERICAL EVIDENCE only — the two limit laws.**

    (L1)  rho fixed < 1        :  n Gamma_n(rho)   ->  kappa(rho)
    (L2)  rho = 1 - c/sqrt(n)  :  n Gamma_n(rho_n) ->  c^2 / (8(c^2+4))

## 2. Assumptions

- Only the incumbent/outsider pair is in play (Top-1, one outsider), so the game
  information is a single shrink/open problem.
- `Gamma_n = sup_w J(w)` with `J(w)` the infimum of the energy over flipping
  alternatives. Weights are unconstrained in sign in the Lean statement; the
  numerical study restricts to the probability simplex.
- The numerical `Gamma_n` uses the symmetric reduction (both incumbent endpoints
  carry `p/2`, both outsider endpoints `q/2`, each middle cell `u/n`), with `p`
  and `q` kept **separate** — never tied to each other, as the assignment
  requires. That reduction is checked, not assumed (section 4).

## 3. Proof of the upper bound (the part that is formalised)

Because `J` is an infimum, exhibiting one alternative bounds it above; the three
witnesses are exactly the three ways the outsider's range can overtake the
incumbent's. Relaxing the two order statistics gives `min{u kappa/n,
(1-u)(1-rho)^2/32}` for the three witnesses at mass split `u`, and the stated
bound is the max over `u` of that min. Formally the combination is a two-case
split on `kappa u <= n V`; the identity `V (32 kappa + n (1-rho)^2) =
kappa (1-rho)^2` closes both branches.

**A real error found and fixed during formalisation.** The first version of the
case split was inverted: the branch `n V <= kappa u` is the branch where the
middle witnesses are EXPENSIVE, so it must use `witness_EE`, not MM/EM. Lean
rejected it. The corrected split is `kappa u <= n V -> middle witness`.

## 4. Evidence, with certificates

    .venv/bin/python scripts/N7_functional_extrema_crossover.py     (needs numpy+scipy)

Every check raises on mismatch; nothing prints-and-exits-0.

| check | worst residual |
|---|---|
| closed form `J(w) = min_pairs A B (1-D)^2/(A+B)` vs an independent z-scan | 3.63e-16 |
| closed form vs an independent constrained QP over full mean vectors (one QP per extrema region, scipy SLSQP, no decomposition used) | 6.00e-11 |
| O(1) symmetric evaluator vs the all-pairs closed form (including the degenerate faces) | 3.98e-16 |
| symmetric reduction vs unrestricted `(4+n)`-dimensional concave maximisation | 0.00e+00 gain |
| `rho = 0` against package N1's independent flat-outsider rate `1/(2(2+sqrt(2K))^2)`, `K = n+2` | 1.20e-07 |

**A second real error, found by the probe's own assertion.** The first symmetric
evaluator dropped the MM/EM candidates when `u = 0` instead of returning `J = 0`.
A cell of weight 0 can be displaced for free, so a single zero-weight cell makes
the flip free. The outer maximiser exploited that hole and reported
`Gamma_4(0) = 1/32`, which violated the proved upper bound `1/48` — that is how
it was caught. Correct value `Gamma_4(0) = 0.0167468`. The degenerate faces are
now part of the equivalence check.

**Three-witness bound is a relaxation, and dominates everywhere tested** (n in
{4,16,64,256} x rho in {0, 0.3, 0.5858, 0.75, 0.9}): ratio `Gamma_n / bound`
ranges 0.7500 to 0.9998, tightening as `rho -> 1`.

**(L1) fixed rho** — `n Gamma_n` against `kappa(rho)`:

| rho | n=4 | 16 | 64 | 256 | 1024 | kappa |
|---|---|---|---|---|---|---|
| 0.0000 | 0.06699 | 0.12500 | 0.17587 | 0.20954 | 0.22886 | 0.25000 |
| 0.3000 | 0.04565 | 0.10515 | 0.16798 | 0.20729 | 0.22827 | 0.25000 |
| 0.5858 | 0.01923 | 0.05870 | 0.12094 | 0.16980 | 0.20412 | 0.25000 |
| 0.7500 | 0.00747 | 0.02644 | 0.07238 | 0.12805 | 0.15947 | 0.19531 |
| 0.9000 | 0.00124 | 0.00484 | 0.01761 | 0.05187 | 0.10097 | 0.15125 |

Monotone increasing toward `kappa` in every row; convergence is slow (consistent
with an `O(n^{-1/2})` correction) and slower the closer `rho` is to 1. At
`rho = 0` the value is exactly `n/(4(sqrt 2 + sqrt(n+2))^2)`, which does tend to
`1/4`. The branch of `kappa` switches at `rho = 2 - sqrt 2 = 0.5858`.

**(L2) rho = 1 - c/sqrt(n)** — `n Gamma_n` against `c^2/(8(c^2+4))`:

| c | n=4 | 16 | 64 | 256 | 1024 | 4096 | limit |
|---|---|---|---|---|---|---|---|
| 0.5 | 0.0074728 | 0.0074314 | 0.0073986 | 0.0073777 | 0.0073659 | 0.0073596 | 0.0073529 |
| 1.0 | 0.0267901 | 0.0264424 | 0.0259305 | 0.0255357 | 0.0252882 | 0.0251496 | 0.0250000 |
| 2.0 | 0.0669873 | 0.0751362 | 0.0723799 | 0.0686629 | 0.0659591 | 0.0643350 | 0.0625000 |
| 4.0 | — | 0.1250000 | 0.1381594 | 0.1280487 | 0.1167785 | 0.1091612 | 0.1000000 |

Approaching from above, monotonically for large `n`. CORRECTED 2026-09-14: this
line previously read "already 9e-6 relative at `n = 4096`", which was wrong — it
reported an ABSOLUTE residual as a relative one, and not even that figure
correctly. Recomputed at `c = 0.5`, `n = 4096`:

    n*Gamma_n = 0.0073595502     limit = 0.0073529412
    absolute residual = 6.61e-06     RELATIVE error = 8.99e-04

The other columns, for the record: `c = 0.5` at `n = 1024` is 1.76e-03 relative;
`c = 1.0` is 1.15e-02 (n=1024) and 5.99e-03 (n=4096); `c = 2.0` is 5.53e-02
(n=1024) and 2.94e-02 (n=4096). The convergence is therefore roughly `1/n` in
the relative error, which is consistent with the limit law but is a far weaker
numerical statement than the retracted "9e-6".

**Which alternative is active** (recorded, as required — not just the optimum).
In the critical regime (L2) the active pair is always **EE or EM**, never MM —
consistent with the bottleneck pair being `(1-u)c^2/32` against `u/8`, which are
equal exactly at `u* = c^2/(c^2+4)`, the allocation named in the assignment. MM
appears only at large `n` with small `rho` (e.g. `rho = 0, n >= 256`), where
`kappa = 1/4`. At the optimum two constraints are tight, so the reported tag
flips between EE and EM along the row — that is the crossover, not noise.

## 5. Nearest prior

- Huang, Ok, Combes, Proutiere, *Structured Best Arm Identification* (PMLR v76,
  2017) — the "every arm must be measured" mechanism is standard BAI; an
  `Omega(n)` statement alone is not a contribution.
- Du, Kuroki, Chen (AAAI 2021) covers nonlinear reward with limited feedback, so
  that general description must not be used as the novelty claim.

What is candidate-novel here is narrower: the *exact* finite bound with the
`kappa` branch point at `rho = 2 - sqrt 2`, and the transition scale
`n (1-rho)^2` separating "pay to discover the extrema" from "pay to separate two
near-equal capacities".

## 6. Decision

**KEEP.** The upper half is formalised and the two limit laws survived an
independent oracle at four values of `n` over two regimes.

## What this does NOT establish

- **No lower bound is proved anywhere.** `crossover_upper` only exhibits
  alternatives. Both limit laws therefore remain NUMERICAL EVIDENCE; the matching
  finite lower bounds named in the assignment (endpoint mass `n^{-1/2}` for fixed
  `rho`, `u_c = c^2/(c^2+4)` at the critical scale) have not been proved, in Lean
  or on paper.
- The numerical `Gamma_n` is computed from the shrink/open closed form. That form
  is cross-checked against an independent QP at `n <= 3` only (14 configurations);
  at larger `n` the QP was not run, for compute. This is stated, not silently
  truncated.
- The symmetric reduction was verified lossless only at `n in {2,4,8}` and
  `rho in {0, 0.5, 0.9}`. It is not proved.
- Convergence in (L1) is slow and NOT extrapolated: at `rho = 0.9, n = 1024` the
  value is 0.101 against `kappa = 0.151`. The tables are consistent with the
  claimed limits but do not by themselves exclude a different limit.
- Nothing here concerns the response table of the real generator, C_lucb, or any
  allocator: this is one two-relation family.
- `Gamma_n` is a game information rate, not a sample complexity; no stopping rule
  or algorithm is implied.
