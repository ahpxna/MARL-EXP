# Worker checkpoint — 13 September 2026

This checkpoint advances four parts of the eight-package assignment. It does not close the entire six-paper programme. `manifest.json` and `RECEIPT.md`, generated only after hash and axiom checks succeed, determine acceptance. Structural sources under development are excluded from this checkpoint.

## Exact scope of the new proofs

| Area | New modules | What is proved | What is still open |
|---|---:|---|---|
| Functional | 3 | Two unbounded scalar/full-cost separations; interval projection and pair opening; exact full-extrema oracle equality | General R-by-K decomposition, strict-alternative perturbation, coupled physical tables, allocator advantage over C_lucb |
| D6 static | 5 | Exact scaled coefficients; clamped value limit; coefficient and value errors; eventual physical-game certificate | Uniform compact formulation and first-order boundary-window limit |
| Support | 3 | Refutation of the s−1-private helper; all-private union lower bound on a line; actual kernel support/radius/membership construction | Cyclic reduction, concrete cyclic tent, adversarial query lower bound, matching strategy |
| Query | 2 | Scalar midpoint decoder, exact minimax radius, feature repair iff bad-pair separation | Physical feature/horizon restrictions, cost optimization/dual certificate, population-to-empirical guarantees |

Previously accepted work is separate: D05/D06 has 33 modules and 259 audits; the adaptive continuation has 12 modules and 53 audits and was installed in `research/adaptive_worker_acceptance_20260912`. The decoder handoff is finished. A common adaptive scheduler, the law of its extracted samples, whole-algorithm stopping tails, expected Gamma rate, and matching lower bound remain open. The reference-family observation-law bridge and growing-q complexity are also open. Discovery stopping does not close those tasks.

## Functional: quantified statements and proof

The Lean row type is `Fin 3 → ℝ`. For two independent/free rows with positive precisions, energy is the sum of the six precision-weighted squared displacements divided by two. `fullCost` is the infimum over alternatives with the first row's range at most the second row's range. These are closed, tie-allowing alternatives.

In the cheap-middle family, the scalar cost is 1/32. Raising the cheap middle cell of the second row from 1/4 to 1 is feasible and costs 9 eta/32. Thus 0 ≤ full/scalar ≤ 9 eta. In the cheap-maximum family, the two expensive cells of the first row give a contraction lower bound [3/4−z]_+²/4; any expanded pair in the second row gives [z−1/2]_+²/4. The positive parts sum to at least 1/4, giving full cost at least 1/128. Its scalar cost is eta/[8(1+3 eta)]. The two `no_uniform_*` theorems explicitly quantify over every positive comparison constant and construct a positive eta at most one that violates it.

For the oracle, a range-constrained row lies in some interval [ell,ell+z]. Coordinatewise projection minimizes its cost. A row of range at least z has an ordered pair with difference at least z, including z=0 and flat rows. Completing the square gives the exact pair-opening cost. Every oracle candidate produces a feasible six-cell alternative with exactly its proposed cost. Conversely, every alternative dominates one such candidate. These two inequalities prove equality of the infima. No optimizer is assumed in a structure field.

`functional/exact_oracle.py` implements rational active-region enumeration for this same two-by-three oracle. Every one of the 324 closed regions gets either a positive-semidefinite quadratic KKT certificate or a Farkas infeasibility certificate. `verify_exact_oracle.py` checks all certificates without calling the solver, and checks that the best region produces an actual feasible alternative with exactly the claimed energy. Ten instances cover four eta values in each family, a tie, and a flat table: 3,240 regions. Four deliberately corrupted certificates are rejected. At eta=1/10000, the cheap-middle ratio is 9/10003, while the cheap-maximum ratio is 100100021/160012. These are exact scalar-proxy comparisons, not C_lucb allocator benchmarks.

## D6: finite constants and actual-game interpretation

Write C=exp(−2 tau), c_k=(1−tau/k)^(2k−2), a_k=(1+(k−2)tau/k)c_k, b_k=((k−2)tau/k)c_k, e_k=min(a_k,2b_k), and threshold_k=2a_k−e_k/k. The normalized phase value is

    max(0, threshold_k−rho) * (rho−2b_k + max(0,e_k−(2a_k−rho))/(k−1)) / (4c_k).

Its limit is

    G(tau,rho) = max(0,2(1+tau)C−rho) * (rho−2tau C) / (4C).

The positive part is retained throughout. The finite logarithm inequality for 0≤x≤1/2 gives |log(c_k)+2tau|≤(2tau+4tau²)/k. Exponential is 1-Lipschitz on the negative half-line, hence the same coefficient error for |c_k−C|. The exact exponent 2k−2 is included in the limit proof.

The value-error module defines explicit constants:

    D  = 2tau + 4tau²
    Da = (1+tau)D + 2tau
    Db = tau D + 2tau
    Dt = 2Da + (1+tau)
    Nv = 2(1+tau)(2Db+4) + (2+2tau)Dt
    Cv = Nv/(2C) + 2(1+tau)²D/C².

For tau≥0, rho∈[1,2], k≥2, k≥2tau, and 2D/k≤C, the theorem gives |V_k/k−G|≤Cv/k. The last condition is an explicit numeric size condition, equivalent for positive k,C to k≥2D/C. The proof bounds the a,b errors, uses Lipschitzness of max for the threshold factor, bounds the extra positive-part term by 4/k, and controls division using c_k≥C/2. It does not assume the desired value error.

For every tau>0 and rho∈[1,2], eventually in q, every actual reference world T with k=q+1 admits a `Region` at t=tau/(q+1), rho, whose `CertifiedValue` equals this formula. The Region carries both minimax quantifiers from the already accepted physical certificate. Its strong restriction (q−1)b≥1 is proved eventually from b_k→tau exp(−2tau)>0; it is never dropped. Thus the normalized clamped limit is a limit of certified actual static game values. It is not an adaptive information-rate theorem.

`static/check_scaled_reference.py` supplies 60 finite-error checks and five negative controls refuting the unclamped formula. The separate 36 boundary-window values are numerical evidence only. The proposed V_k(rho_infinity+s/k)→[D_boundary−s]_+/2 remains unproved in Lean; the checked leading-value limit does not imply it.

## Support: corrected quantifiers and physical kernel

The exact counterexample consists of [0,3), [2,5), [1,4). Only the first two have private points, and the union has size 5 rather than the proposed 7. It refutes the old helper, not the final query-depth conjecture.

For strictly increasing natural starts x_i and equal positive integer length L, the line theorem assumes every one of the s intervals has a private point. A private point of an interior interval forces the adjacent gaps to sum to at least L+1. The union size is L plus the sum of the gaps clipped at L. Pairing the gaps, with the final positive gap in the even case, proves

    |union| ≥ floor(s/2)(L+1) + (s mod 2)L.

The cyclic enumeration is finite evidence only: 138 parameter cells, 12,938 all-private families, with an attaining family in every cell. It does not supply a cyclic theorem or decision strategy.

For any nonnegative kernel phi(j,w) on m≥2 coordinates, define center_w=sum_j phi(j,w)/(m−1) and P_w(j)=center_w−phi(j,w). The actual residual after retaining coordinate j is exactly phi(j,w). On support {0} union {P_w : w in W}, the selected radius is half the largest kernel value, with zero included. Thus radius≤eps iff every retained tip satisfies phi(j,w)≤2eps, for eps≥0. Kernel-column injectivity and nonzero columns imply physical point injectivity and nonzero tips; consequently membership at P_a is exactly a∈W. These kernel premises remain explicit and must be checked for a proposed tent kernel.

## Query: constructive minimax and repair

For every finite nonempty population, arbitrary representation R, and scalar target g, the midpoint of each nonempty fibre's minimum and maximum achieves half its diameter. Empty representation fibres receive value zero but do not affect risk. The largest same-fibre pair difference divided by two is nonnegative, is attained as a worst-case lower bound against every decoder, and equals the infimum of feasible uniform error tolerances. Constant-target and singleton fibres are included.

For a finite chosen feature set J and eps≥0, a decoder on (R,h_J) has uniform absolute error at most eps iff every same-R pair whose target difference exceeds 2eps is separated by some selected feature. This is a scalar finite-population statement. No general norm half-diameter theorem, held-out guarantee, or novelty claim relative to Test Cover follows.

## Evidence and reproduction

Each new Lean module has its source, olean, log, and receipt. Acceptance checks exit zero, source unchanged during its compilation, matching source/olean/log hashes at finalization, and only the standard axioms `propext`, `Classical.choice`, `Quot.sound` in printed theorem dependencies. The finalizer also checks the local transitive dependency snapshots against their own compiled receipts or the prior D05/D06 acceptance manifest. Dependencies from Mathlib are recorded through the Lean toolchain and package manifest.

The two Query dependency copies differ from repository originals only by appended `#print axioms` commands. They are archived for reproduction and do not overwrite the original repository sources. Rebuilt dependencies and their audit counts are not counted as new modules or new audits.

Run each directory's `compile.py` in dependency order with the recorded Lean toolchain; numerical controls use Python's standard library only. The installation script refuses differing existing source files, copies only the newly accepted modules into `work/p13_conjectures`, and archives the full evidence. No unrelated repository edits are included.
