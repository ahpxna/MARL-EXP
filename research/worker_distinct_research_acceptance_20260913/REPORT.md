# Distinct research batch N1–N6 — worker checkpoint, 2026-09-13

This checkpoint implements the newly assigned research directions. It is not an audit or completion claim for the earlier adaptive scheduler/termination/Gamma work. Work was performed directly without subagents. This checkpoint contains 12 freshly compiled new modules and 66 clean axiom audits, against 24 snapshotted local dependency modules. The statement inventory below distinguishes compiled mathematics, numerical evidence, and outstanding work.

## N1: exact action-count law and robustness to breaking ties

`LeanFunctionalFlatOutsiderRateV1` and `LeanFunctionalFlatOutsiderMinimaxV1` prove

\[
\sup_{p,t,w\ge0,\;p+t+\sum w=1}\inf_{\operatorname{range}(z)\ge |y-x|}
\tfrac12[p x^2+t(y-1)^2+\sum_i w_i z_i^2]
=\frac1{2(2+\sqrt{2K})^2},\qquad K\ge2.
\]

This is the actual two-action incumbent (0,1), K-action zero outsider Gaussian energy problem. The alternative is represented as an ordered pair with separation at least the incumbent's absolute endpoint difference; zero weights are permitted. The Lean result includes `IsGreatest` of attainable information and the `sSup` identity, not just a scalar quadratic optimization. It uses the closed alternative boundary specified by the benchmark; an application with exclusively strict ranking changes still needs its closure bridge.

A direct dual replaces informal symmetrization: choose two least-weight outsider cells, whose combined mass is at most 2/K of outsider mass. Write s=sqrt(2K), H=2+s. Move incumbent means to (1/H,1−1/H), and those two outsider means to ±s/(2H). This witness bounds every allocation by 1/(2H²). The matching allocation gives each incumbent endpoint 1/H and each outsider cell 2/(sH), with total exposure one. Sum-of-squares proves the lower bound against every alternative.

`LeanFunctionalOutsiderPerturbationV1` proves an additional robustness result at the energy/design level: if outsider means theta have range at most rho<1, the same uniform allocation guarantees at least `(1-rho)^2 Gamma_K`, while every allocation has an alternative of energy at most `Gamma_K`. Orient the two least-weight cells in descending theta order for the upper witness. Thus a coordinate perturbation bounded by eta<1/2 gives a factor `(1-2 eta)^2`, uniform in K. This rules out collapse of the benchmark solely from a small tie-breaking perturbation. The incumbent remains (0,1); no padded-incumbent claim is made.

`flat_outsider_probe.json` checks all explicit endpoint pairs for K=2,4,8,16,32 with 70-digit arithmetic and residual below 10^-65. This is a construction check, not an independent full-oracle optimization.

**Remaining:** general Top-k one-cell displacement/mandatory-positive-mass API; strict-alternative closure bridge; the separate padded-incumbent variant if needed; a Lean asymptotic limit statement. No new-literature novelty claim is asserted.

## N4: approximate answers and distance-dependent nuisance alternatives

`LeanD6ApproximateAnswersV1` bridges literal `productCompressionLoss` to `(2-mu)|A\B|/2`, proves the natural-floor exchange-ball equivalence, low-tolerance zero exchange, equal-cardinality uniqueness, and the correct nuisance condition using the alternative's nu.

For distance d>0, bad nuisances satisfy `0<=nu<=1` and `nu<2-2 epsilon/d`. There are bad alternatives exactly when epsilon<d. `LeanD6ApproximateProfileV1` separates empty, closed, and half-open domains. Together with `LeanOpenQuadraticProfileV1`, it proves the positive-curvature quadratic infimum on the nonempty bad domain by clipping the unconstrained minimizer. The half-open endpoint can supply an infimum without being an admissible alternative. Zero curvature has a separate affine endpoint minimizer theorem. Generic nonempty-set infimum monotonicity is proved; the complete outer max/sup D6 Gamma-epsilon monotonicity theorem is not yet instantiated in Lean.

`approximate_game.py` enumerates all legal scalar and joint queries at q=3,4,5, mu=1/2, epsilon in {0,.74,.75,.76,1.49,1.5,1.51}. Unit variance and unit cost are explicit. Each epsilon-good answer shell is optimized. The code averages queries under permutations preserving both A and the chosen answer B, and enumerates alternative-label orbits under that same stabilizer. A semi-infinite LP uses exact quadratic best responses in floating-point arithmetic. Dual distributions over alternative label/nuisance pairs yield upper bounds; all-label best responses yield lower bounds. These are characteristic information games, not adaptive algorithms and not oracle-only query restrictions.

| q | Gamma_0 | Gamma_1.49 | ratio |
|---|---:|---:|---:|
| 3 | 0.1076951491 | 0.5000000000 | 4.642735 |
| 4 | 0.1074279385 | 0.4407665635 | 4.102904 |
| 5 | 0.1088573350 | 0.4307806179 | 3.957295 |

All 21 outer game cells select answer shell zero within numerical resolution. Improvement here comes from removing alternatives that no longer make the answer bad; these experiments do not show an advantage from selecting a different approximate answer. Tiny ratios below one around epsilon=.74 are within the reported LP bounds, not violations of monotonicity. Absolute game gaps are at most 2e-8.

**Remaining:** formal bridge from the existing actual-information quadratic coefficients to the clipped approximate evaluator and outer answer game; general phase/asymptotic law for q and normalized tolerance; adaptive attainment. Current evidence covers mu=1/2, not a full mu grid.

## N6: unknown calibration and legal designs

`LeanMasterUnknownCalibrationV1` proves the finite weighted square completion for general nuisance direction v, positive-curvature profile minimum, and the zero-curvature case with nonnegative weights. It includes the single-channel cancellation identity, balanced cross-term result, opposite-sign channels, cost Cauchy identity and attaining allocation.

`LeanMasterCalibrationCostV1` closes the two-channel information optimum, with positive standard deviations s,t and square-root costs r,v:

\[
\max_{r^2x+v^2y=1} I_{\rm prof}(x,y)
=\frac{\gamma^2}{2(sr+tv)^2},\quad
x=\frac{s/r}{sr+tv},\quad y=\frac{t/v}{sr+tv}.
\]

Nonnegative allocations include zero-exposure boundary cases in the upper bound. The profile equality is proved for positive exposures. The factor-four equal-cost control comparison is specific to that design, not universal.

**New actual D6 construction:** `LeanD6CalibrationBalancedDesignV1` assigns mass `1/(3q+1)` to every ordinary scalar query and `q/(3q+1)` to reference scalar j. All queries are legal; the allocation depends only on q and j, not A or mu. Its weighted actual mean is `(q+1)/(3q+1)` for every admissible A and every mu. Therefore its cross term is zero for every pair `(A,mu),(B,nu)`, and profiling a common offset leaves this design's information unchanged. Normalization is proved for ambient size 2q+2. This is a theorem about the actual response API, not assumed regression coefficients. It assumes equal unit measurement variances when reading weights as budget mass.

This balanced scalar design need not be optimal. `calibration_game.py` optimizes the **full legal query family** after jointly profiling alternative nu and unrestricted common offset:

| q | known offset | profiled offset | profiled/known | balanced scalar design |
|---|---:|---:|---:|---:|
| 3 | .1076951491 | .1076951510 | 1 within bounds | .0229166667 |
| 4 | .1074279385 | .0972987651 | .905712 | .0180288462 |
| 5 | .1088573350 | .0885917450 | .813833 | .0148437500 |

Thus nuisance-free information for one legal design does not imply no penalty in the optimized game. Exact rational checks cover every label at q=2,3,4,5 for the A-independent mean identity. Uniform weights over all scalar queries are a negative control: they cancel same-nu swaps but generally fail for differing nuisances.

**Remaining:** general optimized calibration law; multi-direction/singular nuisance; link of the cost theorem to compensated fixed-world shifted-reference slopes; distribution-level single-channel indistinguishability and adaptive implementation. The compiled single-channel statement here is algebraic.

## N2: randomized staircase menu

`LeanStructuralRandomMenuV1` proves on the actual normalized staircase:

- a ranking hits at most one critical budget when `2*r*epsilon<1`;
- a menu hits at most its cardinality;
- any finite randomized menu with pointwise size<=K and per-budget success>=1−delta obeys `r(1−delta)<=K`;
- every menu with size<r has a critical budget that defeats all of its rankings, so an adversary choosing after seeing the menu defeats every realized menu;
- the canonical menu has exactly r distinct entries;
- uniform K-subsets have exact membership probability K/r, and cover every budget with probability at least K/r, using the actual epsilon-optimal geometry.

These matching bounds establish the proposed ceil tradeoff mathematically. The module leaves finite randomization and the uniform-subset count explicit; it does not package them as a single PMF-valued `random_menu_exact` theorem or a separate ceil-valued optimization definition. Coverage upper bound assumes K>0, appropriate for delta<1 and r>0. No theorem beyond the stated tolerance range or general fractional-cover geometry is claimed.

## N3: nonadaptive/batched membership

`LeanSupportNonadaptiveCompletionV1` proves the missing consistency mechanism: a hitting set has enough available points by incidence counting; it can be extended to a size-s world with exactly the chosen YES transcript; and every proposed window has a size-s consistent counterworld. The interval hitting-set construction itself remains a premise at this stage.

`nonadaptive_windows.py` implements greedy line-interval hitting after cutting the cycle at an unqueried point. It checks 4,824 lower transcripts across 53 configurations (3<=m<=10, 1<=s,L<=3, m>sL), constructs a separate consistent counterworld for every candidate window, and verifies the sL-query upper strategy over every size-s world. All pass. Exact DP chooses a full query batch before replies, and enumerates nonempty posterior reply cells:

| (m,s,L) | 1 batch | 2 batches | 3 batches |
|---|---:|---:|---:|
| (5,2,2), (6,2,2), (7,2,2) | 4 | 3 | 3 |
| (7,2,3), (8,2,3) | 6 | 4 | 4 |
| (8,3,2) | 6 | 5 | 5 |

**Remaining:** Lean interval packing/hitting, cycle cutting and degree-L incidence bridge, nonadaptive exact theorem and physical radius link, and general batch law. The finite table is not a universal depth proof.

## N5: measurement resolution

`LeanQueryResolutionMinimaxV1` proves the overlapping sup-norm balls criterion, the compatible-world midpoint decoder, the matching decoder lower bound and exact minimax infimum for every finite nonempty world family with eta>=0. Coordinate type need not be nonempty. Constant targets and observations incompatible with every world are handled in the definition.

`resolution_panel.py` uses all 1,600 units, including 1,541 constant horizon-6 profiles. Features are actual stored R1, (R1,R2), c1, (c1,c2), with no ID/catalog features; both ATE and Shapley targets are retained. Eta is a fixed rational grid from 0 to 2 in native reward units, declared before outcomes are read; this is a sensitivity grid, not an empirically calibrated noise model. For centered coordinates eta applies to the computed features, not automatically to each raw observation before centering.

For every representation, the global finite-panel floor is already 3/5 for ATE and 5/4 for Shapley at eta=0 and stays at that value over the grid. This panel therefore gives a negative result for a new small-noise instability claim: exact collisions already realize the global diameter. Per-unit certificate counts refer only to noiseless-center observations y=R(theta), not to success probabilities or a guarantee for every disturbance. Critical-resolution calculations distinguish an empty bad-pair set.

**Remaining:** Lean critical-resolution theorem and continuous physical nearly-null directions; actual measurement-noise calibration. No transfer/generalization claim follows from this panel.

## Verification and reproduction

`verify_games.py` independently reconstructs every actual mean on all labels and all legal queries. It expands each dual representative over its full stabilizer orbit and reevaluates each primal allocation against all labels, without importing the solver coefficient builder. All 45 certificates (42 approximate-answer shell cells and 3 calibration games) pass, with 3 corrupted certificates rejected. Numerical certificates remain floating-point bounds, not rational/Lean LP proofs.

`check_boundary_cases.py` checks 210 rational bad-nuisance cases, a true-mu substitution negative control, an excluded endpoint negative control and 5 invalid solver inputs. Compiled Lean receipts record source/dependency/binary/log hashes and axiom audits; only propext, Classical.choice and Quot.sound are accepted. This is a fresh build of new modules against snapshotted existing dependencies, not a clean rebuild of mathlib or the complete project.

Run Python scripts from this directory. If needed, install `requirements.txt` into the local `python_deps` directory; this avoids changing the user's global Python environment. `compile.py MODULE_NAME` reproduces a Lean build using the recorded local toolchain and snapshotted dependencies. The input panel/helper are archived under `inputs/` with hashes. `MANIFEST.json` enumerates the installed artifact set. The manifest and install receipt are evidence, not additional research theorems.
