# CIG-AMF redesign — Lean proof/falsification plan

## Baseline that must remain immutable

The authoritative P12 baseline has no active `sorry/admit/user axiom`.  In
particular it already closes RU1–RU5, RI1–RI2, D6 S1, D6 Q1–Q4 (and Q5
conditional), QN1–QN4, and the covariance reversal witness.  Do not weaken or
restate these as new contributions.

## Why there are `sorry`s now

High-upside conjectures live only under `work/p13_conjectures/`.  They are
**quarantined** and excluded from the active compile ledger.  The point is to
state risky targets early without contaminating the certified baseline.
Experiments/exhaustive search can kill them; only Lean proof can promote them.

## P13-1 D6 half-factor — highest priority

File: `LeanD6DecisionHalfFactorConjecture.lean`.

Change from P12: the active theorem has additive decision term `2*n*delta`.
The conjecture asks for `n*delta/2`, a factor-four improvement.  P12 S1 says
only the approximation coefficient `n*delta` is sharp; it does **not** prove the
decision-transfer factor.

Before proof engineering:

1. run exact integer enumeration (`run_d6_exact_small_search.py`);
2. run counterexample-directed optimizer (`run_d6_counterexample_optimizer.py`);
3. search q-skewed and m=3/4 cases;
4. if any ratio > 1/2, mark conjecture false and store minimal witness;
5. if it survives, inspect the proof of `D6_product_topC_compression_decision_regret` and locate where two triangle inequalities create factor 2.

Proof routes to try: exploit Top-C optimality, cancellation between the two
transfer inequalities, or a direct comparison of selected-vs-optimal residual
oscillations.  Do not add assumptions merely to rescue the 1/2 constant.

## P13-2 unknown-variance robustness

File: `LeanFunctionalUnknownVarianceConjecture.lean`.

Current status: the general deterministic robustness theorem plus its D and
stable-extrema-C specializations are written with no `sorry` and freshly
compiled with exit 0 under the pinned Lean/Mathlib runtime (warnings only).
They do not prove that pilot,
shrinkage, or anytime acquisition beats uniform; those are empirical method
comparisons.

P12 covariance theory assumes the covariance/variance object is given.  The new
claim quantifies the price of replacing sigma by learned sigma-hat.  Prove the
deterministic relative-error lemma first.  Probability/time-uniform confidence
is a separate wrapper; do not mix it into the algebraic core.

After the deterministic lemma, specialize twice:

- D: coefficient vector from the signed functional;
- stable-extrema C: contrast `e_max-e_min` under a premise that extrema identity
  is fixed.

Then add a *separate* selection-error theorem if useful.  This separation is
important because the post-fix experiment showed that variance learning and
extrema identification are distinct bottlenecks.

## P13-3 response/reference budget split

File: `LeanReferenceResponseBudgetConjecture.lean`.

New bridge: if statistical response radius is `A/sqrt(n_Q)` and reference
radius is `B/sqrt(n_kappa)`, total budget `N=n_Q+n_kappa` has a continuous
2/3-power optimum.  First prove the calculus/AM-GM statement.  Only after that,
connect the resulting radius to the existing same-target RU4/RU5 + Top-K margin
constant.  Check the exact P12 Top-K constant before freezing the final sample
complexity corollary.

`LeanReferenceResponseTopKBudgetConjecture.lean` already compiles as a
conditional bridge to `A9_uniform_topK_margin`. It deliberately does not prove
the 2/3-power optimum or a simultaneous statistical coverage guarantee. The
two calculus targets in `LeanReferenceResponseBudgetConjecture.lean` remain
explicit quarantined `sorry`s.

## P13-4 Structural approximate route

Only the scaled all-optimal-extension candidate is alive.  The scratch file is
intentionally a shell: first port the **exact** discovery definitions into Lean,
then replace the placeholders.  Do not reopen adjacent-pair, submodular,
supermodular, M-convex, monotone, or old deficit iff candidates.

The matching falsifier is `scripts/run_structural_counterexample_search.py`.
Its exact binary m=3 pass checked 1,544 worlds with no positive candidate
violation; directed m=4/5/6 search remains available. Survival is not proof and
does not promote the placeholder Lean theorem.

## Margin shielding / Omni zero-regret

First attempt to derive it as a corollary of existing perturbation/Top-K margin
theorems.  If it collapses, record `COLLAPSES_TO_EXISTING_THEOREM`; do not add a
new headline theorem.  The experiment now reports empirical margin/order/tie
causes to guide this check.

## Promotion gate

A P13 file can move to P12 only when:

- no `sorry`, `admit`, or new axiom;
- exact theorem statement matches experimental semantics;
- pinned Lean/Mathlib compilation exit 0;
- counterexample registry updated;
- dependency graph and theorem ledger updated.
# D6 half-factor proof-entry gate

Do not promote or seriously engineer the quarantined half-factor conjecture
until the following falsification campaigns all complete without a witness:

1. exact m=3 binary coordinate-specific q-grid {1/4,1/2,3/4};
2. deep m=3 alphabet 2/3, all k and uniform/random/skewed/boundary q;
3. deep m=4 campaign;
4. at least one directed m=5 binary campaign;
5. structured local perturbation of the current J=0.46875 witness.

If the gate opens, inspect the frozen D6 proof for constant loss using: direct
selected-vs-optimal residual comparison; surrogate Top-C optimality; and
oscillation centering rather than two separate sup-norm transfers.  Do not add
assumptions to force the factor.  Search and proof analysis form one loop.
