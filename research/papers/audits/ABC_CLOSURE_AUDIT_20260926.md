# Audit A/B/C — 26 September 2026

## Scope and evidence

Read the main manuscripts and relevant supplement passages, inspect the substantive Lean endpoints and bridges, and trace the implemented learners/solvers to existing JSON. This is not a claim that every line of every legacy module was reviewed. No Lean rebuild or simulation was launched for this audit. Existing frozen PASS snapshots were checked against source hashes including recursive imports, rather than inferred from filenames or olean timestamps.

At the inspected snapshot, all cited roots in the main/supplement chains (A: 64, B: 51, C: 76) have a PASS snapshot containing the current complete import closure. This does not certify subsequently written, uncited modules. Full8 was interrupted; its absent final summary must not be described as PASS or as a new theorem failure. Other workers are editing concurrently: the findings below concern the inspected statements.

## A — substantive package stands, five presentation corrections remain

The inspected chain supports optimized separation, every/near-optimal starvation, the repair certificate, the exact initial slope on the stated centred family, stopped information lower bounds, and the ideal-learner results. It does not establish that the shipped numerical learner is that ideal learner.

1. **Attainment quantifier** — `paper_a.tex` abstract, contribution summary, text following `thm:optrate`, and conclusion say a learner attains exactly 1/R(b). `LeanPaperARepairGaussV1.optimal_upper` instead proves: for each epsilon in (0,R), there exists a policy family and a burn-in with rate at most 1/(R-epsilon). The burn-in may depend on epsilon. The theorem's displayed bullet is honest; the surrounding summary is stronger. Write “the optimal rate is approached arbitrarily closely by policy families in the stated class.” A single exactly attaining family requires a separate diagonal construction preserving the class, not merely taking epsilon to zero in an existential theorem. The design and Markov horizon are selected at the true world; preserve the body’s explanation that this is a pointwise oracle rate, not a uniformly terminating deployable PAC algorithm.

2. **Missing hypothesis in no-threshold proposition** — `prop:shape` assumes concavity but omits nonnegativity of J_t at a surrogate optimizer. The Lean theorem has this hypothesis. Concavity alone is insufficient: on x in [0,1], J_f=1-x and J_t=2x-1 give sacrifice x and R(b)=2b-1 for b<=1. A positive-information design exists, but small budgets do not buy positive J_t. Add J_t>=0 (as already stipulated in the earlier framework), or the precise optimizer hypothesis. Actual KL games satisfy it.

3. **Two-arm boundary** — the frontier formula includes b=0, but the stopping-rate formula dividing by b(1-b) requires 0<b<=1/2. State this separately. The eventual-budget comparison also needs feasible b' (at least 0<=b'<=1) and b'<b. Do not interpret R(0)=0 as a finite-rate result.

4. **Any-channel wording** — distinguish an abstract information inequality from the formal transcript class. The inspected protocol uses finitely many queries and positive measurable densities over real observations (plus dummy), not all singular or arbitrary observation kernels. Add this scope to the theorem/Lean attribution. Extending the measure-theoretic model is optional if the existing scope is stated accurately.

5. **Censoring contrast** — caption `fig:apaired` says a censored rule's mean and its excess are lower bounds. Each restricted mean is below its own population mean; their difference need not bound the population difference. The omitted tail terms can have either net sign. Write “paired restricted-mean contrast at B.” In these realized runs the comparator stopped, so one can discuss lower bounds on those realized differences, but that does not turn the bootstrap interval into a population uncensored lower confidence bound.

### A implementation and results

- The shipped learner retains a box, tolerance floor 1e-6 and iteration cap 80. Feasible dual lower bounds support numerical stopping within its model; they do not prove convergence to the unboxed ideal oracle. Existing limitations should remain.
- A7 panel has 600 launches, one learner censor, and a swapped-world case where the learner is much slower than uniform/oracle. This is informative negative evidence, not a universal superiority panel.
- Paired deployable panel: 7200 launches, 6258 stops, 942 censored, zero observed wrong stops. On the swapped world the surrogate is fastest in every tested cell. On the base world it can fail badly. This supports geometry-dependent failure/repair, not “geometry always wins.”
- Geometry optimization is a lower-certificate heuristic (Nelder–Mead); do not rename it the certified global optimum.
- Historical producer hashes were checked against archived sources; later main/self-check edits need not force rerunning unchanged algorithms. Retain provenance rather than replacing an old artifact's hash with today's source hash.

### A stopping point

For the present claim package: fix the five statements, maintain the ideal-versus-shipped separation, and finalize the claim-to-theorem map. Arbitrary anchor ratio rho, exact multiple-answer limits, and a deployable budgeted re-solving learner are extensions, not results already implied by replacing constants with symbols. No expensive rerun is required to make the current claims honest.

## B — endpoint is substantive; do not confuse exponents with exact constants

The inspected continuous-channel chain supports the safe-versus-identification exponent separation on the same parity experiment, with real decoder upper bounds and adaptive stopped lower bounds. The general order law requires its information comparability assumptions; it is not a universal claim for arbitrary channels or growing family size.

Three newly written files contain real additional mathematics:

- `LeanPaperBParityWorldV1`: visible-query feature lower bounds, conversion through Hellinger to chi-square, blind-query zero, and per-world decision-order bounds for the chi-square game. Its local log ends EXIT=0; it is listed in verify_all. Do not infer an exact KL leading coefficient or exact optimal sequential constant from a chi-square exponent law.
- `LeanPaperBDecisionMomentV1`: actual mixture-law second moment 18+sigma^2+6*u*h+h^2 and decision gap 12h. This closes the decision moment bridge, not every higher-order latent moment or a Hoeffding bound for unbounded Y^2.
- `LeanPaperBAssemblyV1`: normalized density/chi-square bound, explicit stopped endpoint constants, and a general fixed-finite-world order-law assembly, with distinct-pair conditions avoiding the old diagonal vacuity. Local axiom-print logs are present. Assembly and DecisionMoment were not in verify_all at inspection; include them in a frozen gate before citing them as release-certified. Local printed axioms alone are weaker provenance than a hash-bound successful gate.

### B remaining corrections and evidence

- The supplement preserves old present-tense debt statements and later superseding corrections. Its introductory warning makes the history interpretable, but a reviewer should receive a linear final proof, not reconstruct which “open” sentences are obsolete. Move historical status discussion into an archive; retain final proof and scope.
- The parity-constant quadrature script now exists. The old “script not written” debt is obsolete. The saved 10 coefficient cells and four h values show convergence, but a fixed 60001-point truncated grid does not certify quadrature or tail error. Label constants numerical; exact Taylor remainder and critical KL coefficient are separate tasks if claimed.
- The current fallback decoder experiment has 616 intervals, 11 certified cells, five identification-censored cells, and six two-sided tested-grid brackets. Simultaneous tail allocation is explicit. A bracket is for the tested decoder/grid, not the minimax sample complexity over policies.
- Use the current recorded budgets, not historical prose about ratios; e.g. 100 to 12800 is a factor 128, not 256.
- Zero errors in finite runs is not a proof of delta-correctness; the theorem supplies that guarantee under its assumptions.

### B stopping point

Gate the newly cited additions, remove obsolete supplement debt prose, and clearly separate exponent theorems, conditional critical-game limits, and numerical leading coefficients. No decoder rerun is required for the existing story. If exact/numerically certified constants become a headline, add mesh refinement, precision comparison and tail-error control; merely adding seeds will not address that issue.

## C — current core can stand; an odd-recourse draft is not yet a theorem

The inspected core is substantially beyond the older status reports: complete parity frontiers, same-law attainability, physical normalized-regret identification, typed-flow equivalence, stability, and the heterogeneous 1122/2222 region formulas. Arbitrary typed multiplicities have an exact optimization representation, not a universal closed-form solution.

One-exchange claims must retain their domain. Even-family and established small-family results are formal; repeated-type and remaining odd-band observations must not be generalized from finite LP grids.

`LeanPaperCBudgetExchangeOddV1` is a concrete example of unfinished work: its header describes recourse_one_odd, but at inspection the body ends after pattern counts, oddLaw, odd_avg and sum_pos_split. It does not yet declare oddLaw_feasible, oddT_band or recourse_one_odd. Do not close the all-band odd result from its docstring. Leave the existing theorem scope intact while the worker finishes it.

The recourse model permits one budget reveal with a common initial law and budget-specific final sets. It is not an online sequence of changing budgets, and the final sets for different budgets need not be nested. The flow is a mathematical count-state flow, not a traffic-network control theorem.

### C changes made in this audit

Edited the existing `research/papers/_tex/paper_c.tex` in place, preserving the worker's newer 2222 result:

- embedded its preamble and vector figures so the native editor can compile the current standalone file;
- added an explicit Methodology section explaining count flow, marginal bands, objective and certificates;
- clarified physical support/model scope, same-law attainment, type-count complexity and recourse timing;
- excluded an invalid robustness inference: a search's attained minimum is an upper bound on the worst-case infimum, not proof that a lower bound is loose;
- separated exact theorem curves, existing numerical LP markers and attained search witnesses;
- added four figures using existing JSON only.

The built-in editor compiler returned SUCCESS. No replacement document or shell-built PDF was made. The figure generator is `scripts/FIG_paperC_editor.py`; its manifest is `research/papers/_figures/paperC_editor_figures_manifest.json`. Nineteen checks pass; maximum saved frontier mismatch is 9.02e-17. The four figures show parity price, heterogeneous shape regimes, budget-aware/one-exchange comparisons, and perturbation stability. No new LP or simulation was run.

### C stopping point

The current scoped core does not require a new experiment. Keep unfinished odd/repeated-type recourse outside formal claims. Finish the final manuscript/supplement cross-check and release snapshot. Broader online recourse or arbitrary-multiplicity closed forms are further research, not prerequisites silently added to this paper.

## Final release checklist for all three

1. Resolve A's quantified attainment, hypothesis, boundary, protocol-scope and censoring wording above.
2. Reconcile B's final supplement with the actual completed chain; freeze and gate the new additions before extending claims.
3. Preserve C's current exact/numerical distinction; do not promote unfinished odd recourse.
4. Freeze source, figures, JSON and gate hashes for the actual submission snapshot; do not edit a running verification script.
5. Compile the final main/supplement documents and inspect cross-references/captions against the frozen evidence. C main already compiles in the native editor.

No new literature priority search was performed in this audit. The mathematical packages are coherent, but this audit is not a promise of novelty priority or publication acceptance. Uninspected code is not certified by a clean build.
