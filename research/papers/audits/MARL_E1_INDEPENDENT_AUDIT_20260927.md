# Independent audit: diagnostic v2, E1, new MARL mathematics — 27 September 2026

## Verdict

There is real progress: a fixed-schedule calibration lower bound, a pair-overlap lower bound, and a heterogeneous-receiver exchange theorem. The saved negative traffic diagnostic also survives independent reaggregation. However, E1b is NOT yet an instantiation of the new Gaussian pair-channel theorem. Four figures existing is not evidence that the theoretical and empirical chains are closed.

This audit read the producer algorithms and theorem statements/proofs, not just names or compilation counts. No experiments or Lean builds were rerun. The only new computations were raw-decision reaggregation and a 1024-state finite sum with Gaussian moments integrated analytically. No worker source, ledger, gate script, historical result, or manuscript was modified.

## 1. Critical: the pair theorem and the executable E1b use different observation laws

`work/p13_conjectures/LeanMarlPairCalibrationV1.lean`, `klq_pair`, assumes the channel `rChan P`: unit Gaussian observations whose mean changes only when the queried set contains the hidden pair. Consequently its KL is zero on queries not containing that pair. This is a valid assumed model.

`scripts/MARL_E1_controlled_calibration.py:82`, `Task.rollouts`, instead returns

    D(S,P) = e_P² - e_S²,
    e_T = sum_{j not in T} g_j x_j + beta*x_a*x_b*1[E not subset T] + sigma*xi.

Matching the mean set function does not match this observation distribution. The shared interaction term can change higher moments even when neither set contains the pair.

**Concrete counterexample, zero-based indices, using the current E1b parameters:**

    P={0,1,2,3}, S={0,1,2,4}, E={0,8};
    g_j²=1-0.1j, sigma=0.5, beta²=1.6.

Neither P nor S contains E. At the null beta=0, E[D]=-0.1 and Var(D)=9.10. At the pair world, E[D]=-0.1 but Var(D)=17.42. These moments are computed by enumerating all 2^10 sign vectors and integrating xi analytically, not by noisy sampling. E is also a genuinely repairable pair: replacing item 3 by item 8 has deficit 0.5, between epsilon=0.05 and beta²-epsilon=1.55.

Thus the distributions are distinct; the zero-KL premise fails on the actual E1b channel. Subtracting the known first-order deficit does not fix the variance discrepancy. The null world is also absent from the present E1b benchmark, although the lower bound requires correctness there.

Reproducer: `MARL_E1_CHANNEL_WITNESS_20260927.py` next to this report.

**Minimal repair:** keep two explicitly different experiments. A Gaussian shared-pair experiment may instantiate `rChan` and test the new theorem. The executable squared-loss actor is an empirical extension showing a matching *mean value structure*, without that KL lower-bound claim. For an exact theorem on the actor's raw rewards, derive its actual query distributions/KL bounds; adding Gaussian noise does not automatically erase the interaction-dependent variance.

The actor itself uses the true pair in `reward_mc` and in the residual formula. State explicitly that it is a world-specific Bayes decoder supplied to the scheduler as a black box. This need not leak the pair directly to the scheduler, but it is not one learned, world-independent unknown-pair actor.

## 2. R2 being worse at small N is an algorithm result, not an intrinsic cost of extra rights

For a fixed world class, fixed global-regret target and fixed observation budget,

    F_1(P) subset F_2(P)
    => optimal achievable risk with R=2 <= optimal achievable risk with R=1.

An R2-capable algorithm can always run the R1 algorithm. The current uniform/targeted implementation divides N over 24 candidates for R1 and 114 for R2. With MIN_PER=5 it deterministically returns P without sampling for R1 at N<120 and R2 at N<570. The later crossover is an observed calibration/search strategy tradeoff, not a minimax necessity. The original RepairCalibration docstring already makes this distinction correctly.

Keep the valid geometric-floor decomposition, but rewrite “more revision rights need more calibration” as “this full-pool calibration strategy needs more samples to exploit its larger candidate family.” Add an R2-permission/R1-policy fallback comparator if making an algorithm-selection claim. Do not use test results to choose its switching threshold.

## 3. E1b targeted is exactly uniform here; proxy failure has limited scope

The target filter is deficit < beta2_max - epsilon = 1.95. Maximum deficits are 0.9 for R1 and 1.6 for R2. Therefore all 24/24 and 114/114 candidates pass. Uniform and targeted are the same fixed-allocation algorithm with different random draws. The report's “almost every” should be “every”; curve differences cannot support a targeting benefit.

Keep this as a negative control or add a separately specified regime where pruning actually occurs and report pool sizes. Never select a new regime because it creates the preferred ranking.

The proxy estimates singleton mean gains although the other methods are handed exact g². Its failure supports failure of this mean-only score policy. It is not an impossibility theorem for all algorithms using those raw singleton observations: variance and other distributional information can expose interactions. E1b must not inherit the needle channel's zero-information statement.

## 4. Student-t does not certify the adaptive rule

The report correctly admits that the Bonferroni-t rule is heuristic. Preserve that admission in figures/manuscript. Paired squared-loss rewards are mixtures, not normal samples; adaptive sample counts and repeated elimination introduce further selection issues.

At lines 170–179 adaptive elimination can still occur at two samples per candidate. MIN_PER=5 only filters the final choice. The elimination radius uses plug-in variance without a valid time-uniform guarantee. A final Student-t check cannot restore candidates eliminated prematurely. This is an algorithmic weakness, not proof that the plotted average gains are fabricated.

Minimum correction before a fresh run: do not eliminate before the declared minimum; either use a proved confidence sequence for the stated reward law or label the adaptive curve exploratory. Keep the fixed Gaussian block-test experiment as the certified component. Record actual query counts, candidate counts and per-instance gains. One paired query uses two actor evaluations: distinguish query units from physical rollout evaluations.

## 5. What the new Lean files establish

### CalibrationGap

The fixed deterministic-schedule result is substantive. Under its needle-class/correctness/separation assumptions, the lower and upper costs scale as M log(M/alpha)/beta² (with the usual integer-rounding/regime qualifications). The asymptotic ratio of the displayed bounds is 4/(1-alpha).

For adaptive policies, `own_world_sum` sums E_T[N_T] over DIFFERENT worlds. It is not the total cost within one world. Do not convert it into an adaptive M log M lower bound. The module's own limitations are clear about the missing adaptive upper theorem; the latest worker report correctly narrows the fixed-schedule claim.

### PairCalibration

The code explicitly addresses shared coverage. The necessary inequality is

    |AmbP| D_alpha <= (beta²/2) sum_q E_0[N_q] cov(q),

and for legal repairs cov(q)<=Rk. A constructive fixed schedule tests every reachable set; the output selects the largest-score fired set. The model has one active pair per world, not arbitrary simultaneous pair interactions.

A smaller lower bound does NOT prove an attainable saving of k or Rk. Counts |AmbP| and |Amb| also describe different classes. Leave tightness open. If proceeding, start from the coverage LP with one constraint per ambiguous pair, then verify which additional constraints are required to distinguish worlds with incompatible acceptable outputs. Generic overlap-aware sensing is existing combinatorial pure-exploration machinery, not a new discovery by itself.

### BlockFrontier

This is a real partition-by-receiver extension for coupled set values, conditional on ScoreLocal and per-block top-score prefixes. It does not include byte feasibility. A profile constructed by its exchange path may exceed the transport byte cap. It also does not show that all per-receiver top-score sets come from one common broadcast order; that compatibility must be checked or assumed. `ProfileSearch` still gives the evaluator/search bound on an explicitly byte-feasible candidate set.

### Starvation

The positive-but-small allocation law assumes a bound on allocation to an informative repair. The symmetric-design cost law is also conditional on the symmetric design. Neither proves that optimizing a surrogate forces that allocation. Keep the limited A-role statement; do not promote it into Paper A's full optimized-starvation mechanism.

### A cheap actor realization already available

For E1b's mean value,

    f(A union {i})-f(A) = g_i² + beta² * 1[i in E and E\{i} subset A].

Thus ScoreLocal(f,g²,beta²) follows directly, and f is monotone. Formalizing this is small and useful; it does not solve the channel mismatch. With beta²=1.6 the score-local constant is not small relative to the score gaps, so numerical usefulness of the resulting bound must be reported, not presumed. A single-receiver actor is not yet a heterogeneous team-value realization.

## 6. E1a/two-stage numerical audit

E1 v2 source hash matches the saved JSON; the superseded v1 hash differs, as expected. The self-check validates the mean reward formula on six subsets; it does not validate confidence coverage or acquisition optimality.

Two-stage source hash also matches. Recomputed from saved rows: first tested M beating the fixed-schedule lower bound is 256 at alpha=.05 and 1024 at alpha=.01. Maximum tested ratio to the null-world lower bound is 3.5384. These are finite-grid results, not an asymptotic constant-factor theorem.

**Decoder wording mismatch:** `MARL_E1a_two_stage.py` promises “unique fired repair, otherwise P”, but its null error is probability of ANY firing. For that declared decoder the exact null error is M*p*(1-p)^(M-1), not 1-(1-p)^M. The latter is conservative, so it does not invalidate feasibility or the observed saving. The clean fix is to specify the Lean first-fired decoder and use the worst-position needle for its worst-world error, or to implement and evaluate the unique-fired decoder literally. The current Monte Carlo duplicates the event formula; it does not independently execute the declared decoder.

For E1a, nominal grid N is not actual allocated cost: each arm receives floor(N/M) samples; the uniform-all-k-sets experiment also allocates to the free prefix dummy. Record paid non-dummy counts. Threshold crossing from 4000 trials is an estimate, not a certified sample-complexity bracket. The statement “linear in M” is too strong: beta changes with R in this panel and fixed block cost also has a log(M/alpha) factor.

## 7. Figures

Read the complete producer `scripts/MARL_make_figures.py` and its SOURCES.json.

- Fig2 E1a draws one lower-bound line from the FIRST setting against all curves, although beta changes between R1 and R2. Use per-setting bounds or normalize by beta² as well, and retain the M dependence.
- Fig2/4 label nominal N as rollouts; replace with clearly defined allotted paired-query budget or actual counts.
- Fig4 uniform/targeted are duplicate algorithms in this regime. Label as a negative control; no claimed acquisition benefit from their separation.
- Fig1 intentionally selects the maximum-gain example. Label it “best-gain illustration”, not representative traffic improvement. It is an oracle adjacency matrix, not a scene rollout/video.
- Fig3 correctly marks the previously inspected pilot test panel as development data and labels oracle rows. Add uncertainty at the episode level if making comparative claims. It is not a new learned-MARL success result.

## 8. Diagnostic v2 remains negative; what assets might still help

Independent reaggregation of 13,056 saved selections (17 models x 96 validation groups x 8 cap/policy choices) exactly reproduced reported mean gains. No byte-cap or R1 violations were found. Three producer hashes and the decisions hash match.

At +28B public MLP is -1.49 to -0.17; history MLP is -0.15 to +0.78; joint-only privileged control is +7.09 to +7.98. The history seed0 mean in prose should be +0.1875, not +0.10. Joint-only headway16 ranges -0.5 to +1.292, not only up to +0.8. These small reporting corrections do not alter the negative legal-selector conclusion.

Epoch/lambda selection optimizes repair_R1; direct receives its own threshold but shares that selected critic. Call it a shared-critic comparator, not an independently tuned strongest direct baseline. Validation has only two traffic seed IDs and has been inspected before. Positive privileged controls are evidence for a representation/information hypothesis, not proof of irreducible lack of legal information.

Useful assets, without restarting a broad research program:

- C/Marl block geometry: state the exact feasible profile and revision constraints, including the byte-cap limitation.
- B protocol/change-of-measure: analyze the actual permitted observation channel; do not transfer KL from a matching mean.
- A starvation: quantify acquisition only after establishing informative queries and an actual allocation bound.
- FunctionalCertificateLifetime and RevisionAuditBridge: reuse deterministic drift/margin transfer; neither supplies a probabilistic coverage certificate for free.

If a later authorized learning test is needed, predict actor responses using existing privileged action labels at training time and legal inputs at inference. This is a hypothesis, not a guaranteed rescue. A naive factorization E[value|z,S]=sum_a p(a|z,S)Q(z,a) can fail because hidden state affects both selected action and rollout value; prove sufficiency/conditional independence or preserve that dependence. Do not open another traffic-training branch solely because privileged actions help.

## 9. Closest literature check before calling this an analysis-paper novelty

Malloy and Nowak, *Sequential Testing for Sparse Recovery*, already study fixed versus sequential sensing and the logarithmic dimension penalty, with explicit component-wise/asymptotic assumptions. This is relevant machinery/positioning, not proof that their theorem subsumes every present statement. Read sections II–IV, including those restrictions:
https://nowak.ece.wisc.edu/SeqTest.pdf

Du, Kuroki and Chen, *Combinatorial Pure Exploration with Full-Bandit or Partial Linear Feedback* (AAAI 2021), study combinatorial actions, shared unknown parameters and limited feedback. Pair incidence features place the Gaussian shared-pair model close to this framework, although noise assumptions and exact tasks require comparison:
https://ojs.aaai.org/index.php/AAAI/article/view/16892

Therefore neither “adaptivity saves log M” nor “one query informs many pairs” should become the sole new headline. The defensible candidate is the communication-constrained revision geometry linked to calibration requirements, plus an honest executable-model/traffic boundary. Publication strength is not guaranteed just by relabeling negative learned results as an analysis paper.

## 10. Minimal completion order

1. Fix the claim/channel mapping and decoder description in this report's items 1–6 before inserting results into the manuscript. This does not require waiting for gate.
2. Keep immutable current artifacts. Add the finite witness as a regression check. Freeze any corrected producer before rerunning only affected small panels.
3. Formalize the simple mean-value actor realization; report actual bound size. Keep probability-of-coverage and byte-cap compatibility explicit if unfinished.
4. Correct figures from existing data: duplicate algorithms, lower-bound normalization, nominal/actual cost, example selection and uncertainty.
5. Treat pair tightness/adaptive Lean upper/budget-uniform tables as optional extensions unless the manuscript headline requires them. They do not repair the current observation-law mismatch.
6. Do not claim a learned MARL algorithm beats baselines. Any newly authorized learning curve is a distinct preregistered test and must be judged by its own criteria, without peeking or changing producer mid-run.

## Running-process check appended during this audit

At about 21:34 local time, B1 `b1_lc_20260927_201443` had completed all four collector shards (960 records total) and four replay shards. Training parent PID13666 and workers13675–13678 were active for about73 minutes. Forty jobs were scheduled; no completed-job line or report had yet appeared. `executor.map` returns in submission order, so no line does not prove no later job has finished. No epoch telemetry or intermediate model/checkpoint is written by this driver; it discards model blobs and writes the report only at the end. Do not kill/restart casually.

The machine has16GiB physical RAM. Swap used was16851.5MiB; in a two-second sample vm_stat showed22131 swap-in pages and25628 swap-out pages, page size16KiB (about173MiB/s in and200MiB/s out). This is active swapping, not just a historical swap allocation; 33% reported free-memory metric does not establish a comfortable working set. No process was paused/killed, and no producer was edited.

Gate smokeMARL17 had58 completed exit files, all0, out of the reported146; latest started log was LeanPaperBProtocolV1. No final gate verdict inferred.
