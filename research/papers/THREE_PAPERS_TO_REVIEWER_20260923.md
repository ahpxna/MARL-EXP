# Three-paper completion specification — 23 September 2026

This is a complete work order, not another short batch. Work in `/Users/phanan/cig-amf-main`. Finish the mathematical endpoints, connect them to the algorithms and evidence, and assemble three coherent manuscripts for a real reviewer. Do not create new research branches merely to postpone these endpoints. Do not stop after compiling the next wrapper.

## 0. Status and scope to carry forward

The earlier 12:39 build snapshot has been superseded. The worker reports that the five endgame modules subsequently built cleanly and were then changed only in docstrings. A source newer than an olean is now a freshness discrepancy to resolve in the final frozen build, not evidence that the old elaboration errors remain. Do not repeat the 10–9–5 error table.

The worker has written `LeanPaperAGaussianKLV1`, `LeanPaperBParityNormV1`, `LeanPaperCParityBaselineV1`, `LeanPaperCBaselineAttainV1`, `LeanPaperCEvenTotalV1`, and `LeanPaperCEvenRankSumV1`. Treat these as written, pending their declared verification gate; do not reimplement them. `gFamily_abs_sum` already supplies the normalizer. `CFlowBandJoin`, the even/odd zero-band witnesses, and the window computations already exist. Use them.

Remaining construction obligations are the even endpoint law, the odd endpoint law, and the operational B protocol certificate. A7 also still has a substantive operational proof obligation: obtaining its accumulation and expected stopping bounds for the actual learner. Merely narrowing the description of a fixed numerical floor does not discharge that obligation.

No experiments or Lean builds were launched for this specification. Saved B decoder counts were reanalysed, without generating observations. Two new Lean files are proof drafts, not compiled results.

### Files delivered with this specification

1. `work/p13_conjectures/LeanPaperCRelabelBandJoinV1.lean`: derives a general nonzero item band from explicit weight-class prefix counts, preserves every expected regret, and pushes the law onto all permutations. Worker: compile, resolve elaboration against current APIs, then use it for BOTH endpoint laws.
2. `work/p13_conjectures/LeanPaperACertificatePerturbationV1.lean`: bounds estimate and effective-count errors uniformly over boxed alternatives, on the actual `PaperA7Stream.Qstat`. Worker: compile, then take infima and join tracking/selection; do not mistake this deterministic result for a probability or stopping theorem.
3. `scripts/ANALYSE_paperB_decoder_grid_v2.py`: fixes two-sided multiple testing and nonmonotone decoder-budget interpretation using existing `bad/reps` counts. This is a postprocessor, not a sampler. Its deterministic counterexample checks passed.
4. `research/unified_20260919/paperB_decoder_grid_v2_20260923.json`: output of that postprocessor. Its input SHA and analysis SHA are stored. This version has 11 upper-certified panels, 6 panels with a failed grid prefix plus an upper certificate, and 5 without an upper certificate. The identification slope interval at m=3 includes both -4 and -2.
5. `research/papers/POST_RUN_A_CLAIM_CORRECTIONS_20260923.patch` plus its `.bases.json`: prepared wording corrections for the two live A producers, NOT applied while they run. The mechanism header still describes a union of single half-spaces although the code correctly uses an intersection for each pair. A7 also still says a requested floor implies a positive floor on actual error and automatically yields a finite-epsilon rate. The patch corrects these claims, the documented variance factor and the modulus; it changes no sampling, optimization or stopping calculations. Worker: after both relevant jobs finish, compare base hashes, run `git apply --check`, inspect the diff, and then apply/adapt it. Preserve the launch source and annotate existing run metadata instead of rerunning sampling just for changed wording.

Do not overwrite historical JSON. Do not modify a script while its process is running. Final compilation should use a frozen copy of the runner AND the Lean sources/dependencies, with exit status and hashes for each module. Seeing the final totals of a previously modified shell script is not a proof that every preceding command used the intended bytes.

## 1. One scientific question and a finite destination for each paper

| Paper | Central question | Required result package | What is not the contribution |
|---|---|---|---|
| A | When does a cheap surrogate lead to the wrong evidence allocation for the actual compression decision? | Realizable response/KL model; separation after optimizing both designs, including unit variance; failure of surrogate-optimal designs; explicit cost of repair; attainability of the true information objective by a specified learner | Inventing confidence sequences, Gaussian likelihoods, or Track-and-Stop |
| B | How much easier can a safe decision be than identifying the hidden world, under the same restricted observation channel? | Actual safe sets from compression geometry; order law on a specified query class; continuous adaptive transcript lower bound; a matching decoder; explicit safe-versus-identification separation in one experiment | Generic “decide without identifying,” an unnormalized cube identity, or a fitted slope |
| C | What is the price of controlling each item's retention probability when one randomized ranking must serve every budget? | Actual all-ranking laws; zero-band values; an all-size even frontier and odd breakpoint; band-preserving ranking/flow equivalence; stability for actual normalized regret | Generic symmetry averaging, flow decomposition, or counting a few LP sizes |

These are three related papers about the price of a constraint: evidence geometry (A), observation/answer geometry (B), and cross-budget retention geometry (C). Share definitions and cite the common foundation, but give each theorem one primary owner. Do not present old Functional, D6, Support, Query, MASTER, and Structural histories as six parallel introductions. Old results enter only where they are needed by one of these three arguments.

The criteria below define completion of the current scientific program. They are not an acceptance guarantee. If a theorem fails, record the counterexample and replace that theorem's exact scope, not its meaning through a renamed assumption.

## 2. Paper A — close the actual decision and operational chain

### A.1 Freeze the statistical model and alternative set

Write the model once: finite cells e; known positive variances v_e; centered response tables in the chosen parameter class; observations Y ~ N(theta_e,v_e); each query costs one observation. Specify whether the parameter class is boxed and at what B. The two-answer eight-cell experiment and the `thetaC` family with 4+2r cells are DIFFERENT model instances. Do not move constants between them.

For each retained answer T define

    Bad_epsilon(T) = {lambda in Theta : L_lambda(T) > min_S L_lambda(S)+epsilon}.
    J_T(w,theta) = inf_{lambda in Bad_epsilon(T)} sum_e w_e KL(P_theta^e,P_lambda^e).
    Gamma_T(theta) = sup_{w in simplex} J_T(w,theta).
    Gamma_comp(theta) = max_{T safe at theta} Gamma_T(theta).

Use the existing actual-response bridge and strict-alternative theorem. The KL file must prove finiteness as well as the `toReal` equality, for ALL centered theta/lambda, ALL cells, and positive variance. Do not let `toReal(top)=0` silently erase an infinite divergence. Compile `gaussianKLIdentification_holds` and its unconditional separation consequences.

A regional QP represents the closure of a strict alternative. State and use the density/approximation theorem that makes the infima equal. Do not replace `>` by `>=` without it, especially at the d=1/2 boundary and at zero allocation weights.

### A.2 Deliver the headline theorem on the centered family

On the present normalization the target bounds are

    9 / [128(4+2rM)] <= Gamma_true <= 1/(8rM),
    Gamma_proxy = 9/512,
    4/(4+2rM) <= Gamma_true/Gamma_proxy <= 64/(9rM).

Check these against the final declaration before quoting constants. They must concern the same centered class and the strict actual alternatives.

At M=1, r -> infinity proves no uniform constant-factor approximation AFTER optimizing both games. State this quantifier explicitly. Then instantiate the stronger design failure: EVERY exact proxy optimizer has zero true information, while Gamma_true is positive. This is not the claim that a forced-exploration algorithm never stops.

Keep the repair result honest. A certificate at one design is not a characterization of all optimal designs. The rational M=256 witness already refutes a blanket “repair never fires there” statement. If the usable theorem is a sacrifice frontier for (1-beta)w_proxy+beta*w_cert, state its two bounds and its actual scope. A negative result about proxy-optimal certification plus a constructive sacrifice law is scientifically coherent; do not invent an optimality-level positive repair theorem.

### A.3 Complete correctness on the actual infinite potential process

Define the predictable query rule and the infinite potential observation process first. Stopping selects a prefix of that process. The code's finite budget is a censoring mechanism; it is not the mathematical hitting time.

Use the true null residual at EVERY candidate lambda:

    S_e(t;lambda) = N_e(t) * (muHat_e(t)-lambda_e) / sqrt(v_e).

The shortcut S=N*muHat/sqrt(v) is valid only at lambda=0. Existing `Qstat` already uses the correct residual. Use its closed-form identity instead of re-proving a second mixture integral:

    Q_t(lambda) = 1/2 sum_e N_e(t)^2/[(a+N_e(t))v_e] * (muHat_e-lambda_e)^2,
    log M_t(lambda) = Q_t(lambda) - 1/2 sum_e log(1+N_e(t)/a).

For each true theta, instantiate the adaptive martingale and Ville result to obtain simultaneous coverage. Define Z_t(T)=inf over actual bad alternatives of Q_t. The implementation computes a lower certificate Zlo_t(T). Prove pointwise Zlo_t(T)<=Z_t(T). Then the stopping test Zlo_t(T)>b_t(alpha) implies correctness on the coverage event. No concentration assumption about the allocation oracle is needed for this correctness implication.

This is also why failed numerical lower solves must return a conservative zero/no-stop, never drop a region from the lower envelope. Primal feasibility with tolerance 1e-8 is not an EXACT feasible alternative: for exact certification, repair the witness into the region, evaluate rationally/outwardly, or subtract a proved feasibility-error bound. Label ordinary floating certificates as numerical certificates if that final arithmetic protection is absent.

### A.4 Close information accumulation — two numerical errors, not one

Keep these separate:

    epsilon_s: suboptimality of the allocation oracle at the current estimate;
    nu_t: loss of the stopping lower certificate relative to exact Z_t.

An accurate allocation oracle does not imply a tight stopping certificate. A valid but always-zero stopping lower bound is perfectly correct and never stops. The finite cap in the regional stopping-dual solver must therefore also be analysed or replaced by certified refinement.

On a good window [n,t), prove in this order:

1. Confidence radius and predictable forced exploration: N_e(s) has the lower growth promised by the tracker; the actual r_s tends to zero. Initialization counts and the tracking deficit must be included.
2. Selection: the ordered plausible-optimum rule retains every true optimal answer. With shrinking confidence/oracle errors, finitely many answers, and the required local continuity, the selected answer eventually equals the FIRST true information-optimal answer. If using a different sticky rule, prove its version of this statement. “Any safe answer remains plausible” does not select the answer of best information value.
3. Oracle perturbation, after stabilization:

       J_Tdagger(w_s,theta) >= Gamma_comp(theta) - 2L r_s - epsilon_s.

   This follows by moving J to the estimate, applying the certified oracle lower/upper gap, and moving Gamma back. Use the variance-aware L on the actual boxed class.
4. Forced mixture: J is concave in w and nonnegative, so the exploration mixture costs at most rho_s Gamma_comp in this lower bound.
5. Tracking: compare N(t) with sum_{s<t} w_s. Bound the induced information error using the actual bounded per-cell KL on the box. Use distance to the optimal set when the oracle is set-valued; do not demand convergence to one optimizer vector.
6. Concavity gives a lower bound on t J_Tdagger(N(t)/t,theta) from the sum of the per-round lower bounds. The pre-window rounds contribute a controlled n/t loss, not an omitted term.
7. Move from this linear-count energy to the implemented statistic, using the new `LeanPaperACertificatePerturbationV1`.

The new draft proves, for every boxed alternative lambda and |muHat-theta|<=r,

    Q_t(lambda) >= sum_e N_e(theta_e-lambda_e)^2/(2v_e) - R_t,
    R_t = sum_e [N_e r(4B+r)+a(2B+r)^2]/(2v_e).

It comes from the exact identity N-N^2/(a+N)=aN/(a+N) in [0,a] and a difference-of-squares bound. If v_e>=v_min and sum_e N_e=t, then

    R_t/t <= r(4B+r)/(2v_min) + a d(2B+r)^2/(2v_min t).

This bound is UNIFORM in lambda, so it survives the infimum over the actual alternatives. Finally subtract nu_t for the computed lower certificate. Obtain a statement about Zlo_t, not an unrelated additive statistic:

    Zlo_t(Tdagger)/t >= Gamma_comp - tracking/selection/window errors - R_t/t - nu_t/t.

Worker tasks after compiling the new draft: prove the displayed v_min corollary; use `le_csInf` with nonempty alternatives and bounded-below energy; instantiate the count/selection bounds on the actual process; derive the real numerical or theoretical certificate gap. Do not feed this entire accumulation inequality back as a new named hypothesis.

### A.5 Choose and prove the precision contract

There are two honest endpoints, and the document must distinguish them.

**Exact asymptotic theorem.** Specify an ideal certified-refinement implementation with epsilon_s -> 0 and nu_t/t -> 0. A numerical iteration limit may cause a refresh to return “unresolved”; it must not certify a tolerance it missed. Explain the fallback allocation and prove its contribution is negligible, or continue refinement until the stated certificate exists. Increasing an iteration counter alone does not prove solver convergence.

**Finite-precision implementation.** The current 1e-6 floor/80-iteration cap is a scoped implementation. Recorded gaps on finitely many runs do not prove a uniform bound on all future gaps. To claim a rate with Gamma-C epsilon in the denominator, prove a uniform/certified error contract, answer stability under that contract, and the stopping-gap bound. Require Gamma-C epsilon>0. Without those steps, report finite-panel performance only.

The newest source says “the finite-epsilon form transfers”; treat that as a TARGET, not an established consequence of recording gaps. Likewise, a requested tolerance bounded below does not mathematically imply the solver's ACTUAL error is bounded below; the correct statement is that the schedule does not guarantee vanishing error.

### A.6 Finish the tail and expectation without discarding infinity

The actual tracking-confidence process should give P(good_s fails)<=s^-4. With n=ceil(sqrt(t)), a union bound over [n,t) gives O(t^-3/2). Use the deterministic accumulated-information bound to show that after a deterministic threshold t_alpha(eta), failure to stop implies a bad window (plus any separately controlled solver failure event).

Then apply the layer-cake identity to tau in Nat-infinity:

    E tau = sum_{t>=0} P(tau>t) <= t_alpha + C sum_{t>=t_alpha} t^-3/2 < infinity.

Constants must be controlled independently of alpha near zero. It is not enough to prove “for each alpha some finite C_alpha exists.” Combine the upper bound with the information lower bound for the SAME model and answer criterion. For the centered family, unique correctness permits its corresponding lower-bound specialization; do not silently replace a multiple-answer lower bound by a fixed-answer one on a general model.

Final A theorem has a concrete law, predictable policy, actual bad set, untruncated hitting time, alpha-correctness, finite expectation, and the claimed characteristic rate. It should not still take `hUpper`, `hLower`, `hfinite`, `hgood` or `hinit` that assert the conclusion's substantive parts.

## 3. Paper B — construct the operational certificate

### B.1 Keep the two observation models separate

The raw-F four-world Gaussian mixture with linear probes and the m-world parity membership channel are different experiments. They may instantiate one abstract order principle, but a density bound from one cannot automatically be used for the other's decoder.

For the parity membership experiment use

    Y_j = v(j,w) product_{ell<=j} Z_ell + (h/j) sum_{ell<=j} Z_ell + xi,
    v(j,w)=-1 iff j=w,  xi~N(0,sigma^2), Z uniform signs.

The normalized characteristic-function gap is

    phi_+(t)-phi_-(t) = 2 i^(j+1) sin(t) sin(th/j)^j exp(-sigma^2 t^2/2).

Compile `LeanPaperBParityNormV1` and connect it to the actual observation law, not just a new definition of the right-hand side. The old cube sum identity remains useful; it needs the factor 2^-j and the independent Gaussian factor.

### B.2 Build one Experiment for both tasks

Use one query set, known h/sigma, observation kernels, cost per query, hidden world set, and allowable policy class. Include independent algorithmic randomization if the claim is randomized/adaptive. Queries are chosen from past history; the returned answer is measurable at stopping. `allowed := True` on functions of a future stream is invalid.

Take the loss from the actual `selectedRadius` construction. For the tip family, prove the safe answer set is exactly [m] minus {w} in the claimed tolerance regime. Identification still returns w. Both costs count ALL queried observations.

Use the law of the STOPPED TRANSCRIPT when instantiating the KL fields. The KL of entire infinite potential observation streams can be infinite even for a finite-cost algorithm and is the wrong object.

### B.3 Per-query information and stopped transcript

For each relevant pair prove, uniformly over allowed queries,

    KL(K_theta(q),K_lambda(q)) <= C h^(2s).

For the raw-F linear-probe model use the actual iterated-difference density and a positive Gaussian lower envelope. The route is KL <= chi-square <= h^(2s) integral(B_s^2/ell). Bounds on an attained Hellinger value or a local search supremum do not supply this KL upper bound.

For the parity experiment repeat/instantiate the density argument on THAT mixture. At safe order s=1 all finitely many query orders j>=1 give O(h^2) for 0<h<=1. For the identification pair {m-1,m}, queries j<=m-2 have identical laws, query m-1 has order m-1, and query m is no more informative in h-order. Constants can depend on fixed m.

Use the existing one-round kernel chain rule, integrate the conditional per-query bound under the actual history law, and induct on t wedge tau:

    KL(P_theta^(t wedge tau),P_lambda^(t wedge tau))
      <= C h^(2s) E_theta[t wedge tau].

The policy kernel is identical at a given history under both worlds; it cancels conditional on that history, not after pretending the adaptive observations are iid. Extend to the stopped transcript with the required limit/data-processing theorem. If E tau is infinite, the desired cost lower bound is automatic; handle the finite case to justify integrability. This is how `HardPairCertificate.stopped_information` gets proved.

### B.4 Derive the SAFE hard pair from correctness, not from a fixed arbitrary pair

In the coSafe family any two worlds may share a safe answer, so a fixed two-point lower bound is insufficient for the safe task. Use the output distribution:

1. Fix w0. Correctness implies P_w0(answer=w0)<=delta.
2. Among v != w0 choose one with p=P_w0(answer=v)>=(1-delta)/(m-1).
3. In world v, q=P_v(answer=v)<=delta, because that answer is unsafe there.
4. Data processing gives transcript KL >= binary_kl(p,q).
5. Use binary entropy <= log 2:

       binary_kl(p,q) >= p log(1/q)-log 2
                       >= [(1-delta)/(m-1)] log(1/delta)-log 2.

For example, delta <= min(1/(2m), 2^(-4(m-1))) yields a lower bound
`log(1/delta)/(4(m-1))`. This is deliberately conservative but uniform in delta on the stated interval. Handle q=0 with extended KL, rather than taking log 0 as a real expression. The pair may depend on the algorithm; the constants and per-query bound may not.

For identification use the fixed pair m-1,m and the event “guess=m-1.” Its probability is at least 1-delta in the first world and at most delta in the second, yielding a constant times log(1/delta). This discharges `find_pair` for each task with the appropriate information order.

### B.5 Actual decoder and its cost

At a fixed frequency t0=1 use cos(Y) for odd j and sin(Y) for even j. These are bounded in [-1,1]. Their two means have gap

    g_j(h)=2 |sin(1)| sin(h/j)^j exp(-sigma^2/2).

For 0<h<=h0<=1, the existing sine lower bound gives g_j(h)>=c_j h^j with explicit positive c_j. Threshold at the midpoint; Hoeffding gives error <= exp(-N g_j(h)^2/8). Use the theorem already found in the pinned library, not the old claim that only Chebyshev is available.

Safe decoder: query j=1; output 2 if it names world 1, otherwise output 1. Identification decoder: test queries 1 through m-1; return the unique positive name, or m if none; designate a measurable fallback when tests disagree. On the event that all tests are correct this decoder is correct. Allocate delta/(m-1) to each test and sum query counts. Equal N or query-specific N_j are both valid designs, but the implementation and theorem must name the same one.

Use ceilings explicitly and absorb their finite total into a constant only after imposing the stated h0/delta0. Then construct two `UniformProtocolCertificate`s for ONE Experiment:

    safe:     s=1,       N_safe ~ h^-2 log(1/delta),
    identify: s=m-1,     N_id   ~ h^(-2(m-1)) log(1/delta).

Instantiate `tip_finish`. It must not still receive these two certificates as unproved parameters. Uniformity is in h and delta with fixed m, not in a simultaneous m,h limit.

### B.6 The repaired experimental ladder still needs this correction

Adding CP lower bounds was necessary, but the current producer gives EACH lower and upper tail error 0.05/J. Used jointly this only gives a Bonferroni failure bound 0.10. Use 0.05/(2J) for each tail, or another explicitly split total budget.

Also, a fixed decoder's true error is not automatically monotone in N. A lower error bound above delta at N=40 does not exclude success at N=20. The new postprocessor uses only a CONTIGUOUS prefix of tested budgets all proved to fail. It bounds the first successful TESTED budget. It does not exclude untested integers and does not bound the minimum over all possible decoders.

Worker: point B's figure producer at the new analysis artifact or port its mathematics into the main producer after the current run finishes. Keep the meanings distinct: upper-certified achieved budget; finite-grid first-success bracket; minimax complexity theorem. A slope interval over grid budgets is not a confidence interval for an asymptotic exponent without an additional finite-h approximation argument.

## 4. Paper C — construct the two endpoint laws once

### C.1 Inputs already available

Use `insRanking`, `insMixture_free_value`, `insMixtureEven_free_value`, `mixCount`, `mixCountEven`, `O1_odd`, `O1_even`, `permOfCountEq`, `rankOf_permOfCountEq`, `regret_relabel_sum`, and `pushLaw` from the existing files. The exact window calculations and zero-band laws are finished work, not tasks to repeat.

Compile the new `LeanPaperCRelabelBandJoinV1`. It proves

    P_sym(i in prefix_k)
      = [sum_x q_x count_{weight g_i}(prefix_k(base_x))] / c_{g_i}.

It then turns the explicit class-count bound into an actual per-item band at ANY eta, preserves every expected regret, and emits a law on all permutations. The old zero-band-only helper could not directly do this. The denominator is always the class of an existing item; empty types are not divided by.

### C.2 Odd endpoint

For odd m>=3, take a uniform insertion position a in {0,...,m-2}, q_a=1/(m-1), and the ranking `insRanking m a`. Its light entries alternate; its adjacent heavy entries are +3,-3. The base multiset is the multiset of `gFamily m`.

1. Prove equality of weight counts at w in {-3,-1,1,3} by evaluating the EXISTING `countIns_*` formulas at k=m; for other w both counts vanish. Use `permOfCountEq` to define base_a and its rank identity. Do not define a permutation axiomatically.
2. Transfer each prefix count via that identity. The expected count is `mixCount m w k`.
3. Apply `O1_odd` to show `|mixCount/c_w-k/m|<=1/m` at all interior budgets. At k=0,m prove the marginal is respectively 0,1 separately. For m=3 there is no +1 class; the item-indexed helper avoids dividing by zero.
4. `insMixture_free_value` supplies expected regret 2/[(m+4)(m-1)] at every interior k. Relabelling does not change it.
5. Apply `actual_banded_witness_of_counts` with eta=1, D=m+4, V=freeValue. Choose its emitted all-permutation law to fill `OddEndpointData`.
6. Invoke `odd_breakpoint_iff`. This proves the breakpoint, not automatically a closed formula for the whole odd curve.

### C.3 Even endpoint

For even m>=4 use a uniform insertion position and an independent fair sign flip. R=Fin(m-1) x Bool and q=1/[2(m-1)]. Sign flip preserves the even family's weight multiplicities.

1. Repeat the count-to-permutation construction for the unflipped and flipped rankings. Reuse generic count helpers; do not duplicate the whole odd file.
2. The expected weight count is `mixCountEven`. Use `O1_even` and sign symmetry to obtain the band at etaStar=(m-2)/(2(m-1)) for EVERY actual item.
3. The heavy marginal is (2k-1)/(2(m-1)); its deviation is |2k-m|/[2m(m-1)]. The ordinary-class count has its own proved bound; do not infer it just by looking at the heavy items.
4. `insMixtureEven_free_value` supplies the budget-wise free value. Apply the nonzero-band helper and push the law onto all permutations.
5. Feed this law to `evenEndpointData_of_law`; `rankSum` is already supplied by the worker's new even-total proof.
6. Invoke `even_frontier` and instantiate its data argument. This closes the formula for ALL even m, not just LP sizes.

The final even headline, for eta>=0, is

    V_m(eta) = max{2/[(m+4)(m-1)], 4(1-eta)/[m(m+4)]}.

The odd headline currently targeted is V_m(0)=(m+3)/[m(m+4)] and
V_m(eta)=V_free iff eta>=1. Do not label that as a solved whole odd frontier.

The same actual law must satisfy band and value. A band proof for one distribution and a value proof for another do not form an endpoint witness.

### C.4 Physical and flow endpoints

`FamilyBaselineIdentification` is now drafted for m>=4. Keep that exact range until a separate m=3 finite case is added; the odd endpoint supports m=3, so either close the small baseline case or state the physical headline for odd m>=5. Do not silently pass a 4<=m theorem at m=3.

Use `family_regret_identification_unconditional` and `gFamily_abs_sum` to replace the algebraic parity regret by actual normalized compression regret. Take maxima and infima over the SAME budgets, same laws and same eta. Preserve the direction and normalizer.

`actual_banded_infima` is the intended flow endpoint. Instantiate its objective with the paper's maximum expected regret over all interior budgets; the theorem about an arbitrary Phi is not itself the paper instantiation. Both ranking->flow and flow->ranking must carry every band constraint and the whole budget vector. Do not claim an efficient algorithm for arbitrary perturbed item weights from the four-type flow formulation.

For stability use the all-item formulation and the moving-normalizer theorem, with d>0 a lower bound on both l1 masses. The planned bound is `|V(g)-V(g')|<=3||g-g'||_1/d`. Keep the feasible item-band set fixed, recompute the true per-budget baseline, and then instantiate the special family. A search that fails to find a destructive perturbation does not prove a uniform robustness radius.

## 5. Evidence and figures — enough to test the story, not another census

### A figures

**A-F1: the actual centered separation.** Plot a certified interval for Gamma_true/Gamma_proxy versus r at M=1, together with the proved bounds. Use r=1,2,4,8 initially; the all-r claim is a theorem. The old eight-cell separation JSON is a different family and may be shown separately, not relabelled. A numerical true-game calculation must include centering and every alternative region. Store primal witnesses, dual/prior upper bounds, residuals, failures, and exact model metadata.

**A-F2: mechanism, after the current rerun finishes.** Reuse the repaired mechanism JSON, now with per-run tau. Show middle-cell query share and certificate-rate/RMST against budget for geometry-certificate optimization, frozen proxy with the specified exploration, and uniform. Call `J_true_lower_*` a lower certificate, not exact J. Nelder–Mead supplies a design, not a certified global optimum. Compare allocation policies under the SAME stopping certificate. A proxy run censored at B has not been shown never to terminate.

**A-F3: learner and information accumulation.** Keep the current one-world results as diagnostics. Add a finite panel with A/B-swapped truths, two gap regimes and an active-region transition; 50–100 independent replicates per chosen cell is a reasonable cost-estimation start, not a promise of error certification. Freeze the panel after development checks. Record selected answer, all kept answers, counts, oracle gaps, Zlo, threshold, and stopping gap diagnostics. Offline truth can evaluate J(N/t,theta), but never enter the learner.

For confidence-axis diagnostics use common random streams across alpha intentionally and record that dependence. Plot the penalty and log(1/alpha) separately. A grid such as 1e-2,1e-4,1e-8,1e-16 probes whether the logarithmic term begins to dominate; it does not prove asymptotic optimality or empirically certify errors as small as 1e-16. Store log-alpha. Do not require an ordering learner<oracle<uniform by a self-check.

### B figures

**B-F1: safe and identification on ONE channel.** Use saved worst-world counts, total query costs and the corrected two-tail analysis. Display upper-certified budgets and censoring explicitly. The current counts need no resampling to fix their interpretation. The three comparable m=3 cells support a large achieved-cost separation, not an estimated minimax ratio.

Only add simulation if a stronger empirical claim is needed: target the missing m=4 identification cells with budgets suggested by the analytic gap, instead of repeating every existing cell. Use the same error target below 1/m for the safe task, and record both all-world and worst-world results. If a budget ladder is chosen using a pilot, freeze it before independent confirmation or account for the full selection family.

**B-F2: query-class boundary.** Reuse the linear-probe Hellinger/envelope/crossover artifacts. Show that a higher-degree legal class can lower the cancellation order. Attained search values are LOWER bounds on the supremum: they can refute an upper bound, not verify one. Record integration error at the H^2 scale and use the stable squared-density-difference expression. Check the normalized density sums, Gaussian factor, and h=0 identity. Separate the raw-F and parity-membership models in captions.

The current finite-grid slope interval for identification contains both -4 and -2; do not make a measured-exponent separation claim from it. The theorem can establish the exponents while the experiment establishes achieved-cost separation.

### C figures

**C-F1: exact price and phase boundary.** Use existing flow/frontier data, exact per-size certificates and final all-m theorem curves. Plot V_m(eta)/V_free, annotate parity and etaStar. Show the odd zero-band price separately from the even one. Existing size evidence reaches a selected set through 31, not every integer through 31.

**C-F2: item-level robustness.** Use the existing 60 per-item and 160 group perturbations. Distinguish fixed versus moving denominator and recomputed versus stale baseline. The new stability bound can be recalculated from stored norms/distances without resolving the optimization. Show attained adversarial examples as such, not as worst-case lower certificates.

**C-F3, only if computational efficiency is a contribution.** Benchmark exact item-permutation LP versus type-flow LP on sizes where both are feasible, then flow alone at larger sizes. Record wall time, memory, dimensions, feasibility residual and objective gap. Current JSONs with only dimension counts do not measure a runtime speedup. This optional benchmark does not block the mathematical paper.

### Concrete producer/result map and launch constraints

Read the following saved outputs FIRST. Source names here identify the relevant code, not instructions to rerun them blindly.

| Purpose | Existing producer | Existing artifact under research/unified_20260919/ |
|---|---|---|
| A theorem-family allocation mechanism | scripts/EXP_paperA_mechanism.py | paperA_mechanism.json |
| A eight-cell learner | scripts/EXP_paperA7_learner.py | paperA7_learner.json |
| A stopping-chain diagnostics | scripts/EXP_paperA7_stopping_chain.py | paperA7_stopping_chain.json |
| A older game family / repair | scripts/EXP_paperA_separation_games.py; scripts/EXP_paperA_repair_barrier.py | paperA_separation_games.json; paperA_repair_barrier.json |
| B actual decoders | scripts/EXP_paperB_decoder.py | paperB_decoder.json |
| C all-size arithmetic / exact per-size certificates | scripts/EXP_paperC_general_m.py; scripts/EXP_paperC_breakpoint_certs.py | paperC_general_m.json; paperC_breakpoint_certs.json |
| C type-flow LP | scripts/EXP_paperC_flow_lp.py | paperC_flow_lp.json |
| C item robustness | scripts/EXP_paperC_robustness.py; scripts/EXP_paperC_perturbation.py | paperC_robustness.json; paperC_perturbation.json |

The corrected B artifact already delivered was generated without observation sampling:

```bash
cd /Users/phanan/cig-amf-main
.venv/bin/python scripts/ANALYSE_paperB_decoder_grid_v2.py --self-test
```

For a LATER completed raw B run, use the same postprocessor with `--input` pointing to that immutable raw JSON and `--out` pointing to a NEW filename. It refuses to overwrite an existing analysis. Do not run the sampling producer merely to obtain corrected intervals.

Several current experiment scripts hard-code their output path. Before any additional panel, add explicit configuration and a fresh output path in a NEW producer version, record the frozen configuration/source, and prove the case reducer matches the intended model. Do not invent unsupported command-line flags or overwrite the current JSON. The A r-pair centered-game figure needs that new model-aware producer if no matching artifact is already present; extending the old eight-cell solver by changing a label is invalid.

### Shared artifact requirements

Use immutable run IDs and output paths; source/dependency hashes from BEFORE launch; final comparison showing whether source changed; explicit RNG recipe and model normalization; raw per-run outcomes or per-cell bad/reps counts; every solver failure including skipped primal candidates; correct censoring and total costs. Mean/SEM alone is not enough. A smoke check of flags or tuple lengths does not validate a statistical conclusion.

Changing only wording while a job runs still breaks naive source-at-write provenance. Finish the run, retain its launch source, and change wording afterward. If the algorithm did not change, do not rerun expensive sampling merely to obtain a new docstring hash: record the two source versions and the nonsemantic diff instead.

## 6. Assemble the manuscripts while closing the final joins

Do not wait to reorganize stable definitions, existing theorems, and related work. Keep unfinished endpoint statements in a private checklist, not marked as proved in the abstract. After the final joins, do one coherent rewrite rather than another historical addendum.

For each paper create a compact claim map with columns:

    scientific claim | model/quantifiers | mathematical proof | Lean declaration
    | remaining assumptions | algorithm/producer | immutable artifact | figure | nearest prior art.

The main theorem must have no data field whose content is its own conclusion. Standard model assumptions such as positive variance and a specified query class are legitimate; uninstantiated hUpper/hLower/stopped_information/endpoint_band are completion obligations.

Suggested main-text logic:

* A: a realizable counterexample to the proxy -> optimized separation -> how much true information the proxy-optimal design loses -> what repair buys -> actual oracle/learner attainability -> operational evidence and limitations.
* B: the safe decision geometry -> query-class-induced indistinguishability -> normalized per-query information -> adaptive lower bound and concrete upper algorithm -> same-channel separation -> boundary where richer measurements change the exponent.
* C: a randomized ranking that must work across budgets -> marginal constraint -> exact zero-band prices and endpoint laws -> full even frontier/odd breakpoint -> exact flow equivalence -> robustness outside equal-weight symmetry.

Keep about three or four headline results per paper. Definitions and proof lemmas are not additional contributions. Move detailed Lean/API material and repetitive derivations to a supplement. The formalization supports trust in the claims; it is not a substitute for explaining why the result changes what one can infer, decide, or optimize.

## 7. Novelty and reviewer checks, without inventing new work to avoid submission

Use the existing literature corpus and bibliography. Compare the final theorem, not keywords. For every central result write: what the nearest prior theorem already gives, exactly which assumption/quantifier differs here, and which displayed result cannot be obtained merely by relabelling that theorem. Check the actual source text before asserting novelty.

For A, generic multiple-answer exploration, mixture martingales and structured identification are reused machinery; the optimized surrogate/decision separation and its realizable geometry must carry the contribution. For B, generic safe decisions and pairwise testing are established; the same-model query-order/cost separation and the restriction boundary must carry it. For C, generic fair-ranking marginals and flow reductions are not the novelty; the all-size signed-prefix laws, phase boundary and robustness must carry it.

If a nearby theorem already implies one component, cite it and keep the more specific consequence; do not advertise the machinery as new. If no result exceeds existing work after this comparison, stronger experiments alone do not repair novelty. Conversely, do not delay submission for another broad literature sweep when the remaining issue is an explicit endpoint law already described above.

Final hostile checks:

1. Boundary parameters: positive variance, zero weights, strict/closed alternatives, h=0, delta>=1/m, m=3 versus m>=4, eta at the breakpoint, and zero normalization.
2. Same information: oracle curves are diagnostic; alternative world, true extrema, support label or optimal design never silently enters deployable policies.
3. Same task/model: centered vs uncentered, parity vs raw-F observations, total vs per-query budget, conditional vs unconditional expected cost.
4. Same law: band and objective proved for the same ranking distribution; correctness and expectation for the same learner; lower/upper B rates for the same allowed policy class.
5. Numerator/denominator: range vs half-range, sigma vs sigma squared, cube sum vs probability mean, raw vs normalized regret, and float point estimate vs certified interval.
6. Evidence-class: mathematical theorem, compiled formal theorem, exact rational certificate, numerical bound, Monte Carlo result, and heuristic diagnostic stay distinct.

The reviewer bundle is ready when those checks and the claim map are consistent: three manuscripts with a clear scientific claim, supplements containing the full proofs and scope, a frozen Lean build with expected declarations/axioms, immutable artifacts, and figures reproduced from those artifacts. Acceptance remains a venue/reviewer judgment. The current target is a defensible complete result package, not a percentage or a count of green modules.

## 8. Concrete worker execution order, continuing to completion

1. Let live jobs finish without editing their sources. Preserve current raw outputs. Do not resample B for the CP correction.
2. Compile the six modules already written by the worker. Add the two new draft modules from this specification only to a NEW frozen gate invocation; do not edit the running gate.
3. Instantiate odd/even endpoint laws through `actual_banded_witness_of_counts`, then emit unconditional C frontier/breakpoint corollaries. Close the actual-regret and flow-objective instantiations.
4. Instantiate A's Gaussian KL bridge. Use the new Qstat perturbation bound in the actual selection/tracking analysis; account for BOTH allocation and stopping-certificate errors. Finish the ENat hitting-time/correctness/expectation theorem under the chosen precision contract.
5. Instantiate B's normalized observation kernel, algorithm-dependent safe hard pair, stopped KL inequality and concrete decoder; emit the two operational rates on the same Experiment.
6. Run the postprocessor on the final saved B counts and feed figures from its output. Keep pre-correction artifacts with their provenance.
7. Read the completed A mechanism/A7 reruns and test each claimed behavior from raw records. Launch only the additional figure-specific panels in section 5 that remain unsupported; do not assert that more seeds will prove an unobserved mechanism.
8. Fill the final claim maps, finish the three coherent manuscripts, and check the actual venue's current scope/format/policy from its official instructions before packaging submission files. Do not assume that an IEEE label alone establishes the right venue.
9. Run one final frozen proof/artifact/figure audit; correct any actual inconsistency; then hand the complete package to an independent reviewer. Stop opening optional research directions unless this review exposes a specific scientific obstruction.

Report progress by delivered endpoint and exact unresolved hypothesis. Do not report “all done” merely because all imports compile, and do not ask for a new batch after each helper lemma.
