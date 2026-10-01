# Lean corpus reading notebook (started 01/10/2026 00:2x EDT)

Task (user 01/10 00:1x): read the Lean of all 7 old papers (ADAPTIVE, D6, FUNCTIONAL, MASTER, QUERY, STRUCTURAL, SUPPORT),
understand what each module means and what it can help with; read the Lean of papers A, B, C twice; then decide which
direction reuses the MOST Lean of genuine NEW scientific value (not bookkeeping, not classical results).

Method: module lists = every `Lean…V<n>` name cited in each paper's .tex (scratchpad leanmap/<paper>.txt):
adaptive 8, d6 51, functional 21, master 7, query 13, structural 13, support 35, paper_a 64, paper_b 52, paper_c 76
(A∪B∪C = 190 distinct). Pass 1 for the 7 papers: every module docstring + every declaration signature
(`scratchpad/leanmap/extract.py`). A, B, C: pass 1 full text, pass 2 statements with the reuse lens.

Value classes used below:
- **N** — new mathematics (a theorem I do not know in the literature, on the paper's own object);
- **T** — technical/formal closure of a known argument (useful, not new science);
- **C** — classical result formalised (textbook);
- **B** — bookkeeping / scope / audit lemma.
Reuse for the MARL line: **R+** directly reusable, **R** reusable idea, **–** not.

## ADAPTIVE (8 modules, 973 lines) — read 00:2x
| module | what it proves | class | reuse |
|---|---|---|---|
| LeanAdaptiveConfidenceJoinV1 | correctness/cost ON a good event; failure ⊆ Eᶜ | B | – |
| LeanAdaptiveExpectedStoppingV1 | layer-cake ∫τ = Σ P(τ>n) for ℕ-valued τ; geometric tail ⇒ E τ ≤ C/(1−ρ); sub-Gaussian threshold √(2c log 1/β) | C (formalised) | – |
| LeanAdaptiveGreedyTraceV1 | the largest-deficit rule as a function reaches counts (7,1,1,1,1) on w=(17,1,1,3,1)/23 (kernel decide) | B (witness) | R (decide template; used for L11 phase-lock) |
| LeanAdaptiveLoopJoinV1 | doubling schedule spends < 4B*; soundness by revalidation; late revalidation overshoots 2^m | C/B | – |
| LeanAdaptiveOnlineQuotaFailsV1 | online largest-deficit rule violates quota (deficit 26/23 > 1) | C (apportionment: house monotonicity vs quota, Balinski–Young) | R+ (cited in MARL v2 V-Q) |
| LeanAdaptiveStoppingFiniteV1 | geometric tail ⇒ τ finite a.s. (τ : Ω → ℕ∞) | C | – |
| LeanAdaptiveStoppingTailV1 | peeling budget δ/(K n(n+1)); union bound; grid overhead 1+ε | C | – |
| LeanAdaptiveTrackingV1 | deficits sum to 0; floor/floor+1 allocation has deficit ≤ 1 and exists; frequency convergence | C | R (round-robin quota; LeanMarlRoundRobinQuotaV1) |
Verdict ADAPTIVE: no new mathematics; formal closures of standard pure-exploration bookkeeping. Low reuse value.

## MASTER (7 modules, 1316 lines) — read 00:2x
Object: Gaussian query design with a profiled nuisance offset (calibration "anchor"/control queries).
| module | what it proves | class | reuse |
|---|---|---|---|
| LeanMasterActiveSetV1 | complementary slackness (tight dual ⇒ support in active set); cancelling design (M=0) makes the anchor worthless; min improves iff every alternative improves | C/B | – |
| LeanMasterAnchorCertificateV1 | energy square completion, profiled info I = D − M²/2K attained; one dual certificate bounds EVERY anchor-free design; U₀ < L₁ ⇒ anchor mandatory | T (certificate pattern) | R (separated-certificate pattern: "sup over a class ≤ U₀ < L₁ ≤ one design" — usable for "no zero-byte rule attains …") |
| LeanMasterAnchorInstanceV1 | small rational instance: anchor-free ≤ 1/8 < 261/1520 | B (witness) | – |
| LeanMasterAnchorThresholdV1 | EXACT two-sided critical price c* = (m−1)²/(m+3)² for the symmetric family (global dual above, explicit improving ray below) | N (narrow: exact threshold in one model) | – |
| LeanMasterCalibrationLawV1 | hidden-shift witness (group without calibration has Γ=0); Γ* = Δ²/(2K(√m+√κ)²) exact (Cauchy–Schwarz, attained) | T/C | – |
| LeanMasterGainFactorizationV1 | Hadamard square factor; slack law (inactive alternatives droppable under small perturbation) | C/B | R (slack law ~ margin stability) |
| LeanMasterGroupCalibrationV1 | rank-one gain ⇒ no mixture beats best single control; rank-two witness G=3I₂ gives strict complementarity | N-ish (clean dichotomy; product-game folklore) | R (idea: mixing senders/controls helps only with rank ≥ 2 structure) |
Verdict MASTER: one narrow exact threshold, one clean dichotomy; little reuse for MARL.

## QUERY (13 modules, 2238 lines) — read 00:3x
Object: Gaussian-mixture observation of a hidden world; the "leakage order" r = first order whose level moments differ.
| module | what it proves | class | reuse |
|---|---|---|---|
| LeanQueryAffinityTestingV1 | Hellinger affinity bracket (ρ²/4 ≤ overlap/2 ≤ ρ/2), LRT attains half the overlap, iid tensorisation ρ^N | C (formalised from integrals) | R (testing bracket for any two-world argument) |
| LeanQueryAnalyticLimitV1 | dominated convergence for H²/h^{2r} → (1/8)∫Δ_r²/p₀ > 0 | T | – |
| LeanQueryCriticalResolutionV1 | critical resolution η* below which ε-feasible, at which it fails (pairs closer than η with |g x − g z| > 2ε) | T/B | R (threshold-of-resolution pattern) |
| LeanQueryGaussianLevelV1 | Gaussian iterated derivatives = Hermite-type polys; level moments; NON-VANISHING of Δ_r (top level dominates) | T (hard half formalised; the fact is known in mixture theory) | – |
| LeanQueryHellingerEnvelopeV1 | χ² ≥ Hellinger pointwise; Gaussian envelopes; integrable majorant | T | – |
| LeanQueryHellingerIntervalV1 | H² ≥ a_E² h^{2r}/32 from one interval (Young + exact ∫(√p+√q)² = 4 − 2H²) | T | – |
| LeanQueryInterventionFloorV1 | exact RANDOMISED regret floor 2401/8192 on a two-world table (deterministic minimax overstates by 1.456×); blind_procedure_floor: same transcript law ⇒ same decision law ⇒ floor for ANY procedure | N-ish (instance) + **T pattern** | **R+ for H6**: zero-byte student = blind procedure on a local fibre |
| LeanQueryMixtureDerivativeV1 | iteratedDeriv through finite sums; mixture coefficient = level sum; both halves on the mixture | T | – |
| LeanQueryRateAssemblyV1 | two-sided N = Θ(h^{−2r}) from the bracket | C/B | – |
| LeanQueryRegretBridgeV1 | γ·e ≤ R for EVERY decision kernel (disjoint good sets), R ≤ L_max·e for the LRT rule; Bayes window | T | **R+ for H6** (regret ≥ γ × testing error) |
| LeanQueryRegretChainV1 | mislabel_costs: disjoint good sets ⇒ every decision costs ≥ γ in one world | C/B | **R+ for H6** |
| LeanQuerySampleComplexityV1 | log sandwich, integer count, matching rate | C | – |
| LeanQueryTaylorRemainderV1 | uniform Taylor remainder, H² ≤ (J/2)h^{2r} | T | – |
Verdict QUERY: the leakage-order rate is close to known moment-matching results for mixtures; the reusable part is the
two-world decision machinery (disjoint good sets ⇒ regret ≥ γ·error; blind procedures share decision laws) — exactly
the quantitative compiled-silence argument (H6).

## STRUCTURAL (13 modules, 2821 lines) — read 00:4x
Object: ONE ranking (a nested prefix chain) must serve EVERY budget k; loss of a k-set = residual oscillation of the
unselected components (`selectedRadius`); ε_nest = least tolerance for which one ranking is ε-good at every k.
| module | what it proves | class | reuse |
|---|---|---|---|
| LeanStructuralAvgPathGapV1 | avg (per-budget) ≤ path (per-ordering execution) ≤ b·avg; ε_nest ≤ b·avg (saturation); equality case | N (in model) / T | **R (commit-to-one-realised-ordering vs average guarantee: exactly committed order vs per-receiver guarantee)** |
| LeanStructuralBudgetRecourseV1 | staircase instance: recourse between ε-optimal sets at consecutive critical budgets is exactly 0/1; every admissible policy has the same total excess recourse | N (instance law) | R (budget transitions ~ capacity changes over time) |
| LeanStructuralConstrainedV1 | free lower bound transfers to marginal-constrained problem; balanced witness | B | – |
| LeanStructuralFamilyLowerV1 | all-m family g_m = (−3, −1^p, +1^q, 3): EVERY ordering pays ≥ 2 (parity/no-big-step mechanism); avg ≥ c/b, path ≥ c; tight | N (in model) | R |
| LeanStructuralFamilyUpperV1 | explicit one-defect orderings for every m and budget j (greedy alternation construction) | N (construction) | R (explicit-ordering construction technique) |
| LeanStructuralIntegerToleranceV1 | quantised objectives keep exact optimal prefixes below one grid unit; normalised χ ≥ 5 rankings needed below 1/114 | T/B | – |
| LeanStructuralNestingThresholdV1 | EXACT nesting thresholds: 4×3 witness ε=1/4; 3×2 witness ε=1/2 (refutes ε*=1/4); family ε=(c−1)/(2c+1) → 1/2 with all components non-constant | **N** | **R+ (ε_nest is the price of serving all budgets with one committed prefix)** |
| LeanStructuralRandomMenuExactV1 | exact random-menu size ⌈(1−δ)r⌉ (lower for every randomised menu, uniform construction attains) | N | R (randomised orders / menus of orders) |
| LeanStructuralRecourseUniformNestingV1 | universal: sorting by decreasing span gives one ranking (2/3)-optimal at every budget (min(D−A, 2A) ≤ 2D/3) | **N** | **R+ (a universal nesting bound; transfers if the MARL per-receiver loss has the same oscillation structure)** |
| LeanStructuralRetainedMarginalV1 | IsRanking, prefixSet, card_prefixSet = min k n; retained trajectory column sums = budget; cyclic menu realises uniform trajectory | T | **R+ (already reused in LeanMarlPrefixThresholdV1)** |
| LeanStructuralRobustSeparationV1 | relaxed weak duality: widening marginals by τ costs ≤ ‖y‖₁τ; instance separation positive for τ < 1/17 | T | – |
| LeanStructuralSaturationV1 | concentrated + balanced ⇒ path = b·avg | T | – |
| LeanStructuralSortedPrefixV1 | ONE nested chain (min-span deletion, exchange argument) 2/3-optimal at EVERY budget, no hypothesis | **N** | **R+** |
Verdict STRUCTURAL: genuine new mathematics about ONE committed nested order serving many budgets — the SAME
structural question as the MARL prefix channel (one common order, receiver capacities K_i) and as Paper 1's
"price of nesting". The loss function differs (oscillation vs team value), so reuse is through the framework
(ε_nest, avg vs execution, universal sorted-chain bound) and the prefix lemmas.

## FUNCTIONAL (21 modules, 4177 lines) — read 00:5x
Object: Gaussian design to identify the group of largest RANGE (capacity = max − min of a group's cell means); the
"energy" of a flipping alternative; extrema free in the alternative.
| module(s) | what it proves | class | reuse |
|---|---|---|---|
| ContrastDesign/ContrastInfimum/ContrastPotential/ContrastDuality | edge-contrast observations: zero cut ⇒ zero information; complete graph value δ²/(2(K−1)); potential/flow certificates; harmonic potential pins pair value δ²/(2R_eff) | C (Dirichlet/Thomson) formalised | – |
| CrossoverExactRegion | exact reduced optimum on a region (three-cost Engel identity) | T | – |
| ExtremaCrossover / CrossoverLower | three witnesses (upper) + explicit allocation lower bound; sandwich within factor 2, sharp (1+d)² on d ≤ √2−1, uniform in n | N (in model) | – |
| Heterogeneous{Crossover,Instance,Lower}, GeometryDischarge, AllocationJoin | heterogeneous means/variances: value enters only via S⁺ = Σσ/(g+δ)²; instantiated value c²/(n(32+2c²H)); domain sharp | N (in model) | – |
| DesignDuality / DesignOptimality / RangeDesignCertificate | weak duality certificate; concavity ⇒ one better cell disproves optimality; KKT certificate with PSD (no inverse); setup-cost crossing; undecided when brackets overlap | T/B | R (certificate discipline; "undecided when brackets overlap" = our IUT/CI reporting) |
| OneCellInformation | one-cell flip energy, mandatory-mass bound | T | – |
| RangeAlternativeUnion / RangeEnergyOracle / ShrinkExpand | closed answer boundary = finite union of convex pair regions; finite oracle; inner QP closed form g²/(2Σ1/w); shrink = clamp projection, expand = one ordered pair | T | – |
| ScalarProxyFails | the scalar proxy is wrong in BOTH directions by no constant (two families) | N (negative) | R (pattern: proxy fails in both directions — cf. our hub-rule/age-first proxies) |
| SuboptimalWitness | exact 8-cell witness that the formula design w* is not optimal (margin 7.1%) | B (witness) | – |
Verdict FUNCTIONAL: solid technical results in a pure-exploration design model (range identification); classical
electrical-network duality; little reuse for MARL beyond certificate discipline.

## SUPPORT (35 modules cited, 22 new beyond QUERY; 6989 lines) — read 01:0x
Object: "decide without identifying" — name a SAFE decision without recovering the world (unsafe tips W ⊂ [m]).
| module(s) | what it proves | class | reuse |
|---|---|---|---|
| BayesMinimax / MinimaxCounting / EquivariantDecoder / MinimaxLower | passive Bayes value E[L_N/(a+L_N)] attained by uniform-unseen decoder, = minimax (equivariance + transitive symmetry ⇒ constant risk); Bayes over ALL rules via pointwise argmin | N (exact passive minimax in model) + C (Bayes⇒minimax) | R (exact zero-byte floor by symmetry: a flat decoder + Bayes-optimal value ⇒ minimax) |
| DecideExponent / DecideRecover / RecoverySandwich / SamplingLaw / TupleCount | DECIDE exponent = total unsafe mass s; RECOVER exponent = smallest class mass p_min; growing-K decide risk exact (1/2)(1−P)^N vs coupon-collector recovery | **N (decide/identify separation)** | **R (conceptual core of compiled silence: acting needs less than identifying)** |
| GeometryReduction | the support geometry with restricted query/decision sets IS decision-region determination (Javdani et al. 2014) at the same cost; both restrictions necessary | N (honest negative/collision) | – |
| CyclicWindow / IntervalHitting / NonadaptiveExact / NonadaptiveLower | non-adaptive exact s·L queries (cyclic windows) | N (combinatorial, in model) | – |
| NormalizedTolerance | exact phase transition in ε at γ = (m−1)/(b(m−1)+a) | N (in model) | – |
| OccupancyMoments / PassiveSampling / PassiveDecisionMass / PassiveAnswerMultiplicity | E L_N, E L_N² exact; certification w.h.p. with decision-relevant mass γ; γ=0 vacuous | C/T | – |
| ParityBundleSize | parity geometry: every bundle of < d queries leaves loss exactly 1/2 (adaptive too); single-query gain 0 | C-ish (XOR/parity folklore) formalised | R (partial messages can have zero value until complete — cf. Paper 1 XOR game) |
| QueryErrorTradeoff | depth-b tree correct in ≤ b+1 dense worlds; attained | C | – |
| ThreeWorldWitness | three worlds: every PAIR shares a zero-regret decision, all three do not (in the real geometry) | N (witness) | **R+ for H6: a local fibre needs a GLOBAL common safe action; pairwise compatibility is not enough (feeds Paper B's obstruction law)** |
Verdict SUPPORT: genuine new results on deciding without identifying (exact passive minimax, decide/recover exponent
separation); reuse for MARL is conceptual (compiled silence = decide from a local fibre) and through the fibre
obstruction witness that Paper B generalises.

## D6 (51 modules cited, 30 new beyond QUERY/SUPPORT; 9128 lines) — read 01:1x
Object: query-width / compression of a retained set under a reference (calibration) query; worlds = hidden sets A,
a distinguished label j; information games over legal measurements (scalars, pairs, joint queries).
| module(s) | what it proves | class | reuse |
|---|---|---|---|
| ReferencePhase{Threshold,Witness,Value,RegretBridge}, ReferenceCertifiedPhaseValue, ReferenceMatchingMinimax, ReferencePhysical{Bounds,Certificate}, ReferenceEndpointWorlds, ReferenceOrbitAverage, ReferenceFullCountLoss, ReferenceLegalCountMinimum, ReferenceMaximumBranches | exact finite-k phase threshold ρ* = 2a − e/k (iff), matching minimax certificates over EVERY randomised legal policy, non-empty witness only from q = 8, physical bound slope ≤ 1/4 (Bernoulli induction) | **N (exact phase law in model)** | – (model-specific) |
| ScalarInformation / GeneralFamily / ThreeClassPhase / UncappedProfile / ScalarWidth{Region,Sharp} / ScalarOptimalAssembly / WidthCostInformation / WidthTransitionLocal | B-scalar never blind (retracts "two blind directions"); the (d,x) slice is the cheapest member of its class; distance-one active; every legal design capped by one adjacent swap (averaging) ⇒ scalar design optimal below a width threshold; local strict improvement past it | N/T | R (averaging-argument pattern: "some swap caps every design") |
| MarginSensitiveExchange / SharpMarginThreshold | exchange loss ≤ |S∖T|·(2δ − μ) with score margin μ; margin 2 sufficient, every sub-threshold margin fails | N (sharp) | **R (margin-sensitive version of the block frontier; with the relay patch, η-margin ⇒ prefix optimal)** |
| OracleValueStability / CyclicValueConfidence | Γ Lipschitz in the nuisance across all phases (modulus 2q(2q+1)); estimated-optimizer regret ≤ 2·modulus·|μ−μ̂| + τ; coverage of information regret on the cyclic stream | T | R (plug-in regret decomposition = Paper 1 Theorem 1 style) |
| AlternativeReduction / DesignDerivation / CalibrationActiveFace / CenterAnswerGeometry / ApproximateActualEvaluator | finite check of quadratic infima; Lipschitz modulus certifies grids; design derived (w_B = 1−η, w_pair = η/c), optimum at an endpoint unless equal price; active-face criterion; boundary path arbitrarily cheap | T/B | – |
Verdict D6: a large, careful, model-specific corpus (exact phase law with certified minimax values). New in its own
model, little transferable to MARL except the margin-sensitive exchange bound and certificate patterns.

## Pass-1 verdict over the 7 old papers (01:1x)
- New mathematics that is about ONE COMMITTED NESTED ORDER SERVING MANY BUDGETS: STRUCTURAL (ε_nest exact thresholds,
  universal 2/3 sorted chain, avg-vs-execution gap = #budgets, random menus) — the closest to the MARL prefix channel.
- New mathematics about DECIDING FROM A FIBRE WITHOUT IDENTIFYING: SUPPORT (exact passive minimax, decide/recover
  exponent separation, three-world fibre obstruction) + QUERY (blind-procedure floor, regret ≥ γ·error) — the closest to
  compiled silence (H6).
- Everything else (ADAPTIVE, MASTER, FUNCTIONAL, D6) is new or technical within pure-exploration design models and has
  little reuse for the MARL line.

---------------------------------------------------------------------------------------------------
## PASS 2 (deep: proofs + manuscripts own TODOPAR self-assessments) — 01/10 00:26–00:35 EDT
User 00:26: "đọc cho đàng hoàng, t thấy m đọc hơi nhanh". Pass 1 graded from docstrings/signatures; pass 2
reads proof bodies and each manuscript's abstract/TODOPAR. CORRECTIONS to pass 1 (pass 1 over-graded):

### STRUCTURAL — downgrade
- The manuscript's own TODOPAR (structural.tex l.165–175): "the lower bound is three lines of pigeonhole … V_path/V_avg =
  m−1 = |Bud| is the generic distance between max-of-average and average-of-max … reads as inflation. The result with no
  counting argument behind it is Theorem thm:construction". Agreed after reading the proofs:
  * `excess_le_two_thirds` (RecourseUniformNesting) = two triangle inequalities on osc + min(D−A,2A) ≤ 2D/3. **Elementary.**
  * `one_prefix_chain` (SortedPrefix) = top-k of a MODULAR function (span) is nested (min-span deletion) + the 2/3 bound.
    Elementary; the chain is just sorting by span.
  * `AvgPathGap` (max E ≤ E max ≤ b·max E; eps_nest ≤ path) = **C** (classical finite-sum facts), not N.
  * `NestingThreshold`: exact thresholds on 3×2 / 4×3 witness matrices (finite case checks) → N but witness-level;
    universal ε_nest* ∈ [1/2, 2/3] is OPEN.
  * `RandomMenuExact` lower = averaging (each ranking hits ≤ 1 critical budget) — elementary; staircase family specific.
  * Genuinely substantive: the explicit one-defect construction (FamilyUpper, greedy alternation with invariant
    |s|≤1 ∧ |s−a+b|≤1), and the uniform-retention law (NOT in Lean; Paper C later proves the whole banded frontier).
- Reuse value revised: the GENERIC DEFINITIONS (`EpsilonOptimalAt`, `OnePrefixChain`, `PrefixCover`,
  `PrefixCoverDimensionAtMost`, `prefixSet`/`card_prefixSet`, grid lemma `epsilonOptimal_on_grid`) are R+ because
  they are stated for ANY objective `Finset I → ℝ`; the theorems are R (patterns), not R+.

### D6 — upgrade one item
- d6.tex TODOPAR: "the margin half is a self-contained result on Top-C selection under APPROXIMATE MODULARITY … positioned
  against Feige–Feldman–Talgam-Cohen". `pair_doubled_loss_le_card_mul_two_delta_sub_margin`: with mixed differences
  |∂²F| ≤ δ and Top-k-by-score with margin μ, 2(L(S)−L(T)) ≤ |S∖T|(2δ−μ); SharpMarginThreshold: μ = 2δ is sharp.
  Proof = endpoint patching + score-surplus summation (moderate). This is the margin form of Paper 1's block frontier and
  of our `approx_scoreLocal`/`relay_frontier` (η-approximate modularity ⇒ top-k optimal when the k/k+1 score gap ≥ 2η).
  R (pattern; the D6 statement is for productCompressionLoss, not for a team value).

### QUERY — downgrade the "R+"
- `blind_procedure_floor` is a TABLE theorem (4 decisions, two worlds; raw-law equality of the worlds NOT proved — its
  own docstring). The bridge "same transcript law ⇒ one decision distribution" is a two-line Fubini. Pattern only (R).
- `regret_floor` = averaging over two worlds (max ≥ mean, every column coefficient ≥ 19208/32768). Elementary.

### SUPPORT
- `ThreeWorldWitness` = the Helly-triangle ({0,1},{1,2},{0,2} pairwise meet, no common point) realised in selectedRadius.
  Classical combinatorial idea; B (witness). Paper B's obstruction law is the general statement.
- SUPPORT TODOPAR: the minimax theorem took constant-risk and Bayes-value as HYPOTHESES (equivariance action not
  instantiated; deterministic rules only) — reviewer-level gap recorded by the paper itself.

### ADAPTIVE / MASTER / FUNCTIONAL — unchanged grades, with the papers' own caveats
- ADAPTIVE: the result "most worth developing" (TODOPAR) is an UNPROVED quota-method bound |N_i(t)−t w_i|<1.
- MASTER: TODOPAR says the E2 simulation measures a common-world detection task, not the titled threshold decision.
- FUNCTIONAL: TODOPAR: the paradigm (non-mean statistic, finite union of convex regions) is established (Agrawal–Koolen–
  Juneja CVaR, Ariu et al.); title narrowed because the separability step is not proved.

### Revised verdict for the 7 old papers
Depth of NEW math is modest everywhere; the genuinely hard formal pieces are QUERY's non-vanishing (Gaussian level),
D6's certified phase law, FUNCTIONAL's KKT/PSD certificate, STRUCTURAL's construction. For the MARL line the reusable
assets are (i) generic DEFINITIONS (STRUCTURAL prefix-cover/OnePrefixChain), (ii) PATTERNS (approximate-modularity
margin threshold of D6; two-world averaging floor of QUERY; Helly-triangle of SUPPORT), not deep theorems.

---------------------------------------------------------------------------------------------------
## PAPER A (64 modules, 22.2k lines) — pass 1 (manuscript + generic modules in full)
Object: Gaussian pure-exploration design; a FROZEN SURROGATE (extrema frozen, ordering constraints dropped) vs the TRUE
alternative game; starvation; the price of repair; the repair law R(b) = optimal budgeted rate.
| layer | modules | what | class | reuse |
|---|---|---|---|---|
| generic duality | SacrificeDualityV1 §General (`exchange`, `frontier_upper`, `value_upper`, `budget`, `weak_duality`, `repair_mix`, `repair_clipped`) | weak LP duality for ANY two concave design values on a finite simplex: a frozen certificate c + covering loads ν ⇒ Λ·J_t(w) ≤ sac(w), R(b) ≤ b/Λ, N·sac ≥ ΛD; mixing gives R(b) ≥ min(1,b/s(v))J_t(v) | T (weak duality), cleanly general | **R+** (any surrogate-vs-true frontier on a convex design set, e.g. time-shared schedules) |
| generic shape | RepairLawV1 (`no_threshold`, `linear_repair`), RepairRateV1 (`R_concave`, `R_continuousAt`, `near_design`) | frontier concave, continuous, no threshold, linear on [0,s(v)] | T | **R+** |
| generic channel law | RepairLawV1 (`event_info`, `budget_law`, `budget_law_multi`), RepairBridge/NoPos/Stop, PolicyClassesV1 | on ANY channel (Channel/Policy/hist of PaperBProtocol): E|N|·R(b) ≥ (1−δ)log(1/δ) − log 2 for budget-honouring δ-correct policies; finite horizon AND unbounded stopping; nested policy classes; mean-of-sacrifice escapes | **N** (the repair law as a rate statement) + T (change of measure) | R (needs a learning/identification problem) |
| model | Centred, Separation (1773 L), Frozen, Strict, Frontier, RepairSlope, Sacrifice*, Endgame | separation 9/512 vs Θ(1/rM); starvation; exact slope 1/(8rM); sacrifice law 8rM log(1/δ) | N (in model) | – |
| learners | A6*, A7* (ideal learner: ridge GLR, Ville, tracking, expected stopping; surrogate learner Ω(log²)) | full formal track-and-stop-type analysis | T (heavy, formal) | – (unless a MARL learning-rate theorem is wanted) |
| two arms | RepairLawV1 two_arm_*, TwoArmRateV1 | R(b) = b(1−b)Δ²/2 exact | N (small) | R (template) |
Verdict A: the GENERIC layer (sacrifice duality + repair-law shape + channel law) is reusable and genuinely new as a
"surrogate-starvation → exact repair price" framework. The model layer is pure-exploration-specific.

## PAPER B (52 modules, 17.4k lines) — pass 1
Object: deciding without identifying under noise; obstruction = set of worlds with no common safe answer.
| layer | modules | what | class | reuse |
|---|---|---|---|---|
| combinatorics | SafeOrderV1 (`safeAt_iff`, `unsafe_mono`, coSafe), SepDerivedV1, DecisionOrderV1 (`dec_hitting`, `id_implies_dec`, `dec_mono`, ultrametric `max_order_iff`), QueryDesignV1 (`hitting_embeds` ⇒ NP-hard), UnifiedObstructionOrderV1 | safe-order law s* = max_H min_pairs sep; menu reaches order s iff it HITS every obstruction; every hitting-set instance embeds | N (law) / C (Helly-type core is elementary) | **R+ (already partly reused: MarlCompiledSilenceV1 imports UnifiedObstructionOrder)** |
| protocol | ProtocolV1 (Channel with dummy, Policy kernels, hist measure), TranscriptKLV1 (`transcript_kl_le_qsum`), KLV1, ChangeV1, DensityV1 | adaptive sampling measure and transcript KL chain rule | T (heavy, formal) | **R+** (any adaptive message/observation lower bound) |
| lower law | ObstructionLawV1 (`obstruction_pigeonhole`, `obstruction_lower`, `obstruction_lower_star`), StoppedLawV1, ChiStarV1 | E[#queries]·t* ≥ ((1−δ)/(|W|−1))log(1/δ) − log 2, every policy, unbounded stopping; χ² sharpening | **N** | **R+** |
| upper law | ObstructionLawV1 tournament, HellingerTestV1, ShareTournamentV1, PrivateQueryV1 | survivors tournament; Hellinger exponent; |Q| vs |W|² sharing; cardinality factor necessary | N/T | R+ |
| order + game | ObstructionLaw graded_*, CriticalGameV1 (limit h^{-2s} D_h → G*), VisibleV1 | exponent = obstruction order; constant = critical game | N | R |
| channels | Parity*, Family*, Hellinger*, Rates (2414 L) | parity mask: safe h^{-2} vs identify h^{-2(m−1)}; latent family orders 1 vs r | N (in model) | – |
Verdict B: the most TRANSFERABLE new law of the whole corpus: the obstruction law is stated for every finite
safe-answer correspondence and every channel; its combinatorial half is already in MARL v2 (compiled silence), its
ANALYTIC half (rate lower/upper, stopping, query-design hitting) is not yet used.

## PAPER C (76 modules, 26.8k lines) — pass 1
Object: ONE random removal order serving EVERY budget under per-item marginal bands, signed-prefix regret.
| layer | modules | what | class | reuse |
|---|---|---|---|---|
| reduction | FlowV1, FlowBandJoinV1, TypedFlowV1, FlowCertV1 (`potential_bound`, `cert_lower`), LawPushV1, FlowObjectiveV1 | permutations → composition flow (exact, band carried), for every multiset of d types; dual potential certificates telescoping along paths | T (standard flow reduction, exact with bands) | **R+ when a per-receiver value depends only on the prefix COMPOSITION by type** |
| frontier | Endgame, EndpointLaw, OddFrontier/Kink*, Even*, Window, Uniform | V_m(η) exact for every m, η (even: max{2/((m+4)(m−1)), 4(1−η)/(m(m+4))}; odd: two affine pieces, crossing η_t) | **N (deep, exact)** | R (signed aggregate only) |
| typed / two-magnitude | TwoMag* (≈7k L), FreeBandV1 | exact frontiers on (1,1,2,2),(2,2,1,1),(2,2,2,2); free threshold η_free attained | N (in model) | – |
| robustness | StabilityEndgame, RobustBall, Collapse* | Lipschitz in weights; price ratio Θ(min{m,1/ε}) on ℓ1 balls | N | R |
| timing / recourse | ExPost*, BudgetAware/Exchange/Sharp/Families, CountRecourse | budget after the draw ×(m−1); band then costs ≤ 1+1/m; knowing the budget; ONE exchange after the reveal recovers the whole gain | **N** | **R (one exchange ≈ one revision ≈ one relay hop)** |
Verdict C: deepest exact new mathematics of A/B/C, but tied to the signed-sum loss. It transfers literally to a prefix
broadcast whose receivers estimate a SIGNED AGGREGATE of senders' values (e.g. max-pressure = Σ in − out) under an
airtime-fairness band: "drop the first k" = "a receiver of capacity m−k misses the last k".

---------------------------------------------------------------------------------------------------
## Direction decision after pass 2 (01/10 00:5x EDT) — which direction reuses the most GENUINELY NEW Lean
Candidates and what each reuses (only NEW-math Lean counted; classical/bookkeeping excluded):
1. **Decision depth of the prefix broadcast (B → MARL v2)** — reuses B's safe-order law (SafeOrder `safeAt_iff`,
   UnifiedObstructionOrder `classes_resolve_iff`, obstruction floors), B's hitting/NP-hardness (DecisionOrder,
   QueryDesign), the corpus' price-of-nesting question (STRUCTURAL `OnePrefixChain`, Paper 1 XorGame/NestingDegree),
   and MARL v2's relay modules (NewsRelay, StrongOneHop) and DecisionLifetime. Rate half (B ObstructionLaw/StoppedLaw/
   Hellinger tournament) is available for noisy messages. MOST MARL-flavoured (what a decentralised policy can decide,
   what communication is necessary). Collisions: Javdani et al. 2014 (adaptive noise-free hyperedge cutting — the
   Bayesian adaptive version of the hitting law), Messias–Spaan–Lima NIPS 2011 (local beliefs identify the optimal
   action → no comm), local shields for Dec-POMDPs (Oxford; per-agent safe action sets from observation-consistent
   state subsets), SeqComm-DFL arXiv 2604.08944 (Fano bound on comm value via I(s; a*|o), priority-ordered sequential
   messages), PET/degraded message sets (nested decoding at the coding level). Novel part: obstruction/hitting law ON
   the nested prefix channel, the nesting price with receivers of different capacities, relay collapsing it to one
   inclusion, the obstruction-mass floor for compiled silence, act-vs-identify message gap.
2. **Surrogate starvation → repair price for the freshness surrogate (A → MARL v2)** — reuses A's generic duality /
   repair-law layer. Already used as framing (V-A: Paper A repair mixture measured, ledger L-177). Concept collides
   with AoI-vs-VoI literature; the generic layer is weak-duality (T).
3. **Fair prefix broadcast for a signed aggregate (C → networking)** — C's exact frontiers transfer only to a SINGLE
   signed value vector; E3 has per-receiver vectors (ledger notes 30/09: "do not transfer"). Not pursued.
**Decision:** pursue 1 (new modules started 00:3x: LeanMarlDecisionDepthV1, LeanMarlPrefixEDFV1,
LeanMarlObstructionMassV1, LeanMarlRelayDecisionV1), keep 2 as framing already in the paper, drop 3 for E3.

## A/B/C pass 2 (proofs of the reuse-relevant modules; 01/10 00:4x–01:2x)
Read in full or nearly: B `SafeOrderV1`, `ObstructionLawV1` (§1–3), `DecisionOrderV1`, `QueryDesignV1`, `ProtocolV1` (§1–2),
`ChangeV1`/`ChiStarV1`/`CriticalGameV1`/`CertificateChannelV1`/`DecideV1`/`DecoderV1`/`DensityV1`/`FamilyChannelV1` headers
and statements; A `SacrificeDualityV1` (all), `RepairLawV1` (header + statements), `RepairRate/Bridge/NoPos/PolicyClasses`
(statements), A6/A7 learner headers (`SurrogateCost`, `EstCost`, `BadRounds`, `A7Confidence`, `A7StoppedGen`,
`AdaptMart`, `LowerKL`, `BudgetUpper`); C `TypedFlowV1` (all) + the module map.
Findings that changed what is reused (all now used or recorded):
- B `DecisionOrderV1.max_order_iff` needs an ULTRAMETRIC separation order; the prefix broadcast's `sepPos` IS ultrametric
  (proved: `LeanMarlAdaptiveDepthV1.sepPos_ultrametric`), so B's per-world decision order = the anytime decoding depth
  of a prefix receiver and its maximum = the fixed decision depth (`worst_anytime_depth_iff`). Genuine reuse of B's new
  math, not a re-proof.
- B `CriticalGameV1.same_order_ratio`: private vs shared queries differ by the menu size k in the rate CONSTANT at the
  same order. Reading for MARL: a relay packet that carries k senders' records is a "shared query"; with noisy records
  relay improves the decision-rate constant by up to the records per packet (instantiation not written; noted).
- B `DecideV1.zero_query_floor`: overlapping safe sets make a query-free uniform guess unsafe only w.p. 1/m — the
  randomised zero-byte floor; consistent with `LeanMarlObstructionMassV1.floor_witness` (1/2 at m=2).
- B `ProtocolV1` needs positive densities on ℝ: noiseless or erased records are SINGULAR, so the rate law does not apply
  to E3's deterministic records or packet loss; only to noisy-record models.
- A's learner layer (A6/A7) is a full formal track-and-stop theory (Ville via the mixture martingale, freezing lemma,
  tracking, GLR stop, stopped change of measure) — T, very heavy; its MARL analogue (a scheduler that learns sender
  relevance while following a freshness surrogate pays log²) is not part of the current paper.
- C `banded_vectors_agree` holds for ANY cost on composition states: the flow reduction transfers to any per-receiver
  value that depends only on the decoded composition by type — single receiver only (E3 receivers differ).

---------------------------------------------------------------------------------------------------
## The predecessor repo /Users/phanan/cig_amf (user 01:2x: "coi thêm trong đây nữa coi có chỗ nào dùng dc ko")
What it is: the ORIGINAL CIG-AMF MARL project (54 commits, 2026-07-30 → 08-29): Paper A "Causal Influence Spectrum"
(interventional response model → structural capacity C_ij, behavioural direction D_ij, latency) and Paper B "CIG-AMF
Core-Periphery" (C-based selection of which neighbours get explicit pair models; direction-aware peripheral memory;
entropy-adaptive core budget k_i = ⌈k_min + H̃(C)(k_max − k_min)⌉). Its own fixed scientific question
(docs/FAILURE_RESEARCH_AND_ALTERNATIVES.md §1): "Does DECISION-RELEVANT inter-agent structure improve scalable MARL under
non-stationarity?"
State verified from its artifacts:
- H1 (estimator recovers the influence ordering) FAILED: results/h1, 8 seeds × {DR ε ∈ 0…0.12, plug-in}: rank correlation
  with the tiny oracle −0.11 … +0.13 (std ≈ 0.4 per seed), sign agreement 0.17–0.48 — chance level. The failure doc lists
  why (non-matched estimands, missing propensities, horizon > 1 mismatch, a signed target with conditional mean zero).
- External CityFlow result = a 2-episode smoke (results/external_training_cityflow, "architecture_generalization_only").
- Audit (docs/AUDIT_REPORT.md): critical bug (one agent's peripheral memory copied to all 24), H3 null (NoMultiMemory
  tied and 3× faster).
Reusable for the MARL v2 decision-depth line (honest grades):
1. THE QUESTION, answered in a cleaner setting (R+ framing): the predecessor tried to ESTIMATE action-influence
   structure causally and could not (H1 null). MARL v2 asks the information version — which senders' RECORDS change the
   receiver's acceptable action — and the teacher's counterfactual views (training-only oracle) MEASURE it exactly
   (V-D), with no causal-estimation step. The answer is the obstruction/hitting structure, and it is small (empty-base
   smoke: ≤ 1 sender per receiver-step). This is a strong "why this paper" paragraph, and an honest one.
2. Entropy-adaptive budget ↔ hitting number (R, testable): concentrated relevance ⇒ small core; in V-D terms the
   receiver's hitting number. A V-D v3 field (which sender is the minset-1 sender; per-sender singleton flips) would
   test whether relevance concentration predicts the hitting number and whether the relevant sender is a spatial
   neighbour (decision structure is local).
3. Cross-fitted AIPW (models/crossfit_aipw.py) — not needed for messages: a receiver can compute its own actor's action
   with and without each DECODED record (a local counterfactual, no randomisation); undecoded senders' relevance is
   unknowable without their records, which is exactly the nesting problem relay solves. Keep only as a citation of the
   predecessor's lesson.
4. Signed stratified Deep-Sets periphery (beneficial/harmful/neutral/uncertain) — superseded by relay packets carrying
   every record and by BYTEBUDGET summaries; not reused.
5. Related work to add: Pieroth, Fitch, Belzner, ICML 2024 "Detecting Influence Structures in MARL" (total/state impact
   measurement of one agent's ACTIONS on another's returns) — distinguish: action influence vs message decision
   relevance (obstruction splitting). Also Jaques 2019 (social influence), already cited elsewhere in the corpus.
6. Protocol lessons (FAILURE doc): matched estimands, horizon one, logged propensities — V-D complies (one-step teacher
   action, same state, same senders, both bases logged).
