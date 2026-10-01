# Novelty comparison of current Papers A/B/C with the supplied literature corpus

Date: 2026-09-25. This is a separate review artifact, not a project ledger update.

## Evidence and scope

Inputs: `/Users/phanan/Downloads/Pasted text.txt` (numbered 82-entry literature ledger), `Pasted markdown.md`, their `(1)` follow-up reports, and `/Users/phanan/cig-amf-main/research/literature_audit_20260921/`.

The original report says **500+ raw citation/reference records**, not 500 full papers read. The local queue contains 1,000 records; its progress file records 240 abstracts examined. The OpenAlex corpus contains 4,537 records and the arXiv corpus 1,812; these overlap and must not be added as unique papers. Several numbered ledger entries describe a research line rather than one unambiguously identified paper. Thus this review does not certify a thousand theorem-level comparisons.

`CROSSWALK_82.csv` preserves every numbered entry of the supplied 82-entry ledger and maps it to the result IDs below. Rows distinguish rechecked primary sources from the user's inherited summaries. The present detailed comparisons concentrate on the closest sources, not on accumulating unrelated citations. The papers and relevant Lean declarations were read; no experiments or Lean builds were rerun. Novelty means an additional result for the stated model, not universal superiority over prior work or a guarantee of acceptance.

## A — what optimizing the wrong information geometry costs

### Current result package

The centred additive compression family has two cells on A, two anchor cells on B and r middle pairs. Anchor variance is 1, middle variance M>0. At the reference world, A=(-1/2,1/2), B's anchors=(-1/8,1/8), and its middle cells are zero. Actual product responses, loss and observation KL are connected on the centred parameter class.

**A0, model bridge.** The actual loss retaining A is range(B)/2 and retaining B is range(A)/2. The true strict alternative for choosing A is therefore range(B)>range(A), with centring enforced. The frozen surrogate keeps the original anchor contrast. These are different alternative sets, not simply a globally valid local quadratic approximation of one set. Gaussian information is the weighted squared distance on the same observation model.

**A1, optimized separation.** With J the fixed-design information and Γ=sup_w J(w),

\[
\Gamma_{fr}=9/512,\qquad
\frac{9}{128(4+2rM)}\le\Gamma_{true}\le\frac1{8rM}.
\]

Both games have already optimized allocation. Consequently Γtrue/Γfr=Θ(1/(rM)) in the regime rM≥1, including M=1 and r→∞. The displayed exact inequalities hold more broadly; the uniform Θ shorthand must not be extended to rM→0.

**A2, all and near-optimal designs.** If a(w) is anchor/A mass,

\[
J_{fr}(w)\le(9/512)a(w).
\]

Thus every exact optimizer has zero middle mass and Jtrue=0. More quantitatively,

\[
J_{fr}(w)\ge\Gamma_{fr}-e
\Longrightarrow w_{mid}\le512e/9,
\qquad J_{true}(w)\le64e/(9rM).
\]

**A3, price of repairing the design.** Let sac(w)=1−Jfr(w)/Γfr and R(β)=sup{suitable Jtrue(w): sac(w)≤β}. For 0≤β≤1,

\[
\frac{9\beta}{128(4+2rM)}\le R(\beta)\le\frac{\beta}{8rM}.
\]

The lower side is a feasible mixture achieving the guarantee, not a proof that its value equals that particular lower-bound constant. The strict alternative version is available. This is a two-sided exchange law between loss of surrogate objective and recovery of information relevant to the actual decision.

**A4, operational sacrifice and rates.** For a finite-horizon randomized adaptive policy correct at the truth and all strict alternatives, put Dδ=(1−δ)log(1/δ)−log2, N=Σe E[Ne] and wbar_e=E[Ne]/N. Then

\[
E[N_{mid}]\ge8rM D_\delta,
\qquad N\,sac(\bar w)\ge8rM D_\delta.
\]

If, pathwise, Nmid≤cT^a+B, 0<a≤1, EB≤b, then for positive numerator

\[
ET\ge\left(\frac{8rM D_\delta-b}{c}\right)^{1/a}.
\]

The same-model ideal learner attains ET/log(1/δ)→1/Γtrue. The analysed frozen learners, including the estimator-driven unrestricted frozen oracle under its stated local exactness condition, incur Ω(log²(1/δ)) under square-root forcing. The fixed-horizon sacrifice result and the unbounded learner endpoint must keep their separate scopes. A full operational upper frontier at every prescribed tiny β is not established merely by the static R(β) bounds.

Lean anchors: `LeanPaperACentredV1` (starvation), `LeanPaperAStrictV1`, `LeanPaperAFrontierV1:160`, `LeanPaperASacrificeV1:236,286,410`, `LeanPaperA7IdealFamilyV1:304`, `LeanPaperA6EstCostV1:237`. All paths here are under `/Users/phanan/cig-amf-main/work/p13_conjectures/`.

### Closest comparisons

**Overstall, Properties of Fisher information gain for Bayesian design of experiments (2022).** Section 3 reduces expected FIG to a sum of pointwise utilities; Section 4 explicitly has conditions under which *all* optimal designs are undersupported or parameter redundant. Therefore A2's universal quantifier is not, alone, a new conceptual result. The basic approximate-optimizer mass argument is also a familiar objective-gap argument. The additional package is A0+A1+A3+A4: an actual compression alternative class, optimized true-vs-frozen information separation, a two-sided repair exchange, and a policy-level information demand connected to the sacrificed surrogate budget. A is not a generalization of all exponential-family models in Overstall. [Primary paper](https://arxiv.org/pdf/2003.07315)

**Wan–Liu–Grigas–Shen (2026), Decision-Focused Sequential Experimental Design.** Theorem 3.2 states that their decision-focused candidate elimination succeeds while a decision-blind benchmark can retain suboptimal predictors. Consequently neither decision-focused acquisition nor a stopping advantage is new. A's distinct statement keeps the actual compression decision and valid stopping objective, isolates the wrong allocation geometry, and derives a quantitative budget/rate penalty A3–A4 rather than only an inconsistency example. The two models are not nested; this is an additional mechanism theorem, not a stronger theorem in every respect. [Theorem 3.2](https://arxiv.org/html/2602.05340v1#S3)

**Bennouna et al. (2025; 2026).** The 2025 Definition 1 concerns recovering the optimal solution set from linear data. Its geometric theorem, under its assumptions on the uncertainty set, is data sufficiency iff relevant directions lie in the data span. This already settles a central form of “learn decision-relevant directions rather than the whole parameter.” A instead prices *noisy repeated acquisition*: how much each true-only direction must be sampled and why optimizing a particular surrogate refuses to sample it. Equations A3–A4 are the useful difference. Do not sell A as broader linear-optimization sufficiency. [2025 primary paper](https://arxiv.org/pdf/2505.21692), [2026 extension](https://arxiv.org/abs/2602.15365)

**Schutte et al., Sufficient Decision Proxies (2026).** Their proxy is a representation/scenario used in downstream decision-focused optimization; they characterize when such proxies retain optimal decision quality. A's frozen proxy is an alternative set inside an information-allocation game. Representation sufficiency and experiment-design sufficiency are different questions. A adds the effect of *optimizing that experiment-design proxy*, quantified by A1–A4; it does not refute their sufficient-proxy theorem. [Primary paper](https://arxiv.org/html/2505.03953v3)

**Garivier–Kaufmann; Degenne–Koolen; Jourdan–Mutný–Kirschner–Krause; Qin–You; Wang–You.** Characteristic games, different measurement and answer sets, multiple correct answers, tracking and GLR stopping belong to this literature. Jourdan's CombGame specifically gives oracle-efficient combinatorial methods with asymptotic optimality and finite-time guarantees. A7 is an attainability bridge using established machinery, not the novelty headline. These frameworks do not by themselves calculate A1–A3 or identify the true-only directions and demands in A4. They are often broader and more algorithmically efficient than A's construction. [Jourdan et al.](https://proceedings.mlr.press/v132/jourdan21a.html), [Degenne–Koolen](https://arxiv.org/abs/1902.03475), [Wang–You](https://arxiv.org/abs/2606.21889)

**A's defensible chain:** actual compression alternatives → optimized surrogate loses the true-only directions → every nearly optimal surrogate design suffers quantitative starvation → repair requires a surrogate-value budget → corrective exploration fixes the sequential cost exponent. Removing “compression” from the motivation does not make this package generic, but the exact family and the operational link must remain visible.

## B — which distinguishability order is sufficient for the decision?

### Current result package

Let A(w) be the nonempty set of acceptable answers in world w. H is unsafe when ∩w∈H A(w)=∅. Pair order sep(w,v) is derived from the observation channel, not freely assigned after looking at the desired answer.

**B1, geometry/order.**

\[
s_* = \max_{H\text{ unsafe}}\min_{w\ne v\in H}\operatorname{sep}(w,v).
\]

This is the least order at which every remaining ambiguity class has a common answer. No unsafe H means a zero-query common answer. For A(w)=W\{w}, the only minimal obstruction is W, so s_safe=min_pair sep. For identification A(w)={w}, each pair is unsafe and s_id=max_pair sep. The no-diagonal condition is essential.

**B2, information bottleneck.** Given symmetric per-query divergence bounds κ,

\[
t_* = \min_{H\text{ unsafe}}\max_{w\ne v\in H}\kappa(w,v).
\]

Some world under every correct finite-horizon policy satisfies

\[
E_wN\,t_*\ge\frac{1-\delta}{|W|-1}\log(1/\delta)-\log2.
\]

A tournament upper bound requires actual tests with error at most exp(−cnκ), not just an upper bound KL≤κ. On a graded channel κ=C h^(2 sep), t*=C h^(2s*). Matching testability then gives the h-exponent and log(1/δ) dependence, for fixed finite W. The displayed upper construction has |W|² overhead; this is not a new exact instance-optimal characteristic constant.

**B3, same-channel arbitrary exponent separation.** On the parity channel,

\[
Y_j=v(j,w)\prod_{\ell\le j}Z_\ell+
\frac h j\sum_{\ell\le j}Z_\ell+\xi,
\qquad\xi\sim N(0,\sigma^2),
\]

one obtains s_safe=1 and s_id=m−1, with matching costs

\[
N^*_{safe}=\Theta(h^{-2}\log(1/\delta)),\qquad
N^*_{id}=\Theta(h^{-2(m-1)}\log(1/\delta)).
\]

These are h→0 rates at fixed m,σ. They are not dimension-uniform complexity statements as m grows with h.

**B4, a latent function and a query-class bound.** For r≥2,

\[
F_{u,v}(z)=3u z_1-2z_2-2z_3+v\prod_{\ell=4}^{r+3}z_\ell,
\qquad Y=F_{u,v}(Z)+h\langle a,Z\rangle+\xi,
\quad\|a\|_1\le1,
\]

the real Gaussian-mixture densities satisfy uniformly over admissible probes

\[
\chi^2(P_{u,+}^{a},P_{u,-}^{a})\le C_r h^{2r},
\qquad\chi^2(P_{+,v}^{a},P_{-,v}^{a})\le C_u h^2.
\]

Exact iterated differences and an integrable density floor prove these bounds. Bounded sine/cosine feature decoders attain the corresponding orders. The adaptive protocol is formalized for arbitrary **finite menus** of admissible linear probes; matching upper bounds require a menu containing the exhibited decision/tail probes. The stopped extension covers almost-surely stopping policies with the stated level-2δ truncation step. Do not replace this with “arbitrary adaptive real-valued query selection” without a continuous query kernel bridge.

Lean anchors: `LeanPaperBObstructionLawV1:248,430,499`; `LeanPaperBParityFinishV1:99`; `LeanPaperBFamilyChannelV1:386,446`; `LeanPaperBFamilyDecoderV1:522,550`; `LeanPaperBStoppedLawV1:538,566`. The family safe correspondence is used in the statistical formalization; the separate physical-loss identification must remain distinguishable from that definition.

### Closest comparisons

**Javdani et al. (2014), decision-region determination.** Their splitting hypergraph already collects hypothesis groups not jointly contained in a successful decision region, and cutting these hyperedges characterizes successful decisions. Thus neither overlapping answers nor multi-world obstructions are new concepts. B adds a graded *continuous noisy observation channel*, proves which order must resolve the obstruction, and derives matching small-h rates on explicit channels. B1 alone is mostly a useful re-expression; B1+B2+B3/B4 is the contribution. [Section 3.2](https://proceedings.mlr.press/v33/javdani14.pdf)

**Degenne–Koolen and multiple-answer pure exploration.** Their characteristic game already captures the fact that identifying an acceptable answer need not identify the world. B's t* is a coarser obstruction-based quantity, not a uniformly sharper replacement. Its value is interpretability: compute a distinguishability exponent from the geometry, then prove a channel realizes it. The tournament theorem remains conditional on pairwise testability. [Primary paper](https://arxiv.org/abs/1902.03475)

**Donoho–Liu, Geometrizing Rates II.** Hellinger continuity moduli already connect a target functional, statistical indistinguishability and minimax rates. Therefore “the target controls which statistical differences matter” is occupied ground. B adds finite overlapping answer correspondences, controlled observations and the obstruction/order formula; it is not a replacement for their much broader nonparametric theory. [Primary paper](https://web.stanford.edu/dept/statistics/cgi-bin/donoho/wp-content/uploads/2018/08/GeoII.pdf)

**Ho–Nguyen and weakly identifiable mixtures.** Algebraic cancellations and singularity orders already determine nonstandard parameter-estimation rates. B holds the actual observation channel fixed while changing the target from an acceptable compression to full world identification. It must prove that admissible adaptive probes cannot bypass the hard order. Merely displaying a Taylor series with its first nonzero term at r would not distinguish B. [Primary paper](https://arxiv.org/abs/1501.02497)

**Rioul–Cheng–Guilley (2021).** Their theorem derives a moment-order information asymptotic in a low-SNR Gaussian-noise setting (with explicit scope and higher-order qualifications). B does not invent moment cancellation. Its additional package is uniform information control over a probe class, adaptive transcript lower bounds, constructive upper tests and differing decision/identification exponents. B's all-r bound is for its specific parity mixture, not a general repair of every high-order cumulant expansion. [Theorem 1](https://arxiv.org/pdf/2102.02468)

**Duc–Faust–Standaert (2015), masking security.** This literature already connects masked leakage, repeated measurements, information and attack success. It is wrong to contrast B as the first conversion from leakage order to sample cost. The narrower distinction is B's acceptable-action obstruction, comparison of two targets on one channel, and matching testing rates under its precise linear-probe experiment. Security of general leaking circuits is a different, broader direction. [Primary paper](https://www.iacr.org/archive/eurocrypt2015/90560210/90560210.pdf)

**B's defensible chain:** actual query channel → order-indexed indistinguishability → common-answer obstruction → necessary decision order → uniform per-query information bounds → adaptive lower bound and attainable decoder → two different rates on the same channel. The individual concepts are established; the completed interaction is the candidate contribution. Its construction should not be advertised as a general separation for arbitrary physical compression functions.

## C — the exact price of marginal balance across all budgets

### Current result package

A law P draws one permutation π, then all interior drop budgets use its prefixes. With signed weights g, let

\[
r_k(\pi;g)=\frac{|\sum_{j\le k}g_{\pi_j}|-min_{|S|=k}|\sum_{i\in S}g_i|}{\|g\|_1}.
\]

The band is |P(i belongs to prefix k)−k/m|≤η/m for every item and budget. V=inf_P max_k E_Pr_k, over all such laws, not just the construction's small menu. On g_m, ||g_m||1=D=m+4 and Vfree=2/[D(m−1)].

**C1, even frontier, m≥4.**

\[
V_m(\eta)=\max\{2/[D(m-1)],4(1-\eta)/(mD)\},
\quad\eta_*=(m-2)/(2(m-1)).
\]

**C2, full odd frontier, m≥3.**

\[
V_m(\eta)=\max\left\{\frac{m+3-(m+1)\eta}{mD},
\frac2{D(m-1)}+\frac{(1-\eta)_+}{mD}\right\}.
\]

The kink is η_t=1−2/[m(m−1)]; the free threshold is η=1. At zero band, V/Vfree is 2(m−1)/m for even m but (m+3)(m−1)/(2m) for odd m. The latter is Θ(m), although both normalized absolute values vanish with m.

**C3, budget selected after the draw.** W=inf_P E_P max_k r_k satisfies

\[
W_m(\eta)=\begin{cases}2/D&m\text{ even},\\
[2+2(1-\eta)_+/m]/D&m\text{ odd}.
\end{cases}
\]

Without the band Wfree/Vfree=m−1. Yet the band multiplies W by at most 1+1/m, while it multiplies V by Θ(m) in odd size. These two costs do not multiply. This is more informative than the familiar inequality max E≤E max.

**C4, perturbation scale.** The physical objective has an envelope |V(g',η)−V(g,η)|≤3||g'−g||1/d under the stated positive-normalizer lower bound d and recomputed baselines. For odd m, small perturbations ε≤1/(2m) retain price at least (m−1)/4. For ε in [1/m,1/6], every admissible perturbation with positive free value retains price at least 1/(16ε), and a particular one-item move of size ε has price at most 10/ε. These are lower and attained-upper bounds on the **infimum remaining price** at that size, not a claim that every perturbation collapses the price. Uniform scaling is a simple counterexample to the latter reading.

Lean anchors: `LeanPaperCEndpointLawV1:622`; `LeanPaperCOddFrontierV1:452`; `LeanPaperCExPostBandV1:402,411`; `LeanPaperCCollapseScaleV1:316,396`; physical identification in `LeanPaperCBaselineAttainV1:226` (`family_regret_identification_unconditional`) and `LeanPaperCStabilityFamilyV1:62` (`trueValue_family`); flow equality in `LeanPaperCFlowObjectiveV1:48` (`value_eq_flow`).

### Closest comparisons

**Singh–Joachims (2018), Singh–Kempe–Joachims (2021), Diaz et al. (2020).** Stochastic rankings, exposure constraints and all-k per-item probabilities are prior art. The 2021 paper explicitly says a doubly stochastic marginal rank matrix contains all information relevant to its objective. C differs mathematically because E|Σprefix g| depends on the *joint law*, not solely on individual rank marginals. C1–C3 solve the resulting signed-cancellation minimax objective exactly for a family, rather than just introducing constrained randomized rankings. Their utility models and empirical deployments remain more general/practical in other directions. [2021 primary paper](https://proceedings.neurips.cc/paper/2021/file/63c3ddcc7b23daa1e42dc41f9a44a873-Paper.pdf), [2018](https://arxiv.org/abs/1802.07281)

A concrete distinction: use four labelled weights (+1,+1,−1,−1). The uniform rotations of an alternating order and of a ++−− order both have every item uniform in every position. Nevertheless E|prefix_2| equals 0 and 1 respectively. This illustration is an elementary calculation, not claimed as a new theorem or a formalized artifact.

**Bernstein et al.; Disser et al.; incremental submodular maximization; universal knapsack.** A single order serving multiple budgets is established. C does not improve their approximation ratios. It gives exact values against the budget-specific optimum under marginal bands for a nonmonotone signed objective, together with the parity and timing effects C1–C3. [Incremental maximization](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2023.47), [incremental submodular maximization](https://arxiv.org/abs/2606.28558)

**Prefix discrepancy and Steinitz theory.** Controlling signed prefix sums is classical; choosing signs, choosing an ordering and choosing a band-constrained law on orderings are distinct feasible sets. C's additional statements are the exact regret-relative-to-each-budget and marginal-band frontiers, not the discovery of cancellation or balanced prefixes. [Prefix discrepancy](https://arxiv.org/abs/2111.07049)

**Koike–Lin–Wang, Joint mixability and notions of negative dependence (R0817 in the supplied queue).** Their formulation includes minimizing a worst expected cost of subset sums under fixed marginals; the quadratic-cost results characterize appropriate joint mixes. Thus a claim that optimizing dependence against unknown subsets is new would be false. C restricts realizations to permutations of a fixed multiset, imposes item-level prefix bands, subtracts a separate best-subset baseline for every k, and obtains C1–C3 for absolute signed-prefix regret. The symmetric quadratic-cost theorem does not directly evaluate this nested-prefix, absolute-value problem. [Equations 8–11 and Theorem 4](https://arxiv.org/html/2204.11438v4)

**C's defensible chain:** physical compression regret → joint permutation law across budgets → marginal balance restricts cancellation → exact parity-dependent frontier with same-law attainment → changing when the budget is chosen changes the price → perturbations quantify when the large ratio survives. The family restriction remains substantial; no arbitrary-weight exact formula has been proved.

## What should not be counted twice

1. A new name for KL games, multi-answer GLR, mixture martingales, tracking, KKT, flow conservation or Birkhoff decomposition is not a new contribution.
2. A2's near-optimal mass inequality and A4's Jensen step are not independently difficult breakthroughs. Their role is to connect the specific true-alternative geometry to the operational consequence.
3. B's obstruction terminology has a direct decision-region precedent; its matching theorem must retain pairwise testability, finite-menu scope and fixed-dimension constants.
4. C's max E vs E max distinction is standard. The exact two values, parity frontier, and interaction of their penalties are the additional result.
5. Lean establishes the stated results under their hypotheses; it supports reliability rather than proving literature novelty. Numerical tables and plots likewise do not establish absence of prior work.

## Evidence from experiments: what it contributes to this comparison

The existing artifact audit supports numerical examples, not novelty by performance alone. A's rational game panel supports optimized geometry; the deployed learner does not empirically establish the ideal asymptotic theorem, and its swapped-answer case is weak. B's decoder panel contains budget upper certificates and censoring; it does not measure an optimal adaptive minimax cost. C's independent LP grid agrees with the exact formulas, but the all-m result comes from the proof. These distinctions were retained; no new benchmark runs were used here.

## Conclusion for positioning

The strongest presently defensible additions are A3–A4, B's completed geometry-to-channel-rate package, and C1–C3 with C4 as a strengthening. They are not universal improvements on every paper in the corpus. The 82-entry crosswalk marks which prior results are reused, which are adjacent and which demand a direct comparison. For the closest primary sources inspected, no equivalent of these *complete scoped packages* was identified; this is a bounded literature finding, not a proof of originality or publication acceptance.
