# Novelty decisions from the current evidence

The strongest new direction in this pass is an explicit reference-dependent same-response minimax law, with a dimensional transition at t=Theta(1/k). It extends a compiled corner construction into a testable quantitative theory. It does not establish that no previous paper contains an equivalent result: the comparisons below delimit known overlaps rather than certify absolute novelty.

## Evidence that survives the audit

The Functional confirmatory artifact (300 instances, 1,800 policy runs) reproduces the 2.66977 ratio of medians and the 163/163 conditional paired wins against uniform. The conditional median paired ratio is 2.183147 with distribution-free 95% interval [2.067163,2.324163], ranks 69 and 95 among 163 pairs. These are different estimands. There are 86 instances certified by no variant, median true gap 0.05648263; the 88 not certified by C_anytime have median gap 0.05977322. Fresh analysis with input and script hashes is in `functional_pairing_provenance_v3.json`.

A newly verified design fault invalidates the proposed same-seed horizon comparison: only 1/100 seed-8301 instance gaps agree between horizons 65,536 and 131,072. A shared sequential RNG consumes more noise before constructing the next world. Within-run policy pairing remains valid. The new optional `instance_cell_v1` protocol uses separate world and per-cell RNGs, stores world fingerprints, and preserves each cell's noise prefix across horizons. Horizon-dependent Bonferroni thresholds still differ, so even the repaired coupling does not make the policies a single nested stopping trajectory. Existing artifacts are preserved.

The completed-experiment audit recomputes 35 saved frontier witnesses from rational world values, including all 17 m=6 and 9 m=8 grid points. All attain k(2-rho) for the actual optimum over all retained k-subsets. An independent universal upper theorem certifies those points despite the restricted search ansatz. The code's description of active-set rational vertex recovery was inaccurate: it actually rounds candidates and verifies feasibility; that description is corrected.

Ten integer-block seeds contain 16.8 million trials across 84 pooled cells. Pooled MSE/theoretical-variance ratios range from 0.991511 to 1.007047; all are inside their 95% simultaneous chi-square envelopes. Exact binomial comparisons yield no rejection after Bonferroni correction across cells. This supports the two named block designs and their fixed-threshold estimator law. The threshold is mu0=0.75, not the true allocation phase boundary, so it does not close adaptive matching regret.

Structural's scalar reachability/set-cover computation agrees with independent permutation enumeration at eight curve breakpoints on three models, including the scalar chi5 witness. Four staircase configurations reproduce the saved curves. Hand-entered m=12 rows, the retracted factor-two claim and a universal coefficient-precision conclusion are not usable evidence. The last two unsupported output descriptions were removed or qualified for future runs.

## Collision map and the stronger target for each paper

| Paper | What is already occupied | More defensible next target |
|---|---|---|
| D6 | Generic information lower bounds, optimal allocation and Track-and-Stop asymptotics are established frameworks. A fixed-model Gamma theorem alone is a completion result. | The explicit joint law in dimension, reference and margin; then an adaptive algorithm attaining the original legal-query benchmark with uniformly controlled exploration and phase crossings. |
| Structural | A single ordering whose prefixes work across cardinalities is an established incremental-optimization problem. | The minimum number of rankings for additive normalized error in cancellation/support geometry; a sharp width-independent Theta(1/epsilon) law and the precise geometry needed for its constants. |
| Support | Overlapping decision regions, identifiability and cost-sensitive test selection are not new in isolation. Combinatorial and noisy data sufficiency are also covered by recent work. | Exact obstruction size and adaptive query costs realized by actual support geometry under the physical query restrictions; quantify the effect of partial-safe decisions instead of only zero-error identification. |
| Functional | Variance-aware sampling and the small cost of estimating unknown variance are known; identifying the best of unknown functions is also studied. | Exact least-cost alternatives when the maximizing/minimizing response coordinates can change, with allocation computed from that full alternative set. The binary pair-flip formula is a baseline, not the headline. |
| Query | Identifiability from a representation is a broad pre-existing principle; current synthetic floors do not establish runtime transfer. | A paired obstruction and repair: identical available representation, different correct continuation, and an explicit minimal extra observation that removes the floor in real executable tasks. |
| MASTER | Task-specific data sufficiency and the value of extra information are established decision-theoretic notions. | A proved regret floor for evidence type A plus a matching priced acquisition law for evidence type B on the same concrete CIG family, including all query costs and a stated comparator. |

The mapping is an analytical judgment based on the papers below and the local theorem statements, not a declaration that any paper is publishable already.

## Primary-source checks that change the decisions

Bennouna, Bennouna, Amin and Ozdaglar, *Data Informativeness in Linear Optimization under Uncertainty* (2026), explicitly extend the characterization to combinatorial decisions in Corollary 1 (PDF p.15), and give noisy-observation guarantees in Proposition 10 (PDF p.52). Proposition 10 is a perturbation result for a sufficient, preselected query set; it is not an adaptive stochastic query-complexity theorem. Their introduction explicitly studies non-adaptive selection. Therefore neither “only LP” nor “already solves our adaptive physical-query problem” is an accurate boundary. [Full paper](https://arxiv.org/pdf/2602.15365).

Javdani et al., *Near Optimal Bayesian Active Learning for Decision Making* (2014), already formulate overlapping decision regions and develop Hyperedge Cutting with a guarantee against the optimal policy. A three-world pairwise-compatible/global-incompatible witness cannot claim the general decision-region idea. Its value here is realization in the actual support-radius model and the resulting constrained query law. [Paper](https://arxiv.org/abs/1402.5886).

Bienkowski et al., *Incremental Submodular Maximization: Better Than Greedy* (June 2026), study one ordering whose prefixes approximate every cardinality and improve its competitive ratio to 1.373, with a 1.25 lower bound. Structural concerns a menu of rankings, normalized additive error and non-monotone cancellation radii; those distinctions must appear in the theorem and comparison, not just terminology. [Paper](https://arxiv.org/abs/2606.28558).

Jourdan, Degenne and Kaufmann, *Dealing with Unknown Variances in Best-Arm Identification* (ALT 2023), analyze empirical-variance and transportation-cost approaches, time-uniform stopping and the price of unknown variance. The observed near equality of C_anytime and the known-sigma diagnostic is consistent with existing theory, so it is insufficient as the principal novelty claim. [Paper](https://arxiv.org/abs/2210.00974).

Dorn et al., *Functional multi-armed bandit and the best function identification problems*, define best-function identification through the smallest function minimum (Section 2.2) and analyze optimization-based sampling. That is not identical to selecting response ranges, but it prevents claiming that “each arm is an unknown function” itself is new. [Full paper](https://arxiv.org/pdf/2503.00509).

Lengerich et al., *Purifying Interaction Effects with the Functional ANOVA* (AISTATS 2020), already address movement of effects between main and interaction terms and distribution-dependent canonical representations. Modular compensation/reference dependence is a tool here, not the new result; the quantitative minimax loss and its phase boundary are the prospective contribution. [Paper](https://proceedings.mlr.press/v108/lengerich20a.html).

Garivier and Kaufmann, *Optimal Best Arm Identification with Fixed Confidence* (COLT 2016), give characteristic complexity and asymptotically optimal Track-and-Stop. A D6 Gamma claim must explain the extra contribution in growing dimension, legality, latent labels and allocation phase transitions. [Paper](https://proceedings.mlr.press/v49/garivier16a.html).

## The new reference result and its remaining burden

The derivation is in `work/p13_conjectures/D6_REFERENCE_PHASE_DERIVATION_20260911.md`. With a,b,c defined there, put p=rho-2b, r=2a-rho, e=min(a,2b). For (k-2)b>=1, the proposed actual-family minimax theorem has the explicit value

    V_k = (kr-e)_+ [p(k-1)+(e-r)_+] / [4c(k-1)].

The proof reduces actual oscillation to counts, proves every interior action is dominated by a mixture of two endpoint actions, then uses convexity to retain two endpoint world orbits. These steps supply the WLOG argument missing from a numerical ansatz. At t=tau/k this produces a nontrivial limiting floor with boundary 2(1+tau)exp(-2tau)=rho. Small-cube validation is exact; large-k LP values are numerical; separate rational certificates validate the reduced game. The general-reference construction-to-game bridge remains unformalized in Lean.

A potentially stronger follow-up is to treat a reference change as an information-bearing intervention. For one fixed world compensated at t0, the A/B response-slope contrast at t1 is c(t1)-c(t0). A second reference therefore breaks this family's ambiguity. Quantifying its price would connect the D6 floor, Support's query geometry and MASTER's evidence-acquisition problem without merely repackaging general data sufficiency.

## What the confidence-sequence hinge does not close automatically

Gaussian estimates allow a clean confidence sequence, but simultaneous coverage over infinitely many fresh epochs requires an epoch error schedule. For example delta_s=delta/((s+1)(s+2)) is summable, giving width sqrt(2 v_s log(2(s+1)(s+2)/delta)). A fixed multiple of sqrt(v_s log(1/delta)) at every independent epoch fails eventually with probability one. Time-uniform boundaries and their tuning are standard tools, not fresh novelty. [Howard et al., Annals of Statistics 2021](https://arxiv.org/html/1810.08240v9).

An L1 Lipschitz bound in allocation weights does not by itself bound how the optimal weights change with mu at a phase boundary. Nor does a high-probability eventual statement give an expected stopping-time bound without tail/integrability control. Finally, cancellation against an oracle forced to use the same cyclic design establishes that comparator, not the unrestricted legal-query oracle defining the original Gamma. Adaptive matching total regret, termination and the expected original-Gamma rate remain open until these bridges are supplied.

## A benchmark confound in the Functional generator, and the mandatory list it creates

The v3 world generator sorted capacities descending by relation index and pinned the
minimising and maximising responses to actions `0` and `K-1`:

    capacities = np.sort(rng.uniform(.35, 2.0, size=relations))[::-1]
    truth[r, 0], truth[r, -1] = center-cap/2, center+cap/2

Two consequences, both measured rather than argued. The true Top-k was the leading
block `{0,...,k-1}` in every one of the 300 confirmatory instances, and argmin/argmax
were known a priori in every instance. There is a third consequence that is easy to
miss: the selection is taken with `np.argsort(-scores, kind="stable")`, whose tie-break
favours low indices, so a policy holding **no information at all** already returned the
correct set. `false_safe = 0` across 1,800 runs is therefore partly guaranteed by the
generator, not solely by the certificate.

This does not retract any v3 number. The 2.66977 ratio of medians, the 163/163
conditional paired wins and the paired interval [2.067163, 2.324163] remain correct for
what they measure: six policies on worlds whose labels and extrema positions are fixed
and known. What the panel cannot support is a claim about **learning** Top-C when the
label and the extrema positions are both unknown, which is precisely the stronger target
this review already assigns to Functional.

### The mandatory list

| Requirement | Status | Mechanism |
|---|---|---|
| permute relations | implemented | `permute` (default on): the true Top-k is a uniformly random k-subset |
| vary extrema positions | implemented | `random_extrema` (default on): minimising and maximising actions drawn per relation |
| extrema change after perturbation | implemented | `--extrema-shift F`: a fraction `F` of relations has its extrema pair resampled after the world is drawn, holding each capacity fixed |
| baseline with the same information and the same guarantee | implemented | `C_extrema_oracle`: told argmin/argmax, forms its capacity interval from those two cells only; identical Bonferroni contract, identical confidence, still estimates sigma |

All four are in `scripts/run_functional_variance_stopping_lab_v4.py`. Only the generator
and the reporting changed; the certificate, the intervals, the Bonferroni contract and
the allocation rules are v3's, so the two protocols stay comparable and v3 is recovered
exactly by `--no-permute --fixed-extrema`.

`C_extrema_oracle` is the comparator the fourth requirement asks for. It is strictly
better informed and offers the same guarantee, so the gap between it and the deployable
policies is the price of not knowing where the extrema sit — the quantity the v3 panel
could not express because that price was zero by construction.

### The guard, and its first reading

Every run now reports `world_audit.zero_information_accuracy`: the fraction of instances
on which the uninformed guess `{0,...,k-1}` is correct. Under v3 it is `1.0`. Under v4 it
must sit near `1/C(R,k)`. A panel whose value drifts back toward `1` has reintroduced the
confound, and the number appears in the artifact rather than in a commit message.

First smoke panel, 20 instances at seed 701, `R=5, K=6, k=2`:
`zero_information_accuracy` 0.0 against an expected 0.1, `extrema_always_at_endpoints`
0.0, 8 of the 10 possible Top-k sets realised. That panel carries
`development_only: true` and ran under `rng_protocol: legacy_sequential`; it is a
generator diagnostic and is not admissible as evidence under the frozen protocol.

The same panel at `max_n = 4096` gives a second reading that is a result rather than a
diagnostic. Every deployable policy and the known-sigma diagnostic certify **0.00** of
instances; `C_extrema_oracle` certifies **0.15**. Once the extrema must be found, the
certification problem at that horizon is out of reach for every policy that has to find
them, while the same machinery told where to look succeeds on a sixth of instances. How
far this persists at `max_n = 131072` is being measured; if the deployable fractions stay
at zero there, that is itself the quantitative statement of how much the v3 panel was
simplified by fixing the extrema, and it should be reported as such rather than treated
as a failed run.

### What still has to be run before a Functional claim

The confirmatory panel must be rerun under v4 at the frozen seeds, once without and once
with `--extrema-shift`, under `instance_cell_v1`. Until those artifacts exist, the
Functional evidence in this review supports the estimator and stopping comparison only,
and supports no statement about learning Top-C under unknown extrema.
