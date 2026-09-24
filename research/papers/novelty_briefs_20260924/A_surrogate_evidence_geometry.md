# Brief A — "Optimising a surrogate can cost the decision"

Read `00_PROTOCOL.md` first. Manuscript: `research/papers/_tex/paper_a.tex`. Claim map:
`research/papers/THEOREM_MAP.md` (table "State on 2026-09-24").

**Place in the programme.** The price of solving the wrong intermediate problem: here,
optimising the wrong *oracle*. The contribution must be carried by the optimised
surrogate/decision separation and its realisable geometry. Multiple-answer exploration,
mixture martingales and Track-and-Stop are reused machinery.

## 1. The model, self-contained

- **Cells and observations.** Finitely many cells `e`. Querying cell `e` returns one
  observation `Y ~ N(θ_e, v_e)` with a known variance `v_e > 0`. One query costs one
  observation.
- **The decision is a compression.** There are two "arms": arm A with 2 cells, arm B with
  `2 + 2r` cells (2 anchors and `2r` middle cells). Retaining an arm loses the other arm's
  range: `L_λ(retain A) = range(λ_B)/2` and `L_λ(retain B) = range(λ_A)/2`. An answer is
  correct at `λ` when its loss is minimal.
- **World and parameter class.** The world is `θ_A = (−1/2, 1/2)`,
  `θ_B = (−1/8, 1/8, 0, …, 0)`. Variance is 1 on the four anchors and `M` on the `2r` middles.
  The parameter class `Θ₀` is the *centred* class (both uniform-product marginals recover
  their coordinates).
- **True alternative set.** `Alt(T) = {λ ∈ Θ₀ : L_λ(T) > min_S L_λ(S)}`, with a strict
  inequality.
- **True information game.**

      J_true(w) = inf_{λ ∈ Alt} Σ_e w_e (θ_e − λ_e)² / (2 v_e),
      Γ_true = sup over allocations w of J_true(w).

- **The surrogate** (the "frozen-linear proxy", a common practice). Freeze, at their current
  indices, the cells realising each range's max and min in the loss formula, and drop the
  ordering constraints. Each alternative region becomes a half-space, which gives the game
  `J_proxy`, `Γ_proxy`. It does **not** forbid other cells to move; it changes the geometry
  of the alternative set.

## 2. Headline claims (the objects to test)

| id | claim | quantifiers / scope that carry it |
|---|---|---|
| **A-H1** | **Separation after optimisation**: `Γ_proxy = 9/512` exactly, and `9/(128(4+2rM)) ≤ Γ_true ≤ 1/(8rM)`, so `Γ_true/Γ_proxy = Θ((rM)⁻¹)`. At `M = 1` (unit variance) no constant-factor approximation holds as `r → ∞`. | Both games are optimised over allocations, over the SAME centred class, at the same world, under the same observation law. The gap comes from adding actions, not from inflating a variance. |
| **A-H2** | **Starvation**: every exact maximiser of the proxy game puts zero weight on the middle cells and has `J_true(w) = 0`, while `Γ_true > 0`. A `ξ`-optimal proxy design has `J_true(w) ≤ 64ξ/(9rM)`. | A statement about EVERY optimiser, not one found by a solver. Solving the proxy more accurately drives the design towards zero true information. |
| **A-H3** | **Repair frontier**: `F(β) = sup{J_true(w) : J_proxy(w) ≥ (1−β)Γ_proxy}` satisfies `9β/(128(4+2rM)) ≤ F(β) ≤ β/(8rM)`, attained in order by the explicit mixture `(1−β)w_proxy + β w_cert`. | Two-sided and of the same order. It is a law for this compression problem, not a general repair theorem. |
| **A-H4′** | **Attainability**: a specified ideal learner is δ-correct and `E τ_δ / log(1/δ) → 1/Γ_true` on this family, with `E τ_δ < ∞` at every δ. The learner has a warm start, an oracle maximising the TRUE `J` over (answer × a simplex grid of mesh `1/(s+1)`), forced uniform mixing `1/√(s+1)`, cumulative-quota tracking, and an exact GLR stop at threshold `log(1/δ) + ½Σ_e log(1+N_e/a)`. | Unboxed parameter class. It is an idealised Track-and-Stop-type learner (exact infima). Claimed only as *attainability of the true benchmark*, not as a new algorithm. |
| **A-H5′** (proved 2026-09-24, oracle allocation) | **Sample-cost separation**: the learner that tracks ANY exact optimum of the frozen surrogate game (warm start, forced exploration `1/√(s+1)`, tracker `argmax(s w⋆ − N)`, GLR stop against the true alternatives) has `E τ_δ ≥ (KM/8)² log²(1/δ)`, `K = 4+2r`, while the ideal learner has `O(log(1/δ))`; the ratio is unbounded. | The design is the surrogate optimum AT THE TRUE WORLD, held fixed. Proved for this stopping rule, not for every δ-correct rule. A learner re-solving the surrogate at its estimate is not covered. Search question: is `Ω(log²)` for a fixed design starving the informative arms, under `√t` forced exploration, already known (e.g. in the forced-exploration analyses of Track-and-Stop, or in the 'sub-optimal allocation' lower bounds)? |

## 3. Already conceded — check that our description of each is fair

- Degenne & Koolen, "Pure exploration with multiple correct answers", NeurIPS 2019: the
  multiple-answer lower bound and Sticky Track-and-Stop.
- Wang & You, "Information games with multiple correct answers and piecewise-convex
  alternative sets", arXiv 2606.21889 (2026). We say it leaves an exact stopping threshold
  problem-dependent and labels part of its scaling argument heuristic. **Verify this.** Also
  check its acceptance-set, convex-pitfall and cost-aware-sampling results for any
  surrogate-vs-true separation.
- Schutte et al., "Sufficient decision proxies for decision-focused learning", arXiv
  2505.03953 / IJCAI 2026: proxy insufficiency itself is theirs.
- Bennouna et al., "Data informativeness in linear optimization", arXiv 2602.15365.
- Tosh et al. 2022 (arXiv 2210.12122) and Filstroff et al. 2021 (arXiv 2106.04193): targeted
  active learning.
- Wan, Liu, Grigas, Shen 2026, "Decision-focused sequential experimental design", arXiv
  2602.05340.
- Tang, Sloman, Kaski 2026, "Error amplification under model misspecification".
- Nitinawarat & Veeravalli: controlled sensing.
- Pukelsheim, *Optimal Design of Experiments*.
- Mixture martingales and confidence sequences: Kaufmann & Koolen, "Mixture martingales
  revisited", JMLR 2021; Howard et al., time-uniform confidence sequences.

## 4. Candidate collision zones (candidates only — verify each exists and says what we suspect)

**Z1. Pure exploration with a structured answer function.**
Candidates:

- Garivier & Kaufmann, "Optimal best arm identification with fixed confidence", COLT 2016;
- Kaufmann, Cappé, Garivier, JMLR 2016;
- Degenne, Koolen, Ménard, "Non-asymptotic pure exploration by solving games", NeurIPS 2019;
- Juneja & Krishnasamy, "Sample complexity of partition identification using multi-armed
  bandits", COLT 2019;
- Garivier, Kaufmann, Koolen, "Maximin action identification", COLT 2016. The decision there
  is a max of mins, structurally close to comparing ranges.

Questions:

- (a) Is a range comparison (max − min within a group) treated as an answer function
  anywhere, with its characteristic time computed?
- (b) Does any work compare the characteristic time under a *relaxed or linearised*
  alternative set with the true one after optimising allocations? A proof that the relaxed
  optimum carries zero true information would collide with A-H1/A-H2.

**Z2. Misspecified or approximate structure in identification.**
Candidates:

- Réda, Tirinzoni, Degenne, "Dealing with misspecification in fixed-confidence linear top-m
  identification", NeurIPS 2021;
- Tirinzoni & Degenne 2022 (elimination strategies);
- work on "local versus global" alternative sets and convex relaxations of the alternative
  set.

Question: is the loss from optimising a surrogate alternative geometry quantified, and is a
starvation phenomenon shown?

**Z3. Decision-focused and targeted experimental design.**
Candidates:

- Schutte 2026, Wan et al. 2026, Filstroff 2021, Tosh 2022, Bennouna 2026 (see §3);
- Elmachtoub & Grigas, "Smart predict, then optimize";
- Russo & Van Roy, information-directed sampling;
- Lindley's information measure and Chaloner & Verdinelli's review;
- c-optimality and Elfving's theorem (designing for one functional versus a surrogate
  criterion).

Question: is there a theorem that an optimal design for a proxy criterion has zero
information for the actual decision, with an explicit unbounded ratio? That would collide
with A-H2.

**Z4. Constrained and compound optimal design.**
Candidates:

- Cook & Wong, "On the equivalence of constrained and compound optimal designs" (1994);
- the constrained-design literature (maximise one criterion subject to an efficiency
  constraint on another).

Question: does the general theory make `F(β) = Θ(β)` immediate (concavity plus a mixture)?
If so, A-H3's contribution is only the explicit constants on this construction, and the
manuscript must say so.

**Z5. Formalisation.** Degenne and co-authors have a Lean library for testing lower bounds
(verify the name and scope). This is relevant only if we claim formalisation novelty; we
should not.

## 5. Hostile questions for the researcher to answer explicitly

1. Take the best-known multiple-answer result and relabel cells as arms and the retained arm
   as the answer. Does it already give `Γ_true` for this family? We do not claim the
   framework, but do they compute this game?
2. Is "freeze the extremum indices and drop the ordering constraints" a named approximation
   in the literature (a linearisation of max/min functionals)? Does a known result bound its
   error?
3. Does any work prove that an *exactly optimal* surrogate design is uninformative for the
   true decision, as opposed to merely suboptimal?
4. For A-H5: is `Ω(log²(1/δ))` for forced exploration at rate `t^{-1/2}` a known lower bound
   for Track-and-Stop variants run with a wrong oracle? The mechanism: a √t exploration budget
   on the informative cells.

## 6. Search strings (starting points)

- "pure exploration" "multiple correct answers" relaxation OR surrogate OR linearized
- "characteristic time" "alternative set" convex relaxation
- "partition identification" bandits range OR "max-min"
- "maximin action identification"
- "decision-focused" "experimental design" proxy "zero information" OR starvation
- "optimal design" surrogate criterion "decision" misspecified
- "constrained optimal design" "compound" equivalence efficiency
- "Track-and-Stop" misspecified oracle "sample complexity" "log^2"

Screen `research/literature_audit_20260921/queries.json`, groups `A_identification` and
`A_decision_design`, first.
