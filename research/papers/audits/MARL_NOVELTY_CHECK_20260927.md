# MARL direction: novelty check, story, distance to the finish (27/09/2026, 20:40)

- A targeted web search, not exhaustive. It adds to `MARL_PRIOR_ART_RECOURSE_AND_A_ROLE_20260927`
  and to the collision table in `MARL_STORY_VERDICT_20260927`.
- No ledger is edited.
- A source listed as "read" means its abstract, or the page summary returned by the fetch. Nothing
  was read in full here.

## New prior art found and how it touches each layer

| Layer | Closest prior | Effect on the claim |
|---|---|---|
| Nested priority used for all budgets (motivation) | Yazgan–Mueller–Zoellner, *Dense Coverage, Sparse Refinement: Byte-Constrained Cooperative Perception*, arXiv 2609.29456 (Sep 2026). One model, deterministic ranked-prefix selection, "changing the byte budget simply truncates the same ranked list"; per-cell scores, no interactions, **no theory**. | Strong, current motivation. Deployed V2X systems nest exactly as we analyse; our theory says when that is free (2δ margin) and what it costs otherwise. Must be cited as the empirical counterpart. |
| Price of nesting (concept) | Successive refinement: Equitz–Cover (1991), and Lastras–Berger, "all sources are nearly successively refinable" (rate loss ≤ ½ bit/sample). | The conceptual ancestor in information theory: nested descriptions for every rate, with a bounded price. Our object is a discrete set function with interactions. The analogy must be stated, and the priority must not be overclaimed. |
| One order for all cardinalities | Incremental maximisation: Bernstein–Disser–Groß–Himburg; Bienkowski et al., *Incremental Submodular Maximization: Better Than Greedy*, arXiv 2606.28558 (ratio 1.373, lower bound 1.25); *Incremental–Decremental Maximization*, arXiv 2508.14516. | Already known collision. Their results are competitive ratios for submodular classes. Ours are an interaction-parameterised zero-price threshold, a sharp constant 2, the revision frontier (d−R)₊ and a non-submodular class. |
| Commit, then repair | Recoverable robust selection (Chassein et al. 2018; k-delete recoverable robust, arXiv 2609.29478, Sep 2026; Münch–Raach–de Vries 2025). | Uncertainty there is in costs or deletions, not in the cardinality; no learning cost. The collision is in the concept, not the theorem. |
| T2: calibration cost of a repair | Change of measure and track-and-stop (Kaufmann et al.); multiple correct answers (Degenne–Koolen, NeurIPS 2019); combinatorial pure exploration with full-bandit feedback (Kuroki et al. 2020; Rejwan–Mansour 2020; Du et al., AAAI 2021, where lower bounds for nonlinear rewards are listed as open). | The machinery is prior. The specific content is: dependence on the reachable-repair geometry (\|Amb\| grows with R; `amb_card_ge_gap`); the two-cost law (R lowers the floor and raises the calibration cost; E1b crossover); proxy starvation. |
| T2: the log\|Amb\| gap | Adaptive sensing: Haupt–Castro–Nowak, *Distilled Sensing* (2011); Castro, *Adaptive sensing performance lower bounds*, Bernoulli 2014. Adaptivity removes a log p factor that non-adaptive designs must pay. | **`LeanMarlCalibrationGapV1` plus the two-stage diagnostic re-derive a known phenomenon in our model.** Present it as "the known adaptive-sensing gap appears exactly here", with citation. Not a contribution. |
| T2: shared pair class | Learning hidden graphs with edge-detecting queries (Angluin–Chen, O(log n) per edge; hypergraph lower bounds); noisy adaptive group testing via binary search (arXiv 2106.12193). | A pair world is a single hidden edge with noisy edge-detecting queries. With unrestricted queries the cost is logarithmic (group testing). Our `pair_legal_lower` is the legality-restricted version (cover ≤ R·k), which is the specific part. Tightness is open and probably needs group-testing designs. |
| MARL communication under bandwidth | SchedNet, IMAC, Where2comm, SLIM (2605.21085), BVME (AAMAS 2026, 2512.11179), AgentComm-Bench (2603.20285). | Budget-agnostic learned communication with theory for revision was not found. Generic selection is not novel. |
| Interactions break pairwise/first-order scoring | *Pairwise Approximation Can Select the Wrong Multi-Robot Plan*, arXiv 2609.29929 (IROS 2026 workshop). | Supports the motivation; empirical only. |

## Where novelty stands

- **Defensible core, with no equivalent found:**
  - the interaction-parameterised theory of universal nested priorities: zero price under a 2δ cut
    margin, sharp constant, the revision frontier 2(δ+u)(d−R)₊ + 2ε + ν + ζ, blockwise per-receiver
    frontiers;
  - nesting degree ⌊(m+1)/4⌋ and the higher-order obstructions;
  - the two-cost law, stated on the reachable-repair geometry.
- **Instantiations of known theory**, which must be cited as such:
  - the change of measure and multiple answers;
  - the adaptive-sensing log gap;
  - pair-class counting as edge-detecting queries.
- **Empirical.** Oracle-level traffic diagnostics; a controlled executable task (E1b). **No
  successful learned MARL method.**

## Story

- A coherent version: "Deployed systems nest (Matryoshka, Where2comm, ranked-prefix V2X). We prove
  when nesting is free, what bounded revision buys, and what it costs to learn which revision. On
  traffic we find that the binding constraint is score error and actor-response prediction, not
  nesting."
- The story is an analysis paper, not a methods paper.
- Weak points:
  - the traffic half is diagnostic or negative; only the heterogeneous-receiver oracle shows
    revision headroom;
  - the two-cost law is shown only in a controlled task;
  - several T2 results are re-derivations.

## Distance to the finish

- **Finish line A: analysis paper, this cycle.**
  1. The `smokeMARL17` gate, then the next gate for BlockFrontier, Starvation, CalibrationGap,
     PairCalibration and AuditBridge.
  2. Optional math that strengthens the bridge:
     - realise the edge-local hypothesis on the E1b Bayes decoder (η = β²/2 expected);
     - the all-budget table;
     - the probabilistic δ_U certificate.
  3. A related-work section built from the table above.
  4. The manuscript, entered only from gated Lean.
  5. Update figures 2 and 4 (two-stage, pair).
  6. An independent audit and a fresh novelty pass before submission.
- **Finish line B: the original scope with a learned MARL method.** Blocked by the audit stop rule.
  It needs an actor-response predictor usable with legal information, then E2 and E3 with training
  seeds and SchedNet and direct-selector baselines. Not reachable this cycle.
