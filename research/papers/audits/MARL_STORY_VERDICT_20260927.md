# Is the MARL direction the best story the current assets can tell? (2026-09-27, evening)

Inputs, all read in full:
- FULL_CORPUS_AUDIT_20260927 §0–§21;
- MARL_SYNTHESIS_RESEARCH_PROPOSAL_20260926;
- MARL_PRIOR_ART_RECOURSE_AND_A_ROLE_20260927;
- PAPER_C_TRAINED_TRAFFIC_EXPERIMENT_PLAN_20260926;
- PAPER_C_PRACTICAL_TRAFFIC_AND_PRESENTATION_20260926;
- the eleven manuscript digests;
- the literature in audit §11, §20 and below.

## Verdict

Yes, with one reframe and one make-or-break theorem. Among the routes the assets allow, the
commitment/revision story uses the most proved material:
- C: exact randomised laws, band, U/B/V^(R);
- Structural: menus χ, the 2/3 single ranking, ex-ante vs ex-post;
- D6: zero-price threshold 2δ□ and the sharp price constant;
- Unified: support restriction;
- A: surrogate scores starve interactions;
- Functional: certificate lifetime;
- B/Support: decide without identifying.

The alternatives are thinner for a MARL paper:
- B as cooperative active perception: B's laws are static-channel;
- A as interaction measurement: A needs a paid-query model;
- C with a traffic application: C's frontier is degenerate, see below.

**The reframe.** The paper is about the price of NESTING. Universal nested priorities are what
deployed systems use: Matryoshka / nested-dropout representations, Where2comm truncation,
CoLight-style attention ranks, KPrefixNet. No theory of when nesting is free or what it costs
was found. The theory has four layers:
- (i) nesting is free when every consecutive first-order score gap is at least 2δ□, where δ□
  is the largest mixed difference (message interaction) (D6 `margin_two_sufficient`, all-cut
  corollary);
- (ii) otherwise the price at budget k is at most |prefix_k\T_k|·δ□ ≤ min(k,m−k)·δ□, and this
  is sharp (D6 m = 6 family, 2D/δ□ → 6);
- (iii) one ranking is always within 2/3, and menus of χ ≤ ⌊2/ε⌋+1 rankings suffice
  (Structural);
- (iv) what R revisions buy — new, see below.

MARL traffic control is the application. δ□ and the score margin are measured on a set-valued
team critic, and they predict where revision helps.

**Make-or-break.** Every instance computed so far has R* ≤ 1: all of C (audit §18) and the
XOR game. With those instances alone, "limited revision" has nothing to show between R = 0 and
R = 1. The D6 m = 6 family is the natural candidate for a non-degenerate frontier. It has
k = 3 and |S\T| = 3, and the gap approaches 3·δ□ from below. Checking the frontier R = 0..3
on it is a small exact computation. Proving a frontier (d_k − R)_+·δ□ + deficit for arbitrary
retained sets is M2. If the frontier is degenerate on D6 too, the paper must say "one revision
suffices under these conditions" (a positive but narrower result), not "a frontier".

## Collision table (theorem level)

| Prior work | Overlap | Status after our reframe |
|---|---|---|
| Incremental maximisation (Bernstein–Disser–Groß–Himburg 2022; Bienkowski et al. 2026) | one ordering for all cardinalities, competitive ratios for monotone/submodular classes | concept collides; our statements are interaction-parameterised with an exact zero-price threshold and a sharp constant, and they cover a non-submodular loss |
| Recoverable robust selection with commitment/recovery (Chassein et al. EJOR 2018; Math. Prog. 2026; Acta Inf. 2026) | commit, then ≤ k exchanges after the reveal | concept collides; there the uncertainty is in costs or deletions, not in the cardinality; no interaction-parameterised frontier |
| K-adaptability / finite adaptability (Bertsimas–Caramanis; Hanasusanto–Kuhn–Wiesemann; arXiv 2409.12630) | menus of K policies | Structural χ is the menu side; a menu-versus-revision theorem for unknown cardinality was not found |
| SchedNet, IMAC, NDQ, ETCNet, CASEC, SOP-CG, MUTE (2026), CoSLight, CoLight | learned message/neighbour selection, decision-preserving pruning, traffic signal collaborators | generic selection is NOT novel; they are comparators |
| Where2comm (NeurIPS 2022) | one model, varying bandwidth, by truncation | this is exactly our R = 0 baseline |
| SLIM (arXiv 2605.21085, read in full) | a budget β; one model trained per β; no theory | budget-agnostic training plus revision plus theory is open |
| Matryoshka (NeurIPS 2022), nested dropout (2014), FlexRank, NSN, FlexMoE (2026) | nested prefixes for all budgets, empirical | no price-of-nesting theory found; FlexMoE has online budget switching (empirical) |
| "Pairwise Approximation Can Select the Wrong Multi-Robot Plan" (arXiv 2609.29929, Sep 2026) | empirical: F₂ truncation misranks multi-robot plans; the ranking-change identity e_w − e_c > gap | supports the motivation; no threshold theorem, no budgets |
| Sure independence screening, submodularity ratio, Shapley interaction indices | marginal scores vs interactions for selection | known flavour; D6's constant 2δ□, independent of k, with sharp sub-threshold failures, is the specific claim |
| "Don't Fire Together" (Sensors 2026) | a frozen policy plus scheduling plus staleness | position Functional LIFE as a proved validity rule, not as staleness-aware scheduling |

The search was targeted, not exhaustive.

## Is it OK — the risks that decide acceptability

1. **Degenerate frontier.** This is the make-or-break theorem and computation above.
2. **Loss class.** D6's loss is a worst-case half-oscillation on a product space with a
   product reference. The MARL reading: the team critic Q(s, m_1..m_m) over message variables,
   with unheard messages replaced by a reference (cached or predicted) value. The theorems apply
   exactly to that loss, not to expected return. The return bridge is the synthesis memo's T2
   (standard, conditional).
3. **Code.** The existing code does not enforce the message budget at information access
   (`core_behavior.py:474–495` reads every neighbour), and it has no set-valued critic
   (`PolicyValueNet` returns only a scalar value). Both must be built before any MARL number.
4. **Provenance.** The Structural, D6 and Functional modules the paper cites have never been
   gated from scratch (audit §9). The gate smokeOLD7_20260927 is running.

## Work packages (big picture; no scheduling notes)

- **P1 — D6 frontier.** First, the exact frontier computation on the m = 6 family and on D6's
  other witnesses. Then Lean: M1 (all-cut zero price, the price bound with its witnesses) and
  M2 (the arbitrary-set frontier, or the proved degeneracy).
- **P2 — Generic layer.** M4 (C's U/B/V^(R) for an arbitrary set loss, with C as an instance),
  M3 (the XOR game, exact), M5 (menu versus revision: K = 1 ⇔ R = 0; K ≥ χ gives B; one
  separation).
- **P3 — MARL environment.** A CityFlow protocol v0 with the budget enforced at information
  access (absent messages are cached or stale), a set-valued critic interface for measuring δ□
  and the margin, and a smoke episode.
- **P4 — Provenance.** The old-paper gate report (G1), then C's odd one exchange (C1).

## Update, same evening — the theory core is proved (main + P1/P2 handoffs)

**Lean, compiled, standard axioms only, not yet gated:**
- `LeanMarlRevisionFrontierV1` (main), 13 theorems:
  - `exchange_general`: for ANY S, T, ℓ_S − ℓ_T ≤ |S\T|·δ − (σ(S\T) − σ(T\S))/2. The D6
    surplus theorem carried an unused Top-k hypothesis.
  - `potential_lipschitz`, `potential_mono`, `marginal_bracket`: NEAR-MODULARITY. Retaining j
    lowers the loss by between span_j/2 − δ and span_j/2.
  - `revision_frontier`, `revision_frontier_all_budgets`: the score-ranking prefix after R
    replacements has regret ≤ (d_k − R)₊·δ.
  - `price_le_min`: ≤ min(k, m−k)·δ.
  - `revision_full`.
  - `optimal_of_cut_margin`, `zero_price_all_budgets` (M1): nesting is free when every cut
    margin is ≥ 2δ.
  - `hypotheses_satisfiable`.
- `LeanMarlNestingDegreeGeneralV1` (main): `nesting_lower` (|O_j\O_k| ≤ 2R for any chain
  within R), `two_budget_obstruction`, `nesting_degree_lower` (some systems force ⌈⌊(m−1)/2⌋/2⌉
  = ⌊(m+1)/4⌋ revisions), `distance_regret_lower` (a non-degenerate frontier for the price of
  nesting at every m ≥ 7), `nesting_degree_seven`.
- `LeanMarlGenericRecourseV1` (a21917a, M4): U/B/V^(R) for an arbitrary set cost, all order
  theorems, the vacuous band, and C as an instance (rfl).

**Exact computations (artifacts):**
- `P1_d6_frontier/d6_frontier_exact.json`, 1702 checks: on D6's Vb s, F_k(R) =
  (d_k − R)₊·δ·s/(s+1). The frontier theorem is SHARP at every R as s → ∞. But G ≡ 0 there:
  the reverse score order is optimal. **Vb prices the FIRST-ORDER-SCORE priority, not nesting.**
- `P1_d6_frontier/nesting_degree_m*_R*.json` and `nesting_degree/pairwise_characterisation.json`:
  - one revision always suffices for every set loss at m ≤ 6, which explains R* ≤ 1 in C and in
    the XOR game;
  - two are needed at m = 7, and suffice at m = 7, 8;
  - the worst case matches ⌊(m+1)/4⌋ up to m = 11 (m ≤ 7 exhaustive; 8–11 sampled);
  - the pairwise obstruction decides R* exactly for m ≤ 6 and FAILS from m = 7 (3822 of
    756,315 systems): higher-order obstructions over budgets appear, e.g. budgets 2, 3, 4, 5
    jointly.

**The story, sharpened.** Two distinct prices:
- (i) the price of a FIRST-ORDER-SCORE universal priority (attention/importance ranking). It
  is ≤ (d_k − R)₊·δ and sharp, and it vanishes under a 2δ cut margin.
- (ii) the price of NESTING itself, for the best universal order. It is loss-independent
  combinatorics: zero revisions or one suffice for m ≤ 6; ⌊(m+1)/4⌋ are forced in the worst
  case; the obstructions are higher-order.

Measuring (i) versus (ii) on a learned team critic is the empirical test. The δ in every
theorem is the i-versus-REST mixed difference (aa4bdbe's finding 2), not the pairwise one;
the pairwise one is only a diagnostic lower bound.

**Open and owned by main now:**
- M3 (XOR) and M5 (menu vs revision), designs in P2 HANDOFF;
- Vb family sharpness in Lean;
- the upper bound R*(m) ≤ ⌊(m+1)/4⌋;
- a D6 world realising (ii) at m = 7;
- the CityFlow smoke run and PROTOCOL_v0;
- C1, whose V2 draft is uncompiled;
- the GATE_OLD7 final report, including the Aesop import artefact.

## Update 2 — the decision-value objective, and the first traffic evidence

**Lean** (`LeanMarlSubsetFrontierV1`, main; compiles; 11 theorems with standard axioms only; 0 sorry):
- The objective is the decision value f(S), for ANY set function, under the local interaction
  |f(A∪i) − f(A) − g_i| ≤ δ (i versus rest).
- `value_exchange`, `value_exchange_lower`.
- `subset_frontier`: the gain prefix after R replacements has regret ≤ 2(d_k − R)₊·δ.
- `subset_price_le`: ≤ 2·min(k, m−k)·δ.
- `subset_zero_price`: the price is zero under a 2δ gain margin.
- `bridge_mixed`: D6's mixedDifference bound implies the hypothesis.
- `subset_constant_sharp`: **the constant 2 is attained exactly** (three messages, tied gains,
  δ = 7, price 14). The adversarial search is `research/marl_budget/subset_constant/`.

**Traffic, oracle diagnostic**: `research/marl_budget/diag_20260927/set_objective_full.json`
(producer `scripts/DIAG_cityflow_set_objective.py`).
- Setup:
  - CityFlow 3×3 and 4×4 grids, two demand levels, 2–3 seeds;
  - a frozen max-pressure controller that uses communicated downstream queues;
  - f_i(S) = the oracle rollout value of the decision i takes after hearing S, at the true state.
- 1180 (state, intersection) tables. Every self-check passes, including the subset_frontier
  transcription.

| Measure | Share of tables |
|---|---|
| messages change the decision | 44% |
| δ = 0 | 82% |
| every cut in the 2δ-margin (zero-price) regime | 82% |
| score-priority price > 0 at R = 0 | **4.7%** (mean 3.4% of the value spread) |
| score-priority price > 0 at R = 1 | **0%** |
| nesting price > 0 at R = 0 | 0.17% |
| nesting price > 0 at R = 1 | 0% |

- The realised price is ≤ ½ of the bound in every table, although the bound itself is sharp
  in general.

**Reading.**
- With one-hop neighbours in grid signal control (m ≤ 4), universal priorities are nearly free.
- One revision always suffices there, exactly as the theory predicts: the nesting degree is
  ≤ 1 for m ≤ 6, and the price appears only outside the 2δ-margin regime.
- This is an honest negative for "revision matters" in this setting, and a positive for the
  theory's predictive role.
- **Design consequence.** To exhibit a price that revision must repair, and ESPECIALLY the
  price of nesting, the candidate message set must be large (m ≥ 7) and messages must
  interact:
  - 2-hop or per-lane packet messages;
  - a learned message-consuming policy;
  - vehicle-level V2X with many senders (MetaDrive).

  This is the next experimental step. A favourable regime is NOT to be injected by
  hand-designing a controller.

## Update 3 (27/09, 19:00): what the cheap tests decided

The full evidence chain is in FULL_CORPUS_AUDIT §23.4.

**Refuted for this protocol family.**
- A prepared priority has no latency advantage: per-budget tabulation dominates in value and has
  equal post-grant latency.
- Traffic losses come from score error, not nesting: the best nested chain is nearly optimal under
  a global budget.

**Supported, at oracle level only.** On one broadcast stream with heterogeneous receiver
capacities, bounded per-receiver repair has large certified headroom:
- R = 1 recovers 88% of the private gap;
- the sharing price is real: private beats the exact known-budget shared order in 106/256 cases.

**Not supported.** A selector using legal information cannot learn that headroom in the pilot. This
held after fixing the receiver-history omission, anchoring scores, preferring the prefix on ties and
selecting a no-edit threshold. Supplying privileged joint actions makes repairs rankable, which
supports actor-response prediction as one candidate bottleneck.

**Decision (audits):**
- Stop the learned-traffic expansion for this submission cycle.
- The MARL paper can present the mathematics, the exact mechanism and the diagnostic limits. It
  cannot present a successful learned MARL method.
- Any claim about A as acquisition starvation, or B as acceptable-repair calibration, needs E1
  (controlled calibration), which is not yet run.
