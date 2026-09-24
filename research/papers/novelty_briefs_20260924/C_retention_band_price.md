# Brief C — "The price of per-item retention bands when one ranking serves every budget"

Read `00_PROTOCOL.md` first. Manuscript: `research/papers/_tex/paper_c.tex`. Claim map:
`research/papers/THEOREM_MAP.md`.

**Place in the programme.** The price of solving the wrong intermediate problem: here,
optimising a ranking distribution while misjudging how it is used, both as a band on each
item's retention and as a choice of budget before versus after the ranking is drawn. Generic
fair-ranking marginals, symmetry averaging and flow reductions are not the novelty. The
all-size signed-prefix laws, the phase boundary and the robustness must carry it.

## 1. The model, self-contained

- **Items and weights.** `m` items with signed weights `g_m = (−3, (−1)^p, (+1)^q, 3)`, with
  `p = ⌈(m−2)/2⌉` and `q = ⌊(m−2)/2⌋`. Normaliser `D = ‖g‖₁ = m + 4`.
- **Ranking and budgets.** A *randomised ranking* is a law `P` on permutations. Budget `k`
  serves the top-`k` prefix.
- **Regret.** `r_k(σ) = (|Σ_{i ∈ prefix_k(σ)} g_i| − b_k) / D`, with the per-budget optimum
  `b_k = min_{|S|=k} |Σ_S g|`. On `g_m`, `b_k = k mod 2` (proved).
- **Objective.** `max over interior k of E_P[r_k]`: the budget is fixed *before* the ranking
  is drawn.
- **Retention band.** For every item `i` and budget `k`,
  `|P(i ∈ prefix_k) − k/m| ≤ η/m`. At `η = 0` every item is retained exactly `k/m` of the time.
- **Value.** `V_m(η)` is the infimum of the objective over banded laws. `V_free` is the
  unconstrained value.

## 2. Headline claims

| id | claim | quantifiers / scope |
|---|---|---|
| **C-H1** | **Exact zero-band prices**: `V_m(0) = 4/(m(m+4))` for even `m` and `(m+3)/(m(m+4))` for odd `m`, while `V_free = 2/((m+4)(m−1))`. The price ratio is `(m+3)(m−1)/(2m) ~ m/2` for odd `m` against `2(m−1)/m → 2` for even `m`: a parity split of order `m`. | Every size (`m ≥ 3` odd, `m ≥ 4` even), attained by explicit laws on ALL permutations. The lower bounds hold for every feasible law. |
| **C-H2** | **Even frontier and odd breakpoint**: for every even `m ≥ 4` and `η ≥ 0`, `V_m(η) = max{V_free, 4(1−η)/(m(m+4))}`, with breakpoint `η* = (m−2)/(2(m−1))`. For every odd `m ≥ 3`, `V_m(η) = V_free` iff `η ≥ 1`. | The odd curve between its two anchors is NOT claimed. |
| **C-H3** | **Exact polynomial reduction**: the value of the ranking program equals that of a four-type flow LP with `O(m²)` states, both directions carrying every per-item band and the whole budget vector. | A statement about the VALUE on `g_m`, not an algorithm for arbitrary perturbed weights. |
| **C-H4** | **Stability of the physical optimum**: `|V(g') − V_m(η)| ≤ 3‖g_m − g'‖₁/d`, for `0 < d ≤ min(‖g_m‖₁, ‖g'‖₁)`, with the baseline recomputed, the normaliser moving, and per-item bands. A ratio floor `V_unif/V_free ≥ 1/(4ε + 4/(m−1))` holds for `‖u‖₁ ≤ ε ≤ 1/4`. | An envelope and a floor, not a robustness radius. The collapse point of the true price is open. |
| **C-H5** (optional; old Structural result, not yet in paper C) | **Ex-ante versus ex-post**: with the budget chosen adversarially *after* the ranking is drawn (`E max_k r_k`), the free value is `V_path = 2/(m+4)`, against `V_avg = 2/((m+4)(m−1))`. So `V_path/V_avg = m − 1` exactly. | Free case only. The banded ex-post problem is unsolved. The two linear factors must not be multiplied into `m²`. |

## 3. Already conceded — check that our description of each is fair

- Singh & Joachims, "Fairness of exposure in rankings", KDD 2018 (exposure constraints, the
  Birkhoff–von Neumann decomposition).
- Singh, Kempe, Joachims, "Fairness in ranking under uncertainty", NeurIPS 2021 (ex-ante
  versus ex-post).
- Gorantla, Deshpande, Louis: group-fair ranking, underranking and ex-post group fairness
  (ICML 2021 and later; verify which paper is closest).
- Balinski & Young, *Fair Representation* (1982).
- Schrijver, *Combinatorial Optimization* (flows and permutation polytopes).
- The flow/DAG reduction of a permutation program to compositions is standard; we do not
  claim the technique.

## 4. Candidate collision zones

**Z1. Prefix-constrained fair ranking.**
Candidates:

- Celis, Straszak, Vishnoi, "Ranking with fairness constraints", ICALP 2018 (bounds on group
  counts in EVERY prefix);
- Zehlike et al., "FA*IR: a fair top-k ranking algorithm", CIKM 2017;
- Geyik, Ambler, Kenthapadi, KDD 2019 (fairness-aware ranking at LinkedIn);
- Gorantla et al. (randomised group-fair rankings, ex-post guarantees).

Question: do they study a *signed-prefix* objective, net of the per-budget optimum, at every
budget? Do they give exact prices or breakpoints of a per-item band?

**Z2. Exposure and amortised fairness geometry.**
Candidates:

- Biega, Gummadi, Weikum, "Equity of attention", SIGIR 2018;
- Diaz et al., "Evaluating stochastic rankings with expected exposure", CIKM 2020;
- Kletti, Renders, Loiseau, "Introducing the expohedron …", WSDM 2022 (the polytope of
  achievable exposures).

Question: does the expohedron or permutahedron geometry give our values, or a reduction
equivalent to C-H3?

**Z3. Apportionment and house monotonicity.**
Candidates:

- Balinski & Young, "The quota method of apportionment", Amer. Math. Monthly 1975;
- Still, "A class of new methods for congressional apportionment", 1979;
- later work on house-monotone quota methods.

This is the closest structural analogue: ONE sequence serves every house size (budget) while
each state stays within quota (a band). Questions: is our `η` band a quota-type condition? Do
prices of staying within quota, for a signed or discrepancy objective, appear there?

**Z4. Prefix discrepancy and Steinitz rearrangement.**
Candidates:

- the Steinitz lemma;
- Grinberg & Sevastyanov 1980;
- Bárány's survey "On the power of linear dependencies";
- Banaszczyk, "On series of signed vectors and their rearrangements", 2012;
- Bansal, Jiang, Singla, Sinha, "Online vector balancing and geometric discrepancy", STOC
  2020;
- Chobanyan's rearrangement inequalities.

The deterministic problem "order signed numbers to keep every prefix sum small" is classical.
Question: are *randomised* orderings with prescribed inclusion marginals, and the
signed-prefix regret against the best `k`-subset, treated anywhere? Does any exact value for
a `±1/±3` multiset appear?

**Z5. Sampling designs with prescribed inclusion probabilities for every size.**
Candidates:

- Srinivasan, "Distributions on level-sets with applications to approximation algorithms",
  FOCS 2001;
- Deville & Tillé, splitting and pivotal sampling, Biometrika 1998;
- order sampling (Rosén);
- nested sampling designs.

At `η = 0` our constraint says each item is in the top-`k` with probability exactly `k/m` for
every `k`: a nested design. Question: are extremal results for signed-sum objectives over
such designs known?

**Z6. Incremental and universal solutions for all budgets.**
Candidates:

- Mettu & Plaxton, "The online median problem", SIAM J. Comput. 2003;
- Lin, Nagarajan, Rajaraman, Williamson, "A general approach for incremental approximation
  and hierarchical clustering", SIAM J. Comput. 2010;
- incremental knapsack;
- cutoff-robust ranking in IR.

Question: "one ranking for all budgets, regret against the per-budget optimum" is the
incremental-solution template. Is any result with randomisation plus marginal constraints,
or with an exact price, known?

**Z7. Terminology.** Bertsimas, Farias, Trichakis, "The price of fairness", Oper. Res. 2011.
Cite it if we use "price" in their sense.

**Z8. Ex-ante versus ex-post (for C-H5).** Freeman, Shah, Vaish, "Best of both worlds:
ex-ante and ex-post fairness in resource allocation", EC 2020; Singh–Kempe–Joachims 2021.
Question: is a factor-`(m−1)` gap between the two regimes known for a comparable objective?

## 5. Hostile questions

1. Does C-H1's odd/even split follow from a known parity phenomenon in balancing sequences
   (for instance, the minimum `|prefix|` at odd budgets is 1)? We prove `b_k = k mod 2`; is
   the *banded randomised* value then a short corollary of something known?
2. Is C-H3 a special case of a general theorem that type-symmetric permutation programs
   reduce to flows over compositions *with marginal constraints preserved*? We concede the
   unconstrained technique; does the constrained version already exist?
3. For C-H4: is the Lipschitz stability of LP values in the objective coefficients the whole
   content? It is standard. Our claim is only the constant 3 with a moving normaliser and a
   recomputed baseline; judge whether that is worth stating as a result at all.

## 6. Search strings

- "ranking" "fairness constraints" prefix top-k "every prefix"
- randomized ranking "marginal" constraints "exposure" price OR "trade-off" exact
- "house monotone" apportionment "quota" sequence
- "Steinitz" rearrangement "prefix sums" randomized OR "inclusion probabilities"
- "fixed inclusion probabilities" nested sampling design all sample sizes
- "incremental" approximation "all k" ranking OR ordering competitive
- "ex-ante" "ex-post" ranking fairness gap factor

Screen the `C_marginals` and `C_order` groups of `research/literature_audit_20260921` first.
