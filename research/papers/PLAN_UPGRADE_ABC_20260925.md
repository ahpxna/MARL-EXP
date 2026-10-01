# Upgrade plan: A, B, C to the targets of 2026-09-25

The targets are the user's:
- **A**: the repair frontier determines the optimal sequential cost under a sacrifice budget.
- **B**: from the obstruction order to a limiting information game and query design.
- **C**: exact and algorithmic frontiers for a multi-type class, with a breakpoint
  classification.

This file fixes the exact statements and splits each target into waves. Nothing enters a
manuscript before it compiles in a gated module with satisfiable hypotheses.

Already proved and gated, and used below:
- the sacrifice duality: `exchange`, `frontier_upper`, `budget`, `weak_duality`,
  `repair_mix`, `repair_clipped` (`LeanPaperASacrificeDualityV1`);
- the χ² star law (`LeanPaperBChiStarV1`);
- the private-query channel (`LeanPaperBPrivateQueryV1`);
- the sharing tournament (`LeanPaperBShareTournamentV1`);
- the certificate channel (`LeanPaperBCertificateChannelV1`);
- the robust ball (`LeanPaperCRobustBallV1`).

## A. Repair frontier ↔ optimal sequential cost

Definitions:
- `s_θ(w) = 1 - J_proxy(θ,w)/Γ_proxy(θ)` (convex, since `J_proxy` is concave);
- `R_θ(b) = sup{J_true(θ,w) : s_θ(w) ≤ b}`.

**Three budget classes.** A policy `π` with stopping time `τ` and counts `N_q(τ)` belongs to:
- `Π_b^round` if each round's query distribution `p_t` (a design) has `s_θ(p_t) ≤ b`;
- `Π_b^path` if pathwise `s_θ(N(τ)/τ) ≤ b` at the stop;
- `Π_b^exp` if `s_θ(w̄) ≤ b` with `w̄_q = E N_q(τ)/E τ`.

Because `s_θ` is convex and `w̄` is a `τ`-weighted average of the pathwise designs and of the
round designs, `Π_b^round ⊆ Π_b^exp` and `Π_b^path ⊆ Π_b^exp`. The lower bound is proved on the
largest class, `Π_b^exp`.

- **A-1 (lower, every policy).** For every δ-correct policy in `Π_b^exp`,
  `E_θ τ · R_θ(b) ≥ D_δ = (1-δ)log(1/δ) - log 2`.
  - Proof: change of measure per true alternative `λ` gives
    `Σ_q E N_q · KL_q(θ,λ) ≥ D_δ`, i.e. `E τ · Σ_q w̄_q KL_q(θ,λ) ≥ D_δ`.
  - Take the infimum over `λ`: `E τ · J_true(w̄) ≥ D_δ`.
  - `s(w̄) ≤ b` gives `J_true(w̄) ≤ R(b)`.
  - In A the correct answer at `θ` is unique, since the decision is binary at the world, so no
    answer selection is needed.
  - Status: wave 1, general channel, Lean.
- **A-2 (attainability).** A policy in `Π_b^round`, tuned to `θ` and δ-correct at every world,
  with `E_θ τ ≤ log(1/δ)/R_θ(b) (1+o(1))`.
  - Route: the fixed-design tracking learner `fixLearner w_b` (`LeanPaperA6FixedDesignV1`) at
    a maximiser `w_b` of the budgeted game, with the A7 GLR stop.
  - This needs the A7 upper chain with the oracle replaced by the constant `w_b`: the
    tracking discrepancy `fWarmRun` is already proved.
  - A deployable version tracks the budgeted oracle at the estimate. It has to handle
    non-unique maximisers (argmax sets and continuity of the constrained value) and answer
    changes.
  - Status: wave 2.
- **A-3 (characterisation of repair).**
  - `R_θ` is nondecreasing and concave on `[0, s_max]`.
    - Hence **no threshold**: if `R(b₁) > 0` then `R(b) ≥ (b/b₁) R(b₁) > 0` for every
      `0 < b ≤ b₁`.
    - Either `R ≡ 0` (the decision is unlearnable at any sacrifice) or `R(b) > 0` for every
      `b > 0`.
  - `R(0) = sup` of `J_true` over the surrogate-optimal face, so `R(0) = 0` exactly when
    every surrogate optimum starves.
  - When `R(0) = 0`: `R(b) ≍ b` if and only if the certificate pair gives a finite slope
    (`R(b) ≤ b/Σν`) and some design `v` has `J_true(v) > 0` (`R(b) ≥ min(1,b/s(v)) J_true(v)`).
  - On piecewise-linear games (finite alternatives) the slope `R'(0+)` is finite. It is
    infinite only when `s` is flat to second order at the optimal face, where `R ≍ √b`.
  - Status: the concavity, trichotomy and no-threshold results are wave 1, Lean. The √b
    example is wave 2.
- **A-4 (a second class).** Two Gaussian arms; the decision is which mean is larger.
  - The frozen surrogate lets only the leader move: `J_proxy(w) = w₁Δ²/2`.
  - The true game lets both move: `J_true(w) = (w₁w₂/(w₁+w₂))Δ²/2`.
  - The surrogate optimum is `w = e₁`, with `J_true = 0` (starvation).
  - `s(w) = w₂`, so `R(b) = b(1-b)Δ²/2` exactly: linear repair with slope `Δ²/2`.
  - The alternative structure (a half-space in two arms) differs from the compression family.
  - Status: wave 1, Lean, exact.

## B. Obstruction order → decision game → query design

Fix finite worlds `W`, finite queries `Q`, a safe correspondence, and a graded channel:
`c·h^{2 sep_q(u,v)} ≤ KL_q(u,v) ≤ C·h^{2 sep_q(u,v)}`, with `sep(u,v) = min_q sep_q(u,v)`.

Structural hypothesis (U): `sep` is an ultrametric order, i.e.
`sep(u,v) ≥ min(sep(u,w), sep(w,v))`. Agreement of all observables up to an order is an
equivalence relation. This holds on the parity channel, where `sep = min(u,v)+1`.

- **B-1 (the characteristic game has the obstruction order).**
  - Define `D_h(w) = max_{a safe at w} max_{α∈Δ(Q)} min_{λ: a unsafe at λ} Σ_q α_q KL_q(w,λ)`,
    the Degenne–Koolen value at `w`.
  - Define the world's decision order `s(w) = min{s : {w} ∪ {λ : sep(w,λ) > s}` has a
    common safe answer`}`.
  - Under (U), `c h^{2s(w)}/|Q| ≤ D_h(w) ≤ C h^{2s(w)}`, and `max_w s(w) = s*`.
  - So the per-world benchmark has order `s(w)`, and the minimax benchmark
    `min_w D_h(w) ≍ h^{2s*}`. These are two different statements, proved separately.
  - Proof of the lower side:
    - `S = {w} ∪ {λ : sep(w,λ) > s(w)}` has a common safe answer `a`.
    - Every `λ` where `a` is unsafe has `sep ≤ s(w)`, so it has information
      `≥ c h^{2s(w)}` on some query; a uniform `α` loses `1/|Q|`.
  - Proof of the upper side:
    - Take `s' = s(w)-1`. The set `S' = {w} ∪ {λ : sep(w,λ) ≥ s(w)}` has no common safe answer.
    - For each answer `a` safe at `w`, some `λ ∈ S'` makes it unsafe, and
      `KL ≤ C h^{2 sep} ≤ C h^{2 s(w)}`.
  - That `max_w s(w) = s*` uses (U): the classes `{λ : sep(w,λ) > s}` are the equivalence
    classes of agreement at order `s`.
  - Status: wave 1, Lean.
- **B-2 (the limiting game).**
  - Under exact homogeneity `KL_q = C_q(u,v) h^{2 sep_q}`: `h^{-2s(w)} D_h(w) → G*(w)`.
  - `G*(w)` is the finite game restricted to the answers safe on `S`, the alternatives at
    order exactly `s(w)`, and the queries attaining that order.
  - Lower-order alternatives force `α` off their queries; higher orders vanish.
  - The exchange of limit and max-min uses the finiteness of `W` and `Q` and compactness of
    `Δ(Q)`.
  - Status: wave 2.
- **B-3 (what the invariant misses).** Proved:
  - the private-query channel: same `s*`, cost `×(|W|-1)`;
  - the certificate channel: KL's `1/(|W|-1)` is necessary;
  - the χ² law: `|W|` only additive.
- **B-4 (query design).**
  - For a sub-menu `Q' ⊆ Q`, `s*(Q') ≤ s` if and only if `Q'` hits every set
    `Q_s(H) = {q : ∃ u≠v∈H, sep_q(u,v) ≤ s}` over the minimal obstructions `H`.
  - `s_id(Q') ≤ s` if and only if `Q'` hits every `Q_s({u,v})`, `u ≠ v`.
  - Hence `s*(Q') ≤ s_id(Q')`, and the optimal design is a minimum-cost hitting set per order.
  - A gap example: on the latent family, the single decision probe gives `s* = 1` while
    `s_id = r`.
  - The new part is the order-thresholded incidence produced by the channel; the hitting-set
    reduction is the tool.
  - Status: wave 1, Lean, combinatorial.

## C. Multi-type signed-prefix class

- **C-2 (flow equivalence for `p` types).**
  - State: the counts taken, `v ∈ Π_j [0, n_j]`.
  - Uniform relabelling within a type preserves every item marginal band and the nonlinear
    prefix regret.
  - Status: check whether `LeanPaperCFlowV1` is already general in the multiset, then state
    the `p`-type version.
- **C-1/C-3 (the two-magnitude family and its phase diagram).**
  - `g = (a^{n+a}, (-a)^{n-a}, b^{n+b}, (-b)^{n-b})`, `a > b > 0`.
  - First an exact rational LP over the flow at small counts and a grid of `a/b`, to map
    single versus multiple breakpoints and where parity stops deciding.
  - Then primal laws with matching dual certificates per region.
  - Status: wave 1 is the smoke-sized exact exploration (smallest useful run: counts ≤ 3 per
    type, `a/b ∈ {3/2, 2, 3, 5}`). Wave 2 is the proofs.
- **C-4 (when the band is free).** A computable condition:
  - `V_g(η) = V_g^free` if and only if, at every budget `k`, the proportional composition
    `k·n/m` lies in the convex hull of the optimal compositions reachable along a monotone
    chain.
  - This is an LP feasibility on the count lattice, decided per `g` from its structure.
  - Status: wave 2, after C-1's exploration.
- **C-5 (value vs ratio robustness).** Done: the value Lipschitz envelope, the robust ball
  `robust_ball`, and the rescaling counterexample `rescaled_keeps_price`.

## Order of work (serial)

1. Wave 1 Lean: A-1, A-3, A-4, then B-1, then B-4.
2. C-2 check, then the C-1 smoke exploration.
3. Smoke gate for every new module, and manuscript sections for each gated block.
4. Wave 2 (A-2, B-2, C-3/C-4 proofs) is planned here and reported as open until done.

## Target v2 (2026-09-25, after the second review)

The review's targets were checked against the repository. They are stronger than v1 on three
points and are adopted.

- **A.** The operational statement is
  `lim_{δ→0} inf_{π∈Π_b} E_θ τ_δ / log(1/δ) = 1/R_θ(b)`, with `Π_b` fixed precisely.
  - `w̄ = E N(τ)/E τ` is not `E[N(τ)/τ]`. So a constraint `E[s(N/τ)] ≤ b` does not give
    `s(w̄) ≤ b`, and it is left outside the hierarchy (`mean_escapes`).
  - The hierarchy `Π^prefix ⊆ Π^terminal ⊆ Π^exp` is proved, because `J_f` is an infimum of
    linear forms. An eventual class with a deterministic burn-in `t₀` is added: it holds the
    fixed-design learner.
  - Lower bound: `terminal_budget_law`, `eventual_budget_law`.
  - Upper bound: `fix_upper_rate` and `fix_budget_eventually` (`LeanPaperABudgetUpperV1`).
  - In A the answer is unique, so `R = max_a sup_{W_b} J_a` reduces to one answer. The
    multi-answer exact limit is not claimed: `budget_law_multi` loses `1/|correct|`, and the
    restricted-event change of measure does not follow from Wald.
  - Bridge still informal: the lower bound is over kernel policies and the upper bound is in the
    stream model. The coupling (`stoppedG`, `cnt_eq_at_min`) is proved; the Gaussian KL
    identification of `MeetsBudget` with the stream sacrifice is proved only on the family
    channel.
- **B.** Two layers: `ord_h Γ_dec = 2s*` (order), then `h^{-2s}Γ_dec → G*` (critical
  coefficient game).
  - `critical_limit`, `expansion_hyps`, `decision_limit` (`LeanPaperBCriticalGameV1`).
  - "`s*` fixes the exponent, not the constant": `same_order_ratio` (private `1/k` against
    shared `1`).
  - Query design: `hitting_embeds` (`LeanPaperBQueryDesignV1`) makes minimum-cost design at a
    target order contain minimum-cost hitting set (NP-hard, Karp 1972; greedy `H_n`, Chvátal
    1979, cited).
- **C.** The fixed-`p` flow program over `Π_j(n_j+1)` states (`support_box`, `card_box`).
  - `η_free` = the minimum deviation over the free optima, attained.
  - `V(η) = V_free` if and only if `η ≥ η_free` (`free_threshold`), read off the flow program
    (`free_threshold_flow`).
  - The additive price `Δ_g(η)` is stable without a lower bound on `V_free` (`gap_stable`).
  - The four-type phase diagram is NUMERICAL (`paperC_typed_frontier.json`):
    - counts `(1,1,1,1)`: one breakpoint at `η = 1/3` and `V₀/V_free = 3/2` for every tested
      `a/b`;
    - counts `(1,1,2,2)` and `(2,2,2,2)`: the breakpoint moves between `a/b = 2` and `a/b = 3`;
    - `(2,2,2,2)`: two nearby kinks.
    - Proofs of region laws are open.

## Open-math push (2026-09-25, after the upgrade round)

The user's three items, in the order they will be worked (serial):

- **C: region laws for counts `(1,1,2,2)` and `(2,2,2,2)`.**
  1. Build a generic Lean lemma for layered flows with the band. Take weights `μ_k ≥ 0` on
     budgets, band multipliers `ℓ_{kτ}`, and node potentials `φ_k(v)` satisfying
     `φ_k(v) ≤ μ_k c_k(v) - Σ_τ ℓ_{kτ}(v_τ/n_τ - k/m) + φ_{k+1}(w)` on every edge. Then every
     banded count-feasible flow has
     `Σ_k μ_k E c_k ≥ φ_0(start) - (η/m) Σ|ℓ|`. This is the dual certificate of the flow LP,
     proved once.
  2. Get exact certificates at rational `a/b` from the LP. Solve with HiGHS, rationalise the
     basis, and check primal and dual exactly in fractions. Fit the certificate entries as
     functions of `a/b` on each region.
  3. Lean per region: the primal is an explicit law over permutations with within-type
     relabelling; the dual is the step-1 lemma with the fitted certificate. First targets are
     `V(0)` and `V_free` of `(1,1,2,2)` on `a/b ∈ [2,3]`:
     - numerically `V(0)·D/b = 1/2 + |a/b - 5/2|/3`;
     - `V_free·D/b = 2/5` for `a/b ≥ 13/5`.
- **A: the kernel/stream bridge.** Build a Gaussian kernel channel from a `Spec` on `E ⊕ Unit`
  and prove `klq = (θ_e - λ_e)²/(2σ_e²)`. Show that the stopped fixed-design learner, as a kernel
  policy, is in `EventualClass`, via `cnt_eq_at_min` and `fix_budget_eventually`. Then the
  corollary is closed end to end.
  - The multi-answer exact limit comes after, starting from a literature check of the
    Degenne–Koolen lower-bound proof.
- **B: `G*` for the parity channel and the latent family.** First derive the leading
  coefficients of the per-query information by hand (expansion of the mixture densities in
  `h`). Then formalize the limit `h^{-2 sq} κ_q → c_q`, feeding `expansion_hyps`.
