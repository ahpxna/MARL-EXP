# Plan: sharpen A, B and C (2026-09-25, after commit 930a663)

The goal is to turn the three weak points of `MATH_AND_NOVELTY_AUDIT_20260925.md` §6 into
theorems.

- A is a construction; it should become a law.
- B's law carries `|W|` factors whose status is unknown.
- C lacks even `m` and tight constants.

Every item below is mathematics first, then Lean, then the manuscript. Nothing enters a paper
before it compiles in a gated module with standard axioms and satisfiable hypotheses.

## B. How to make the law match

### B.0 What "match" can and cannot mean

The current law is:

- lower: `E_w N · t*_KL ≥ ((1−δ)/(|H|−1)) log(1/δ) − log 2`;
- upper: `≤ |W|² ⌈log(|W|/δ)/t*_H⌉`.

Removing every `|W|` from both sides is **impossible** for a law stated through the obstruction
value alone. Two instances show it; both are small enough to formalise.

1. **The certificate channel** shows that, with KL information, the lower factor `1/(|W|−1)` is
   necessary.
   - Worlds `1..k`. The answers are `a_v = "not v"`, safe everywhere except at `v`, so `W`
     itself is the only obstruction.
   - A single query returns a symbol `s ∈ W` with `P_w(s=w) = ρ` and `P_w(s=v) = (1−ρ)/(k−1)`
     for `v ≠ w`.
   - The policy "query once, answer `not s`" is safe with probability `1−ρ` at every world.
   - `KL(P_w‖P_u) ≤ ((1−ρ)/(k−1)) log(1/((k−1)ρ))`.
   - With `ρ = δ` we get `N · t*_KL ≤ log(1/δ)/(k−1)`. The pigeonhole bound is attained to
     first order.
2. **The private-query channel** shows the upper factor is necessary.
   - Worlds `0..k`. Query `q_j` is `N(h·[w=j], 1)`. Safe sets are singletons, so the task is
     identification.
   - Every pair has `κ = h²/2 = t*`.
   - At world `0`, only `q_j` separates `0` from `j`. So `E_0 N_j · h²/2 ≥ kl(1−δ, δ)` for each
     `j`, and `E_0 N ≥ k · kl(1−δ,δ)/t*`.
   - The cost is `(|W|−1) log(1/δ)/t*`: the upper side must carry a factor of the number of
     queries.

So a matching law must use the right information on each side and name the one factor that
cannot be removed. Here is the target.

### B.1 The χ² star law (new theorem, removes the multiplicative `1/(|W|−1)`)

For every channel, every finite-horizon policy that is safe with probability `1−δ` at every
world, every obstruction `H`, every `w ∈ H`, and all `η ∈ (0,1)`, `y ∈ ℝ`:

```
P_w( N · t_χ(w,H) ≤ y ) ≤ δ + 2(|H|−1) √(δ e^y),
t_χ(w,H) = max_{u∈H, q≠dummy} log(1 + χ²_q(P_w‖P_u)).
```

Hence `E_w N · t_χ ≥ (1−δ−2η) (log(1/δ) − 2 log((|H|−1)/η))`. The `|W|` is only additive.

*Proof.*
1. Let `S = {output safe at w}`. Split `S` into `S_u`, the part whose output is unsafe at `u`,
   for `u ∈ H∖{w}`. Then `P_u(S_u) ≤ δ`.
2. Let `R_u = dP_u/dP_w` (a product of density ratios) and `Z_u = 1/R_u`. Let `B = {N t ≤ y}`.
3. For any `c > 0`:
   `P_w(S_u ∩ B) = ∫_{S_u∩B} R_u Z_u dP_w ≤ c P_u(S_u) + P_w(B ∩ {Z_u > c}) ≤ cδ + (e^y/c) ∫ Z_u e^{−tN} dP_w`.
4. The χ² product rule gives `∫ Z_u e^{−tN} dP_w ≤ 1`, because each informative step
   contributes `(1+χ²_q)e^{−t} ≤ 1` and the dummy step contributes `1`.
5. Take `c = √(e^y/δ)` and sum over `u`. ∎

*Source of the idea.* This is the change of measure of Degenne–Koolen, Proposition 18 (from
Kaufmann–Garivier 2019). The χ² exponential moment replaces their sub-Gaussian concentration,
so it is **non-asymptotic** and needs **no concentration assumption**. Their Theorem 1 is
asymptotic in `δ` and assumes sub-Gaussian arms. We cite it as the source, and claim the
non-asymptotic χ² form at obstructions.

*Tightness.* On the certificate channel, `log(1+χ²) ≈ log(1/((k−1)²δ))`, so
`N·t_χ ≈ log(1/δ) − 2log(k−1)`. The additive term is attained.

*Consequence for the paper's channels.* Their lower sides already go through χ² (`famChi_*`,
the parity χ²). The four lower constants lose their `1/(|W|−1)`, so the parity constant is
uniform in `m`.

Lean items:
- **L1** (density identity). `∫ F d hist_u = ∫ F · R_u d hist_w` for every measurable
  `F ≥ 0`, every adaptive policy, and positive densities. This is an induction on
  `hist (n+1) = map snoc ((hist n ⊗ step) ⊗ obs)`, the same shape as `lintegral_prod_sched`
  but for an adaptive policy and a general `F`.
- **L2** (adaptive product inequality). If `∫ f(q,y) p_w(y|q) dy ≤ 1` for all `q`, then
  `∫ ∏_i f(q_i,y_i) d hist_w ≤ 1`.
- **L3** Instantiate `f = (p_w/p_u)·e^{−t[q≠dummy]}` via the per-query χ² (`chi` in
  `LeanPaperBProtocolV1`).
- **L4** The main theorem with measurable selection; the expectation corollary; the
  a.s.-stopping corollary through `trunc_correct`.
- **L5** Satisfiability: the Gaussian ±1 channel of `hellinger_tournament_satisfiable`.

### B.2 The sharing tournament (upper, `|W|²` → `|Q|`)

Query every informative query round-robin, `n` times each. Every pair's block
likelihood-ratio test reads the samples of its best Hellinger query, so all pairs share
samples. A union bound over the `|W|−1` tests that involve the truth gives:

`sup_w E_w N ≤ |Q_inf| · ⌈log(|W|/δ)/t*_H⌉`.

The private-query channel shows that the factor `|Q_inf|` is necessary.

Lean: a new schedule and the same `decode`/`beatH` argument.

### B.3 The necessity instances

- **N1** Private-query channel (Gaussian). This is easy: `change_of_measure` already works
  with per-query counts, and the Gaussian KL exists.
- **N2** Certificate channel. The Channel structure needs positive densities on ℝ, so the
  symbols are embedded as well-separated Gaussian bumps. A KL upper bound by data processing
  (log-sum inequality on the mixture) and a decoding error `≤ ρ + overlap` complete it.
  Medium effort.

### B.4 The exact constant, positioned

For finite `W` the exact first-order constant is `max_w T*_DK(w)`. We prove the sandwich:

- for `w` in an obstruction attaining `t*`: `1/t* ≤ T*(w)`;
- for every `w`: `T*(w) ≤ 4|Q|/t*_{hel}`.

The second bound uses the Hellinger triangle inequality. The set
`S = {λ : H²(w,λ) < t/4}` has every pair `< t`, so it is not an obstruction. It therefore has
a common safe answer, and every `λ` where that answer is unsafe has `H² ≥ t/4`. A uniform
allocation then gives the bound.

This proves what `t*` captures: the characteristic time, up to the splitting factor `|Q|`.

### B.5 The resulting law (what the paper will state)

```
(1−δ−2η)(log(1/δ) − 2log((|W|−1)/η)) / t*_χ  ≤  minimax E N  ≤  |Q| ⌈log(|W|/δ)/t*_H⌉
```

- Each side is tight in its `|W|`/`|Q|` dependence (N2, N1).
- With `t*_χ ≤ K t*_H` and `|Q|` bounded, the cost is `Θ(log(1/δ)/t*)` with **no `|W|`** in
  the leading term.
- On graded channels the order law is unchanged.

## A. From a construction to a law

### A.1 Sacrifice duality (new, general)

Setting:
- finite cells `e`;
- frozen alternatives `λ` with per-cell information `d^f_e(λ)`, and true alternatives with
  `d^t_e(λ)`;
- `J_f`, `J_t` are the infima of the linear forms, and `Γ_f = sup J_f`;
- `sac(w) = 1 − J_f(w)/Γ_f`.

A **certificate pair** is:
- a mixture `μ` of frozen alternatives, with `c_e = Σ μ_λ d^f_e(λ)` and margins
  `γ_e = Γ_f − c_e`;
- weights `ν ≥ 0` on true alternatives with `Σ_λ ν_λ d^t_e(λ) ≤ γ_e/Γ_f` for every `e`.

Then:
1. *Exchange:* `sac(w) ≥ Σ_e w_e γ_e/Γ_f` for every design.
2. *Frontier:* `J_t(w) ≤ sac(w)/Σν`, and `Γ_t ≤ 1/Σν` when `c ≥ 0`.
3. *Budget:* for every policy whose counts meet `Σ_e N_e d^t_e(λ) ≥ D` on the support of `ν`,
   `N·sac(w̄) ≥ (Σν)·D`.
4. *Repair side:* `R(β) ≥ β J_t(v)/sac(v)` for every design `v`, by mixing with a surrogate
   optimum. Weak duality gives `Σν ≤ inf_v sac(v)/J_t(v)`.

All four are weak LP duality: finite sums and one infimum.

The construction is the instance where `μ` is the frozen dual certificate (which puts nothing
on the middle cells, so `γ_mid/Γ_f = 1`) and `ν = 8M` on each middle-pair shift, so
`Σν = 8rM`. The existing `middle_le_sacrifice`, `strict_frontier`, `trueGameC₀_le` and
`sacrifice_cost_law` are its corollaries.

**Novelty statement.** The covering LP has the form of Huang's cost-weighted constant. The
costs are the surrogate's own dual margins, which is what links the surrogate's geometry to
the price of repairing it.

Lean: a new module `LeanPaperASacrificeDualityV1`, generic over a `Fintype` of cells and
`Finset`-supported mixtures. Easy.

### A.2 The constant gap, recast

- Let `C_sac* = sup Σν` over certificate pairs, and `C_rep = inf_v sac(v)/J_t(v)`.
- Weak duality gives `C_sac* ≤ C_rep`.
- In the construction, `8rM ≤ C_sac* ≤ C_rep ≤ 128(4+2rM)/9`.
- Closing `32/9` is therefore a static question: compute `C_rep` (a fractional program), or
  find a better certificate. No learner is involved.
- Plan: a smoke-sized exact computation of `max_v J_t(v)/sac(v)` at `r ∈ {1,2}`,
  `M ∈ {1,4,16}`, reusing the exact KKT machinery of `EXP_paperA_frozen_proxy_exact.py`. Then
  conjecture a closed form and prove the matching design (upper) and certificate (lower).
- The policy achieving `C_rep` is a fixed-design GLR policy tuned to `θ_C`. It is δ-correct at
  every world, and it is an oracle-allocation diagnostic, labelled as such.

### A.3 The second class under the same law

The underpricing direction (`≥ M/96`) is the same duality with the roles of the two games
swapped. Instantiate it once to show the law covers both directions.

## C. Even size and constants

### C.1 Even `m`

- On `g_m` with even `m` the price is `2(m−1)/m < 2`.
- The open question is whether a perturbation of size `ε` can **create** a large price, or
  only move it within `[1, 2+O(ε)]`.
- Smallest run that answers it: the exact flow LP (`thm:flow`) at `m ∈ {4,6,8}` over
  single-item and two-item perturbations on a grid of `ε`, computing
  `V(g';0)/V(g';m)` exactly in rationals.
- If the price stays bounded, prove `≤ 2 + Cε/d` from the envelope (`trueValue_stable`) and
  the even frontier. If it can jump, locate the mechanism and prove a collapse/creation scale
  as for odd `m`.

### C.2 Tight constants for odd `m`

- For `ε ∈ [1/m, 1/6]` the known bounds are `1/(16ε) ≤ price ≤ 10/ε`; below `1/m` they are
  `(m−1)/8` or `(m−1)/4` against about `m/2`.
- Compute the single-light-item perturbation exactly (it is the upper witness), and
  conjecture its exact price `c(ε, m)`.
- The lower side needs the minimising perturbation: explore numerically first (exact LP), then
  prove.

## Order of work (serial; no fan-out)

1. A.1 sacrifice duality (Lean, short).
2. B.3 N1 private-query necessity (Lean, short).
3. B.1 L1–L5, the χ² star law (Lean, the main item).
4. B.2 sharing tournament (Lean).
5. B.4 sandwich (Lean).
6. B.3 N2 certificate channel (Lean).
7. C.1 and A.2 smoke computations, then proofs.
8. Manuscripts after each compiled block. Smoke gate after each block; full gate at the end.
