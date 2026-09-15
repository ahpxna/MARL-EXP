# Batch 4 — the mathematics, written as mathematics

Companion to `G04_headline_proofs.md`. Every step below carries its evidence class:

* **THEOREM** — a Lean declaration with an ACCEPTED receipt and a clean axiom audit
  (`propext, Classical.choice, Quot.sound` only).
* **CERTIFICATE** — exact rational arithmetic, replayable from the stored artifact.
* **NUMERICAL** — floating point on a finite grid.
* **MONTE CARLO** — simulation with a reported confidence interval.

An **ASSUMPTION** line names anything a theorem still takes as a hypothesis. Nothing
below is asserted beyond what the named evidence covers.

---

## 1. Structural — the family law for every `m ≥ 5`

Family `g_m = (-3, (-1)^p, (+1)^q, 3)` with `p = ⌈(m-2)/2⌉`, `q = ⌊(m-2)/2⌋`, so
`D = Σ|g_i| = m+4` and `Σ g_i ∈ {0,-1}`.

**Regret.** An ordering is a permutation; the retained prefix at budget `k` has sum
`s_k`, and the normalised regret is `(|s_k| − k mod 2)/D`, because every `g_i` is odd,
so `min_{|S|=k}|Σ_{i∈S} g_i| = k mod 2` by parity. Since `|s_k| ≡ k (mod 2)`, that
numerator equals `dfc s_k := |s_k| − |s_k| mod 2` — the even part of `|s_k|`, with no
index bookkeeping. **THEOREM** `StructuralFamilyLower.parity_bridge`.

**The lower bound, for every ordering.** Suppose an ordering pays nothing at any
budget. Then every partial sum, and both endpoints, lie in `{-1,0,1}`, so every single
element moves the sum by at most `2`. **THEOREM** `no_big_step`. But `3 ∈ g_m`.
Therefore the total defect is nonzero, and since every `dfc` is even it is at least
`2`. **THEOREM** `two_le_totalDefect`. No construction, no census, no hypothesis.

**The two lower bounds.** For any mixture `P` over orderings,
`Σ_k E_P[r_k] = E_P[Σ_k r_k] ≥ 2/D`, so some budget carries `≥ 2/(D(m-1))`
(**THEOREM** `avg_lower`); and every ordering's max is `≥ 2/D`, so `E_P[max_k r_k] ≥
2/D` (**THEOREM** `path_lower`).

**Achievability.** `altFrom` is the greedy alternation — from the current sum, move
back towards `0`. Under the invariant `|s| ≤ 1 ∧ |s − a + b| ≤ 1` it never leaves
`{-1,0,1}`, so an alternating block pays nothing (**THEOREM** `altFrom_defects`). Both
orderings are `block ++ [±3, ∓3] ++ block`:

    j = 2t+1 :  altFrom 0 t t      ++ [-3, 3] ++ altFrom 0 (p-t) (q-t)
    j = 2t   :  altFrom 0 t (t-1)  ++ [ 3,-3] ++ altFrom (-1) (p-t) (q+1-t)

In the odd case the first block ends at `0` and `-3` takes the sum to `-3`: defect
`3-1 = 2` at budget `2t+1`, and `+3` returns it to `0`. In the even case the first
block has **odd** length and ends at `-1` — a block ending at `0` must have even
length, by parity, which is exactly why the two cases are genuinely different — and
`+3` takes the sum to `2`: defect `2-0 = 2` at budget `2t`. **THEOREM**
`orderOdd_defects`, `orderEven_defects`; permutation by multiset,
**THEOREM** `orderOdd_multiset`, `orderEven_multiset`; packaged as
**THEOREM** `exists_one_defect`: *for every `m ≥ 5` and every budget `j ∈ {1,…,m-1}`
there is a permutation of `g_m` whose only defect is at `j`, and it equals `2`.*

**The law.** Mixing those `m-1` orderings uniformly,

    V_avg = 2/((m+4)(m-1)),   V_path = 2/(m+4),   V_path/V_avg = m-1.

**THEOREM** `avg_achieved`, `path_achieved`. **CERTIFICATE**
`P19_structural_construction_replay.json` stores the labelled orderings, the weights
`1/(m-1)` and the defect profiles for `m ≤ 30`, verifies the construction for
`m = 5…150`, and confirms by exhaustive search over **all** labelled permutations for
`m ≤ 9` that no ordering pays less than `2`.

**LIMIT.** The ratio `m-1` grows while the level `2/(m+4)` falls. This is **not** a
separation at a fixed normalised `ε`.

**FIXED.** The old saturation lemma required concentration for *every* ranking;
**THEOREM** `ratio_card_concentrated_on_support` needs it only on the support of `P`.

---

## 2. Support — decide versus recover, and growing `K`

Draws are IID from `p` on a finite space; class `i` has unsafe tips indexed by `κ i`,
injected by `u`, each of mass `pc i`; `s = Σ pc i`.

**The sampling law.** `Pr(all N draws land in A) = (Σ_{x∈A} p x)^N` — **THEOREM**
`SupportSamplingLaw.avoid_prob`, by `Finset.prod_univ_sum` on the product law. A
transversal (one unsafe tip per class) carries mass exactly `s`, so its complement
carries `1-s` — **THEOREM** `transversal_mass`; injectivity of `u` is what makes the
classes disjoint, and **no independence between the per-class counts is assumed** —
they come from one categorical stream.

**The upper end.** Exchanging the sum over histories with the sum over transversals,

    E ∏_i L_i = (∏_i b_i)(1-s)^N.

**THEOREM** `expected_prod_unseen`. With the pointwise `min_i L_i/(a_i+L_i) ≤ ∏_i L_i`
this caps the decide risk.

**The lower end.** `Pr(every class still hides a tip) ≥ (1-s)^N` — **THEOREM**
`good_event_lower`, by fixing one transversal and using monotonicity of indicators.

**The posterior.** Under the uniform prior over the `C(a+L,L)` labelings of a class's
unexplored tips, a fixed tip is unsafe with probability exactly `L/(a+L)` — **THEOREM**
`fixed_tip_unsafe_fraction`, from `Nat.add_one_mul_choose_eq`. A Bayes bound is a
minimax bound (**THEOREM** `bayes_le_minimax`), with equality for an equivariant rule
(**THEOREM** `minimax_eq_of_constant`).

**Recovery.** `1/2 ≤ 1 - ∏_i C(a_i+L_i,L_i)^{-1}` as soon as **any** class still hides
a tip (**THEOREM** `recover_lower_pointwise`, via `2 ≤ C(a+L,L)` by Pascal), and
`1 - ∏ C^{-1} ≤ Σ_i L_i` (**THEOREM** `recover_upper_pointwise`, via Weierstrass
`1 - Σ(1-c_i) ≤ ∏ c_i`). So the recovery exponent is `p_min`, not `s`. **That is the
separation**: deciding safely is governed by the total unsafe mass, recovering the
world by the smallest class mass.

**Growing `K`.** With `a_i = b_i = 1` and `p_i = P/K`, the optimal decide risk is
exactly `(1/2)·1{every class still hides its tip}` (**THEOREM**
`binary_decide_value`), so `R_dec(N) = (1/2)(1-P)^N`, flat in `K`; and
`∏ C^{-1} = (1/2)^U` exactly (**THEOREM** `growing_K_recover`). **CERTIFICATE**
`P20_support_growing_k.json`: at `P = 1/2`, `N_decide = 3` (ε = 0.1) and `6` (ε = 0.01)
for **every** `K ∈ {1,2,4,8,16,32}`, while `N_recover` goes `3 → 8 → 23 → 57 → 137 →
320` and `6 → 17 → 40 → 93 → 211 → 469`. The recovery identity is inclusion–exclusion
on `(1/2)^U = ∏_i (1 - X_i/2)`; it does **not** assume the `X_i` independent.

**LIMIT.** The fixed-`K` constants `k₀` and `B = ∏ b_i` depend on `K`; the growing-`K`
law above is a different model, not an extension of them. The coupon-collector
constant is not proved.

---

## 3. Functional — the allocation, every pair, and a witness that attains

Outsider cells `Fin 2 ⊕ Fin n`: two endpoints at `±(1-d)/2`, variance `1`, and `n`
middle cells at `z_i`, variance `v_i > 0`, `g_i = 1/2 - |z_i| ≥ d/2`. With
`S = Σ v_i/g_i²` and `A = 1/(16 + d²S)`,

    w(endpoint) = 4A  (all four: the incumbent's two and the outsider's two),
    w(middle i) = d² v_i A / g_i².

**Legality.** The weights sum to `1` over all `n+4` cells and are positive —
**THEOREM** `FunctionalAllocationJoin.budget`, `wt_pos`.

**The identity everything rests on.** `A·(σ_x/w_x) = gval(x)²/d²` with
`gval(endpoint) = d/2` — **THEOREM** `resistance_identity`. So an endpoint behaves
*exactly* like a middle cell sitting at the domain boundary `g = d/2`. That is why the
three pair cases of the instance module collapse into one.

**The geometry.** `gval a + gval b ≤ 1 - (mean a - mean b)` for every ordered pair of
distinct cells — both endpoint orders, all four endpoint/middle orientations, both
middle orders — **THEOREM** `mean_gap`; and `mean a - mean b < 1`, which is what the
bridge requires — **THEOREM** `mean_diff_lt_one`.

**The bridge, invoked.** `pairV` (the bridge's pair value) *is* `pairVal` at
`A = W/4` — **THEOREM** `pairV_to_pairVal`, so the two files speak about the same
quantity. Then every ordered pair clears `A d²/2` (**THEOREM** `every_pair_ge`), and
feeding that into `energyU_ge_pairV` gives

    for EVERY flipping alternative,  energyU ≥ A d²/2.

**THEOREM** `gamma_lower`.

**The matching witness.** Move all four endpoints to `±(1/2 - d/4)` and leave the
middle cells alone. The incumbent's spread becomes `1 - d/2`, the outsider's becomes
`1 - d/2`, so the alternative flips (**THEOREM** `witness_flips`), and each of the four
cells moves by `d/4` at weight `4A` and unit variance, so the cost is exactly
`4·(4A)(d/4)²/2 = A d²/2` (**THEOREM** `witness_energy`). Both halves together:
**THEOREM** `gamma_value`.

**The value.** `A d²/2 = c²/(n(32 + 2c²H_n))` with `H_n = S/n`, `d² = c²/n` —
**THEOREM** `value`. The `n` must be carried; dropping it is legitimate only when
reporting `nJ`.

**The uniform law.** `Σ v_i/(g_i+d/2)² ≥ (Σ v_i/g_i²)/(1+d/(2g_min))²` (**THEOREM**
`Splus_lower`), the sandwich is ordered (**THEOREM** `sandwich_order`), and its width
is at most `κ² = (1+d/(2g_min))²`, which is `≤ 4` on the whole domain `g_min ≥ d/2`
and tends to `1` **exactly when `d/g_min → 0`, not merely when `d → 0`** (**THEOREM**
`sandwich_ratio`). The counterexample `c=1, g_i=d/2, v_i=1` has ratio `→ 4`.

**LIMIT.** `FlipsU` uses `≤`, so the witness attains the minimum for *that*
alternative set; for strict rank inversion the same witness gives an infimum approached
by perturbation. And `A d²/2` is the value **at `w*`**: it is not shown optimal over
the design polytope, so it must not be written `Γ* = sup_w J(w)`.

---

## 4. Query — the whole chain, and where it still stops

### 4a. Gaussian derivatives and the level expansion

`hpoly σ n` is the Hermite-type sequence `H_0 = 1`, `H_{n+1} = H_n' - (y/σ²)H_n`, and

    dⁿ/dyⁿ e^{-y²/2σ²} = H_n(y) e^{-y²/2σ²}.

**THEOREM** `QueryGaussianLevel.iteratedDeriv_gauss`. Its degree-`n` coefficient is
`(-1/σ²)^n ≠ 0`, so `H_n ≠ 0` (**THEOREM** `hpoly_coeff`, `hpoly_ne_zero`).
Differentiating one mixture component `j` times in `h` at `h = 0` gives `(-g)^j` times
the `j`-th Gaussian derivative (**THEOREM** `iteratedDeriv_shift`) — that is precisely
where `g(x)^j`, and therefore the level moment `M_{W,j}(v) = Σ_{f_W(x)=v} π_x g(x)^j`,
comes from. Grouping the per-point sum into level moments: **THEOREM**
`sum_by_level`. If all level moments agree at order `j`, the order-`j` coefficient
vanishes identically: **THEOREM** `levelSum_eq_zero_of_levels_agree`.

### 4b. Non-vanishing — the step that is usually skipped

"One coefficient is nonzero" is **not** enough; the shifted Gaussian derivatives could
in principle cancel. Factor `φ_σ(y-v) = φ_σ(y) e^{vy/σ² - v²/2σ²}` (**THEOREM**
`gauss_shift`) and divide by the largest level's factor:

    T(y) = c_{v*} H_r(y - v*) + Σ_{v < v*} c_v H_r(y - v) e^{-(v*-v)y/σ² + const}.

Each term of the sum is a polynomial against a **decaying** exponential, so it tends to
`0` (**THEOREM** `poly_exp_decay`, via `Polynomial.tendsto_div_exp_atTop`). If `T ≡ 0`
then the polynomial `c_{v*}·H_r(·-v*)` would tend to `0` at `+∞`; by
`Polynomial.tendsto_nhds_iff` its leading coefficient would be `0`, so it would be the
zero polynomial — contradicting `c_{v*} ≠ 0` and `H_r ≠ 0`. **THEOREM**
`levelSum_ne_zero`.

### 4c. The lower Hellinger bound, from one interval

With `χ` the indicator of a finite interval `E`, pointwise
`χ(p-q) = χ(√p-√q)(√p+√q)` and `|χ(p-q)| ≤ (t/2)(√p-√q)² + (1/(2t))(√p+√q)²` for every
`t > 0` (**THEOREM** `young_pointwise`, `factor_pointwise`). The first integral is
`2H²`; the second is **exactly** `4 - 2H²`, because `(√p+√q)² + (√p-√q)² = 2(p+q)` and
both densities integrate to `1` (**THEOREM** `sqrt_sum_sq_identity`,
`sum_sq_integral`) — no second Cauchy–Schwarz is needed. So
`|ΔP(E)| ≤ tH² + (4-2H²)/(2t)` for every `t > 0` (**THEOREM** `gap_le_of_integrals`),
and optimising `t` at `√(2/H²)` gives `ΔP(E)² ≤ 8H²` (**THEOREM** `sq_le_of_all_t`).
Substituting a Taylor gap `|ΔP(E)| ≥ |a_E||h|^r/2`:

    H² ≥ a_E² |h|^{2r} / 32.

**THEOREM** `hellinger_lower_from_interval`.

**CORRECTION.** The plan's constant was `/16`, which comes from the cruder step
`|ΔP| ≤ 2√(H²)`. What the stated inequalities actually give is `/32`. The **order**
`h^{2r}` is identical, and that is what the rate law uses.

### 4d. The upper side — the envelope, and why the naive argument fails

`(p_{A,h} - p_{B,h})/p_0` is **not** uniformly small for any `h > 0`: Gaussian tails
break that. The correct route is `H² ≤ (1/2)∫ d_h²/p_{B,h}` (**THEOREM**
`chi2_pointwise`), a lower envelope for the mixture (one component already dominates
it, **THEOREM** `mixture_ge_component`), and

    e^{-y²/2σ² - M|y|/σ² - M²/2σ²} ≤ e^{-(y-m)²/2σ²} ≤ e^{-y²/2σ² + M|y|/σ²}

for `|m| ≤ M` (**THEOREM** `gauss_lower_envelope`, `gauss_upper_envelope`). The ratio
therefore carries `e^{3M|y|/σ²}`, and `3M|y| ≤ y²/4 + 9M²` (**THEOREM** `majorise`)
turns that into a Gaussian with a smaller rate times a constant. The polynomial factor
is handled by `x^n ≤ n^n e^x` (**THEOREM** `pow_le_exp`), giving
`(y²)^r ≤ (2r/b)^r e^{(b/2)y²}` (**THEOREM** `sq_pow_le_exp`), and the whole envelope
is integrable (**THEOREM** `envelope_integrable`).

**ASSUMPTION — the one link still open.** The uniform Taylor remainder
`|d_h(y)| ≤ C|h|^r(1+|y|^r)·envelope` is not derived in Lean. Its Lagrange form uses
exactly the derivatives of §4a, so the route is mechanical, but until it is written the
constant `c₊` remains **NUMERICAL**. What §4d closes is that the tails do **not**
obstruct the `h^{2r}` order.

### 4e. From `H²` to an integer sample count

For `0 ≤ H² ≤ 1/2`, `H² ≤ -log(1-H²) ≤ 2H²` (**THEOREM** `log_ge_self`,
`neg_log_le_two`; the upper half from `log(1/u) ≤ 1/u - 1` at `u = 1-H²`, and
`x/(1-x) ≤ 2x` exactly on `x ≤ 1/2`). Then `ρ^N = e^{-NL}` (**THEOREM**
`pow_eq_exp`), `NL ≥ log(1/(2ε))` suffices (**THEOREM** `sufficient_count`), the lower
bracket forces `N ≥ log(1/(4ε))/(2L)` (**THEOREM** `necessary_count`), and
`⌈log(1/(2ε))/L⌉₊` meets the sufficient condition (**THEOREM** `ceil_suffices`). With
`c₋h^{2r} ≤ H² ≤ c₊h^{2r}`:

    log(1/(4ε)) / (4 c₊ h^{2r})  ≤  N*(h,ε)  ≤  ⌈ log(1/(2ε)) / (c₋ h^{2r}) ⌉.

**THEOREM** `matching_rate`.

### 4f. Back to the regret of a real decision

For a decision kernel `D`, put `t(h) = Σ_{a ∉ G_A} D(a|h)`. Because `G_A ∩ G_B = ∅`,
`G_A ⊆ G_Bᶜ`, so pointwise `γ·t(h) ≤ Σ_a D(a|h)ℓ_A(a)` and
`γ·(1-t(h)) ≤ Σ_a D(a|h)ℓ_B(a)` (**THEOREM** `outside_cost`, `inside_cost`).
Integrating the first against `P_A` and the second against `P_B`:

    γ·e ≤ R,   for EVERY decision kernel.

**THEOREM** `regret_ge_gamma_error`. For the upper side, one explicit rule — a
deterministic test that then plays the selected world's own optimal action — pays `0`
when the label is right and at most `L_max` when it is wrong, so `R ≤ L_max·e`
(**THEOREM** `lrt_regret_le`). Quantifiers: **lower for all policies, upper for one**.
With the affinity bracket, `γρ^{2N}/4 ≤ R* ≤ L_max ρ^N/2` (**THEOREM**
`bayes_regret_window`). The prior is equal — this is Bayes risk, not worst-case
minimax.

### 4g. The measurement class, corrected

`Q4/Q5`. The class the code searches is **quadratic**, not linear: every linear
solution of the first-order equations is π-symmetric and therefore invisible at every
order. Two statements must stay apart: the chosen `g` **has** order `r = 2`; but
"order 2 is optimal in the quadratic class" is **false as stated**, because the
quadratic class contains the linear one. The correct claim is relative to the
**first-order-neutral** class. Without a modelling reason to impose that constraint, an
`r = 1` design is the mandatory comparator.

**MONTE CARLO + NUMERICAL** `P21_query_normalized_lrt.json`. Normalising both
measurements to `E_π[g²] = 1` first: `g₀`'s local exponent `2r` runs `2.59 → 3.70`
(`r → 2`) and `u`'s runs `1.36 → 1.88` (`r → 1`) — the order separation survives an
equal-amplitude comparison. The exact LRT error lands inside `[ρ^{2N}/4, ρ^N/2]` for
both. The negative control (`g ≡ 0`) gives `H² = 2.9×10⁻³³`.

**IMPORTANT AND NEGATIVE.** Fitting `H² = c h^k` on the two smallest pilot points gives
`g₀: c = 1.524×10⁻², k = 3.702` and `u: c = 2.856×10⁻⁴, k = 1.875`, so the constants
differ by a factor `53` and the crossover is at **`h* = 0.1133`**. Below `h*` the
lower-order measurement `u` is the more informative one, as the order law says; above
it the constants dominate and the `r = 2` measurement wins. The reported runs use
`h = 0.6`, which is **above** the crossover — their sample counts (`N = 4678` for `g₀`
versus `N = 41006` for `u`) must **not** be read as evidence about the order.

---

## 5. MASTER — three different problems, kept apart

### 5a. The four-alternative game is not the threshold class

With `θ` free in `ℝ⁴` and both group offsets free, take

    θ = (1, 0, 0, 1),   b = (0, 0);      λ = (1/4, -3/4, 0, 1),  b' = (3/4, 0),

with items `0,1` in group `0` and `2,3` in group `1`. Every ordinary query mean is
`(1,0,0,1)` in **both** worlds, yet the answer `{i : θ_i > 1/2}` changes from `{0,3}`
to `{3}`. **THEOREM** `MasterCalibrationLaw.hidden_shift_witness` (exact rationals).
Hence a group with no calibration query has `Γ = 0`, and P6's positive number is the
value of a four-alternative game — not the threshold rate.

### 5b. The full-class rate

Profiling the group shift out of the boundary alternative for item `i`:
`min_t [a(Δ-t)² + bt²]/2 = Δ²/(2(1/a+1/b))`, and it is **attained** at `t = aΔ/(a+b)`
(**THEOREM** `profiled_information`, `profiled_information_form`). A group that must
deliver information `h` costs at least `h(√m+√κ)²`, by Cauchy–Schwarz on
`(σ_m²x + σ_κ²z)(1/x + 1/z) ≥ (σ_m+σ_κ)²` — no optimiser is consulted (**THEOREM**
`group_cost_lower`) — and the split `z/x = √(m/κ)` attains it (**THEOREM**
`group_cost_attained`). Summing over `K` groups under unit budget:

    Γ* = Δ² / (2K(√m + √κ)²).

**THEOREM** `calibration_rate_upper` (every design) and `calibration_rate_attained`
(the symmetric design). **NUMERICAL** `P17_master_full_class.json`: 32/32 cells
(`K ∈ {1,2,4,8}`, `m ∈ {2,4}`, `κ ∈ {1/4, 2/3, 1, 4}`) agree to machine precision with
an independent bisection that uses only the budget's separability. A structure-free
Nelder–Mead cross-check never exceeds the closed form and undershoots by up to 8% at
`K = 8` — optimiser error in dimension `2K`, in the direction the theorem predicts.

### 5c. The anchor is mandatory — two separated certificates

`E_u(x,x₀;t) = D_u - M_u t + K t²/2 = D_u - M_u²/(2K) + (K/2)(t - M_u/K)²`, so
`I_u = D_u - M_u²/(2K)`, attained (**THEOREM** `MasterAnchorCertificate.energy_expand`,
`energy_completed`, `profiled_le`, `profiled_attained`). `K` is the only place the
anchor enters, which is exactly why buying it can help.

For **any** rational distribution `λ` over **pairs** `(u_j, t_j)` — several shifts per
alternative are allowed, which is precisely the multiplier-extraction bug the audit
found — put `H_e = Σ_j λ_j (d_{u_j,e} - t_j)²/(2v_e)` and `U₀ = max_e H_e/κ_e`. Then
for every `x ≥ 0` with `Σ κ_e x_e = 1`,

    J(x,0) ≤ Σ_j λ_j E_{u_j}(x,0;t_j) = Σ_e x_e H_e ≤ U₀ Σ_e κ_e x_e = U₀.

**THEOREM** `anchor_free_upper`. No complementary slackness, no claim that any cut is
active. Finally, with `U₀ < L₁` and one anchored design reaching `L₁`, no optimiser is
anchor-free — **THEOREM** `anchor_mandatory`, which assumes **no** optimality of the
anchored design and needs **no** value of the game.

**CERTIFICATE** `P12_master_anchor_required.json`: `U₀ = 0.013773103740`,
`L₁ = 0.014042993094`, gap `2.698893537968×10⁻⁴`, exact `Fraction`s at `c₀ = 1/10`.

**RETRACTED.** `sup_{x₀=0} J = U₀` is wrong; the certificate gives only `≤`. The three
MASTER results — the symmetric-family threshold `c* = (m-1)²/(m+3)²`, the finite
three-alternative `U₀ < L₁` at `c₀ = 1/10`, and the full-class rate of §5b — are
**three different problems**. None implies another, and the old `0.118` is none of
them.

---

## 6. D6 — a retraction, the clipped nuisance, and a strict separation

### 6a. The B-scalar is never blind

`I_B(d,x) = (dμ²/q + (q-d)x²/q)/2`, so at `q = 3, μ = 1/4, d = 1, x = 0` it equals
`1/96 > 0` — **THEOREM** `D6ScalarInformation.IB_at_zero` — and it is positive for
every `x` whenever `μ > 0`, `1 ≤ d ≤ q` (**THEOREM** `IB_pos`, `IB_never_blind`). The
A-pair *does* have a blind direction (`x = g`). So the mechanism is an **asymmetry**,
not "two disjoint blind directions" (**THEOREM** `blindness_asymmetry`). **The phase
transition must be explained by a certified value gap, not by blindness.**

### 6b. The nuisance clipped at the boundary

Minimising `Aν²/2 - Bν` over `ν ∈ [0,1]` puts the minimum at `clamp(B/A, 0, 1)`,
covering both boundary cases — **THEOREM** `clipped_min`. This is the step the uncapped
profile silently skipped.

### 6c. The certificate shapes, over every legal query

A design's value is at least `V` exactly when every alternative costs `≥ V`
(**THEOREM** `primal_lower`). A mixture `ρ` of alternatives whose average information
at **every** legal query `e` is at most `V κ_e` caps **every** legal design at `V`
(**THEOREM** `dual_over_all_queries`) — the hypothesis is universally quantified over
`e`, so it is not a scalar/pair-only check.

### 6d. A strict separation, correctly directed

**RETRACTED.** P7 compared `L_full` with `L_two` — both *lower* bounds. That proves
nothing about the two optima.

**CERTIFICATE** `P18_d6_full_vs_two.json`. `L_full` is the exact value of one full
design (a lower bound on `Γ_full`); `U_two` is a dual certificate valid for **every**
design supported on `{scalar B, B-pair}`, with charges at their certified **lower** end
(which can only raise the bound). `L_full > U_two` therefore proves
`Γ_full > Γ_two` strictly. Result: **strict in 6 of 12 cells** —
`(μ,q,t) = (1/4,8,2), (1/4,16,2), (2/5,8,1), (2/5,8,2), (2/5,16,1), (2/5,16,2)`, with
ratios `1.0108, 1.0033, 1.0083, 1.0273, 1.0030, 1.0088` — and **absent** in the other
six, where the ratio is `1.000000`. The third class earns its place only above a
certain `t`; below it the full design gives the two-class value.

Also fixed: information is exactly quadratic in `x`, verified by extracting the
coefficients from `{0,1,-1}` and checking them at three further points — 7092 exact
checks (**CERTIFICATE**); and LP multipliers are now read only from the cuts that were
in the **solved** LP, with a convergence flag per cell.

**STILL OPEN.** `sup_err_grid` is a grid supremum, not a continuous one; no modulus
between grid points, and **no phase boundary is certified**. `t_end` is not a phase
boundary. The alternative family is still `(d,x)` and the symmetry orbits, and that is
declared.

---

## 7. What this batch does **not** close

| | |
|---|---|
| Query | the uniform Taylor remainder, so `c₊` is still measured |
| D6 | the phase boundary; the continuous supremum; the full-game `Γ*` |
| Adaptive | `P(Eᶜ) ≤ δ`, the tracking step, the stopping-time tail; the sharp `1/Γ` |
| MASTER | an active-set derivative law (`value_improves_iff` stays a helper) |
| Functional | `J(w*)` optimal over the design polytope; the P4 side model's transfer |
| Gates | G03's prior columns are still `verified: false`; G3's preregistration evidence |
