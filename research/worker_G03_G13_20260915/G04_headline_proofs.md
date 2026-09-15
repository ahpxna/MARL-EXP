# G04 — human-readable proof of each headline

Written as mathematics, not as an audit list. Each section says what kind of object
the statement is: **THEOREM** (a Lean proof exists, receipt named), **CERTIFICATE**
(an exact finite rational computation), **NUMERICAL** (a solver, certified per cell),
or **MONTE CARLO**. Where a step is assumed, it is stated as an assumption.

---

## Support — deciding safely is exponentially cheaper than recovering

**Statement.** `K` classes; class `i` has `a_i ≥ 1` safe and `b_i ≥ 1` unsafe tips,
each unsafe tip observed with probability `p_i`; `s = Σ p_i < 1`, `p_min = min p_i`.
With `L_i` the unseen unsafe count of class `i` after `N` draws,

  `k₀ (1−s)^N ≤ R_dec ≤ B (1−s)^N`,  `k₀ = min_i 1/(a_i+1)`, `B = ∏ b_i`,
  `α (1−p_min)^N ≤ R_rec ≤ (Σ b_i)(1−p_min)^N`,  `α = a_{i*}/(a_{i*}+1)`.

**Proof.** *Lower, decide.* Fix one unsafe tip in each class. No draw hits any of
those `K` tips with probability exactly `(1−s)^N`, because a single draw hits the
chosen tip of class `i` with probability `p_i` and these events are disjoint. On that
event every `L_i ≥ 1`, and `L/(a+L)` is increasing in `L` (its derivative is
`a/(a+L)² ≥ 0`), so `min_i L_i/(a_i+L_i) ≥ min_i 1/(a_i+1) = k₀`. **THEOREM**:
`SupportDecideExponent.one_le_frac_lower`.

*Upper, decide.* Since `a_i ≥ 1`, `L/(a+L) ≤ L`. **THEOREM**:
`SupportDecideExponent.frac_le_self`. And for non-negative integers
`min_i L_i ≤ ∏_i L_i` — if some `L_i = 0` both sides vanish, otherwise every factor
is `≥ 1` so the product dominates any single factor. **THEOREM**:
`SupportDecideExponent.min_le_prod`. Hence
`R_dec ≤ E[∏ L_i]`. The product of the unseen counts is the number of tuples
picking one unseen tip per class — **THEOREM**:
`SupportTupleCount.prod_card_eq_tuples`, `|piFinset U| = ∏ |U_i|` — and each of the
`B` tuples is unseen with probability `(1−s)^N`, so `E[∏ L_i] = B(1−s)^N`.

*Recovery.* Lower: a single fixed tip of the class attaining `p_min` is unseen with
probability `(1−p_min)^N`, and then the posterior cannot do better than
`1 − 1/(a+1)`. Upper: union bound over all unsafe tips. **THEOREM** for the pointwise
half: `SupportRecoverySandwich.recovery_sandwich`.

**Assumed, not proved.** That a fixed tuple is unseen with probability `(1−s)^N`.
It is checked against the exact joint law (inclusion–exclusion) at 105 rational
checkpoints, 5 configurations × 7 values of `N`: **CERTIFICATE**,
`P13_support_decide_exponent.json`. The `K`-class posterior/minimax step is not
re-derived; `passive_minimax` is the one-class statement.

---

## Structural — the execution gap equals the number of budgets

**Statement.** With `b` live budgets, for every distribution `P` over orderings and
non-negative regret `r`,

  `avgVal(P) ≤ pathVal(P) ≤ b·avgVal(P)`,  and  `eps_nest ≤ b·avgVal(P)`.

On the family `g_m = (−3, (−1)^p, (+1)^q, 3)` with `p+q = m−2`,
`eps_nest = 2/(m+4)`, `V_avg = 2/((m+4)(m−1))`, hence `V_path = (m−1)·V_avg`.

**Proof of the general part.** `avgVal ≤ pathVal`: for each budget `k`,
`Σ_π P_π r(π,k) ≤ Σ_π P_π max_k' r(π,k')`, and take the sup over `k`.
`pathVal ≤ b·avgVal`: `max_k r ≤ Σ_k r` for `r ≥ 0`, so
`pathVal ≤ Σ_k E_P[r_k] ≤ b·max_k E_P[r_k]`. `eps_nest ≤ pathVal` because `pathVal`
is an average of `max_k r(π,·) ≥ eps_nest`. **THEOREM**:
`StructuralAvgPathGap.{avg_le_path, path_le_card_avg, eps_le_path, eps_le_card_avg}`.

**Why the family saturates.** Equality throughout needs two things: the cheapest
ordering's regret must sit on ONE budget (so `Σ_k r = max_k r`), and every budget
must carry the same expectation (so `Σ_k E[r_k] = b·avgVal`). Those two force
`pathVal = b·avgVal`. **THEOREM**:
`StructuralSaturation.ratio_card_of_concentrated_and_balanced`.

**Assumed, not proved.** That `g_m` satisfies the two conditions. For this family the
regret depends only on how many of each sign have been taken — `σ = −3n₃⁻ − n₁⁻ +
n₁⁺ + 3n₃⁺`, `L = |TOT − σ|/D`, `D = m+4` — so the ordering DAG has `O(m²)` states
rather than `2^m`, and both conditions are verified exactly at 28 values of `m` up to
`m = 40`: **CERTIFICATE**, `P14_structural_family_allm.json`. This is a computation
at each `m`, not an induction.

**Do not overstate.** `eps_nest = 2/(m+4)` shrinks. The *ratio* grows; the separation
*level* does not. Concatenating two witnesses does **not** amplify — the budgets are
shared and the blocks interfere.

---

## Functional — the heterogeneous lower bound at the explicit allocation

**Statement.** At `u = c²H_n/(16+c²H_n)`, `w_i ∝ σ_i/g_i²`, endpoints `(1−u)/4`,

  `J(w*) = c² / ( n (32 + 2c² H_n) )`,  provided `g_i ≥ d/2` for every middle cell.

**Proof.** Write `r = σ/w` for a cell's resistance, `R = r_a + r_b`, `B = 1/(2R)`,
`A = 1/(2(1/w_{I0}+1/w_{I1}))`. The pinch value `A·B(1−D)²/(A+B)` beats `A d²/2`
exactly when `(1−D)² ≥ d²(A·R + 1/2)` — **THEOREM**:
`FunctionalHeterogeneousInstance.pairVal_ge_iff`. At this allocation two identities
hold: `A·r_endpoint = 1/4` and `A·r_middle(i) = g_i²/d²`, because
`A = 1/(16+c²H_n)` and `u(16+c²H_n) = c²H_n` give `A/u = 1/(c²H_n)`. Then:

* endpoint/endpoint: `D = ρ = 1−d`, both sides are `d²` — equality;
* endpoint/middle: `1−D ≥ g+d/2` and the criterion becomes `g ≥ d/2`;
* middle/middle: `1−D ≥ g_a+g_b` and it becomes `g_a g_b ≥ d²/4`.

All three reduce to the same domain condition. **THEOREM**:
`{endpoint_pair_ok, mixed_pair_ok, middle_pair_ok}`, and the endpoint pair attains
the bound (`endpoint_pair_value`), giving the value (`instantiated_value`).

The two geometric inequalities are **derived**, not assumed: with `g = 1/2 − |z|`,
`z ≥ −(1/2−g)` gives `1−D = (1+d)/2 + z ≥ g + d/2`, and the middle/middle case is the
same computation. **THEOREM**: `FunctionalGeometryDischarge.*`.

**Sharpness.** Below `g = d/2` the endpoint/middle criterion fails, the endpoint pair
stops being the minimiser, and the formula is no longer a lower bound — **THEOREM**:
`domain_is_sharp`, and **CERTIFICATE** on 8 out-of-domain configurations.

**Not proved.** That `J(w*)` is the optimum over the whole design space. The `n` in
the denominator must be written: `n·J(w*) = c²/(32+2c²H_n)` is the normalised form.

---

## D6 — removing the cap changes the phase, and a third measurement class appears

**Statement (algebra).** With `D_d = c(1−η)(q−1) + 2η(2q−d−2)` and the profile `P_d`,

  `G_d(η,x) ≥ P_d`,  `P_d − d·P_1 ≥ 0`,  `P_1 ≥ 0`,  for all `0 ≤ η ≤ 1`,

so every alternative costs at least `P_1`, with equality when the `d = 1` nuisance
minimiser is legal. **THEOREM**: `LeanD6UncappedProfileV1`, 13 audited names. The
decisive identity is

  `P_d − d P_1 = d η g² (d−1)[c(1−η)+4η][c(1−η)(q−1)+2η(q−2)] / (c q D_1 D_d) ≥ 0`.

**Statement (phase).** The binding dual orbit is always `(s,t,b) = (2,0,0)`, the
A-pair. Its per-sample information is a **perfect square**,
`I_A(d,x) = c_A(q,d)(g−x)²/2` with `c_A = (2(q²−1)d + 2(q+1)d²)/((q+1)²q)`, because
`t − b = 0` kills the linear term. Hence `c_A > 0` for `d ≥ 1` and `c_A` is
increasing in `d` — the difference is
`(d₂−d₁)(2(q²−1)+2(q+1)(d₁+d₂))/((q+1)²q)` — so the A-pair binds at `d = 1`, and it
is blind **only** on the line `x = g`, whereas the B-scalar is blind at `x = 0`.
Disjoint blind directions is the structural reason a mixture of the two beats either.
**THEOREM**: `LeanD6ThreeClassPhaseV1`.

**NUMERICAL.** That the optimal support actually changes at `T_c(μ)` — below it
`{scalar B, B-pair}`, above it `{B-pair, A-pair}` — is a cutting-plane solve over
every legal orbit, certified per cell by a rational primal/dual pair (relative gap
`~2×10⁻⁷`): `P7_d6_full_design.json`. An LP optimum is **not** a universal optimum,
and the phase boundary is a bracket, not a formula. `t_end` is a property of the `η`
family and is **not** the boundary of the full game.

---

## Query — the leakage order fixes the transcript length and the regret

**Statement.** If the measurement has leakage order `r` and
`c₋h^{2r} ≤ H² ≤ c₊h^{2r}`, then for fixed `ε ∈ (0,1/4)`,

  `log(1/(4ε))/(4c₊h^{2r}) ≤ N*(h,ε) ≤ ⌈log(1/(2ε))/(c₋h^{2r})⌉`,

and, reducing decisions to tests, the average regret obeys
`(γ/4)ρ^{2N} ≤ R ≤ (L_max/2)ρ^N`.

**Proof.** The Hellinger affinity tensorises, and for equal priors
`(1/4)ρ^{2N} ≤ e*_N ≤ (1/2)ρ^N` — **THEOREM**: `LeanQueryAffinityTestingV1` (the
upper is Bhattacharyya, the lower is `1 − TV ≥ ρ²/2`). Inverting with `L = −log ρ`
and `H² ≤ L ≤ 2H²` gives the sample complexity — **THEOREM**:
`QueryRateAssembly.rate_two_sided`; the direction `H² ≤ L` is proved from
`log x ≤ x−1`, the direction `L ≤ 2H²` is **assumed**.

For the regret: if the two good sets `G_W = {a : ℓ_W(a) < γ}` are disjoint, every
decision is expensive in at least one world — **THEOREM**:
`QueryRegretChain.mislabel_costs` — so an algorithm's decision induces a test whose
error forces regret `≥ γ`; and the likelihood-ratio test between the two worlds' own
optimal decisions pays at most the cross-world loss `L_max`. **THEOREM**:
`QueryRegretChain.regret_window`.

**Constants, MEASURED not proved.** On the real finite Gaussian mixture the level
coefficients below order `r` vanish identically, the dominating level `v*` is
exhibited, and the tail domination is verified (the ratio to the leading term reaches
`1.000000000` at `y = v*+640`, computed in the stable ratio form because evaluating
the two Gaussians separately underflows first). An interval `E` on which `Δ_r` keeps
its sign gives `a_E`, and `|P(E)−Q(E)| ≤ 2√(H²)` yields `c₋ = a_E²/16`:

| | order 2 (`g₀`) | order 1 (`u`) |
|---|---|---|
| `c₋` | `9.056×10⁻⁷` | `7.171×10⁻⁷` |
| `c₊` | `2.527×10⁻⁵` | `5.001×10⁻⁵` |

`P15_query_hellinger_order.json`. The geometry gives `γ = 13983/32768` and
`L_max = 2401/4096` at budget 1, exactly: `P16_query_regret_chain.json`. The rate is
matched; the constants are `28×` (r=2) and `70×` (r=1) apart.

---

## MASTER — calibration has a price, and below it the anchor is mandatory

**Statement (threshold, symmetric family).** `m+1` ordinary unit-price queries, mean
`a·e₀` at the truth and `a·e_u` at alternative `u`, one common unknown offset
profiled out, an anchor reading the offset at price `c`. Then the anchor-free value
is `V = a²(m+3)²/(8(m+1)²)`, and the critical price is exactly

  `c* = (m−1)²/(m+3)²`.

**Proof.** *Above.* Take the shift `t = a(m−1)/(2(m+1))`. Every ordinary query then
has the same dual coefficient `V`, and the anchor's is `c*·V`. Averaging the nuisance
quadratics over all alternatives and using the budget turns this into a bound on
`min_u I_u` for **every** feasible allocation, symmetric or not — **THEOREM**:
`MasterAnchorThreshold.global_upper`. *Below.* Scale the ordinary design by `1−cz`
and spend `z` on exposure. The exact gain is

  `(profile − V)·(1+(1−c)z)·8(m+1)² = a²z[(m−1)² − c(m+3)² − c((1−c)(m+3)²+(m−1)²)z]`

— **THEOREM**: `gain_cleared` (with `K` kept as an atom, which is what lets the
denominators clear) composed with the polynomial identity `gain_poly`. At
`z = (c*−c)/(2c(1−c+c*))` the bracket is positive, so the value strictly rises —
**THEOREM**: `below_threshold`. Together: above `c*` no allocation beats the
anchor-free optimum; below it one does.

**Statement (mandatory anchor, finite instance).** At `c₀ = 1/10` on the four-item
instance, with a rational `λ` on cut pairs `(u_j,t_j)`,

  `sup_{x₀=0} J ≤ U₀ = 0.013773103740 < L₁ = 0.014042993094 = J(x⁽¹⁾)`, `x₀⁽¹⁾ > 0`,

gap `2.698893537968×10⁻⁴` in exact `Fraction`s. The left-hand side is an UPPER BOUND
on the anchor-free supremum, never its value. Hence every design reaching `L₁` —
in particular every optimizer — has `x₀ > 0`. **CERTIFICATE**:
`P12_master_anchor_required.json`; the finishing lemma is
`MasterAnchorThreshold.anchor_required`. The upper certificate needs **no**
optimality of `λ`: `J(x,0) ≤ Σ_j λ_j E_{u_j}(x,0;t_j) = Σ_e x_e H_e ≤ U₀`.

**Corrections recorded.** This supersedes the earlier P8 threshold: its multiplier
extraction kept only the cuts whose shift equalled the profiling shift and produced
`0.0286687` against a primal of `0.0137731`. And the claim that *no* allocation
zeroes every `M_u` is **false** — the uniform `1/4` allocation does; the correct
reading is that cancelling the offset costs discrimination.

**Rank dichotomy.** A mixture of controls beats every single control only if the
nuisance has rank `≥ 2`: for `p = 1`, `G_{uℓ} = α_u β_ℓ` and
`min_u Σ ρ_ℓ α_u β_ℓ = (Σρβ)(min α) ≤ (max β)(min α)`. **THEOREM**:
`MasterGroupCalibration.rank_one_no_complementarity`, with a rank-2 witness showing
sharpness.

---

## Adaptive — only the composition

**Statement.** On an event `E` where the certificate holds by epoch `k`, a loop that
stops only on a certificate is correct and stops by `k`; and the doubling schedule
spends `< 4B*`.

**Proof.** `Σ_{i≤K} b₀2^i = b₀(2^{K+1}−1) ≤ 2·b₀2^K`, so the total is at most twice
the last epoch; if `k` is the first epoch reaching `B*` then `b₀2^{k−1} < B*`, so the
total is `< 4B*`. **THEOREM**: `AdaptiveLoopJoin.{two_pow_sum, total_le_two_last,
doubling_factor}`; the composition is `AdaptiveConfidenceJoin.guarantee_on_event`.

**Open — and this is why Adaptive is a section, not a paper.** `P(Eᶜ) ≤ δ` for the
GLR threshold, the tracking step, and the tail of the stopping time are all
unproved. The simulation measures the realised constant and a zero error rate over
200 runs; that is **MONTE CARLO**, not a guarantee.
