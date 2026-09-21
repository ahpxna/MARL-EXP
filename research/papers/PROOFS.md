# The central arguments, written out

This file exists so a reader can check the mathematics **without reading any Lean**. Every
argument below is also formalised, and the Lean name is given, but the proof here is meant
to stand on its own: setup, claim, proof, and — stated in the same breath — exactly what
the claim does *not* cover.

Conventions. `Cell r = Fin 4 ⊕ (Fin r × Bool)`: four anchors and `r` disjoint middle pairs.
Arm `A` is the anchors `0,1`; arm `B` is the anchors `2,3` together with all the pairs.
A *design* (allocation) `w` is a probability vector on cells. The *energy* of a design
against a candidate world `λ` at true world `θ` is

$$\mathcal{E}(w,\lambda)\;=\;\tfrac12\sum_e w_e\,\frac{(\lambda_e-\theta_e)^2}{\sigma_e^2}.$$

The variance profile is `1` on anchors and `M` on pairs. The base world `θ₀` has arm `A`'s
anchors at `(-1/2,+1/2)` and all of arm `B` at zero: this centres both arms — which is what
puts it in the class where `energy` *is* the Gaussian KL rather than a proxy for it — while
preserving the unit gap `θ₀(1) − θ₀(0) = 1` that every bound uses.

---

## A1. The true game is cheap: `Γ_true ≤ 1/(8Mr)`

**Claim.** For every allocation `w` and every `d > 1/2` there is an alternative costing at
most `d²/(2Mr)`. Hence `Γ_true = sup_w inf_λ 𝓔(w,λ) ≤ 1/(8Mr)`.

**Proof.** The `r` middle pairs are disjoint and the design has unit total mass, so the pair
weights `p_j = w(j,\text{true}) + w(j,\text{false})` satisfy `Σ_j p_j ≤ 1`. By pigeonhole
some pair `j` has `p_j ≤ 1/r`.

Move that pair alone: `λ = θ₀` except `λ(j,\text{true}) = +d`, `λ(j,\text{false}) = -d`.
Only two cells move, both of variance `M`, so

$$\mathcal{E}(w,\lambda)=\tfrac12\Big(w_{(j,\top)}\tfrac{d^2}{M}+w_{(j,\bot)}\tfrac{d^2}{M}\Big)
=\frac{p_j d^2}{2M}\;\le\;\frac{d^2}{2Mr}.$$

It remains to check this `λ` really is an alternative, i.e. that arm `B`'s range has caught
arm `A`'s. Arm `A` is untouched, so `range_A(λ) = |1/2 − (−1/2)| = 1`. Arm `B` now contains
the values `+d` and `−d` (and zeros), so `range_B(λ) ≥ 2d`. For `d > 1/2` we get
`range_B > 1 = range_A`, so `λ` is an alternative. Taking `d ↓ 1/2` gives the constant.

**The mechanism, and why it survives optimisation.** The adversary reads `w` *first* and
then picks the pair. That is why optimising the allocation does not help: whatever the
design, some pair is starved, and that pair is the one that moves.

**Scope.** This is an upper bound on the game value. It says nothing about which designs
are good.

*Lean: `exists_light_pair`, `pair_shift_energy`, `light_pair_energy_le`, `pairShift_mem_alt`,
`trueGame_le`.*

---

## A2. The true game is not free: `Γ_true ≥ 1/(128(4+2rM))`

**Claim.** The anchor design `w*` — mass `1/(4+2rM)` on each anchor and `M/(4+2rM)` on each
pair cell — has value at least `1/(128(4+2rM))` against *every* alternative.

**Proof.** This design makes the precision uniform: `w*_e/σ_e² = 1/(4+2rM)` for every cell,
anchor or pair. So for any `λ`, writing `δ = λ − θ₀`,

$$\mathcal{E}(w^\star,\lambda)=\frac{1}{2(4+2rM)}\sum_e \delta_e^2 .$$

So it suffices to show every alternative has `Σ_e δ_e² ≥ 1/64`.

Let `λ` be an alternative: `range_A(λ) < range_B(λ)`. Choose `p` and `q` attaining the
maximum and minimum of `λ` over arm `B`'s cells. Because the alternative is *strict*, `p ≠ q`.
Now `range_B(λ) = λ_p − λ_q`, and `range_A(λ) ≥ 1 + δ_1 − δ_0` since arm `A`'s anchors sit a
unit apart at `θ₀`. Using `θ₀ ≤ 3/4`-flatness on arm `B` (at `θ₀` arm `B` is identically
zero, so this is immediate), the strict inequality rearranges to

$$\delta_0-\delta_1+\delta_p-\delta_q\;>\;\tfrac14 .$$

Four numbers whose alternating sum exceeds `1/4` have squared norm at least `1/64`: by
Cauchy–Schwarz, `(x₀−x₁+x₂−x₃)² ≤ 4(x₀²+x₁²+x₂²+x₃²)`, so the squared norm exceeds
`(1/4)²/4 = 1/64`. The four cells `0, 1, p, q` are distinct — `p,q` are arm-`B` cells and
`0,1` are arm-`A` anchors — so their squares are part of the total. ∎

**Scope.** A lower bound *via one exhibited design*. It does not claim `w*` is optimal.

*Lean: `anchorDesign`, `contrast_moves`, `four_sq_lower`, `rpair_true_ge`, `trueGame_ge`.*

---

## A3. The surrogate's own game is bounded by absolute constants

The frozen-linear surrogate does **not** test `range_A < range_B`. It pins the extremum
*indices* of the current world and tests one linear contrast:

$$\Lambda_{\mathrm{frozen}}=\{\lambda:\ (\lambda_1-\lambda_0)-(\lambda_2-\lambda_3)\le 0\}.$$

**These are different sets, and the difference matters.** Take arm `A` at `(0,1)`, arm `B`'s
frozen maximum at `−2`, middles at `0`. Its true `B`-range is `2 > 1`, so it *is* a true
alternative; but its frozen contrast is `(1−0) − (−2−0) = 3 > 0`, so it is *not* a surrogate
alternative. Set equality is false, and we never assume it.

**Claim.** `1/32 ≤ Γ_frozen ≤ 1`.

**Lower bound.** Take the uniform-anchor design (`1/4` on each anchor, nothing on pairs).
Its energy against any `λ` is `(Σ_{a<4} δ_a²)/8`, since the pairs carry no weight and the
anchors have unit variance. At `θ₀` the frozen contrast equals `1`; for `λ` to be a frozen
alternative the contrast must reach `0`, so

$$\delta_0-\delta_1+\delta_2-\delta_3\;\ge\;1 .$$

By the same Cauchy–Schwarz step, `Σ δ_a² ≥ 1/4`, hence the energy is at least `1/32`.

**Upper bound.** Arm `B`'s two frozen anchors have total weight at most `1`, so one of them
carries at most `1/2`. Move that one by `±2` (raise anchor `2`, or lower anchor `3`): either
flips the contrast from `+1` to `−1`, and costs `w·2²/2 = 2w ≤ 1`. ∎

**Consequence.** `Γ_frozen` sits between two absolute constants while `Γ_true` falls like
`1/(rM)`. So

$$\frac{1}{128(4+2rM)}\;\le\;\frac{\Gamma_{\mathrm{true}}}{\Gamma_{\mathrm{frozen}}}\;\le\;\frac{16}{Mr},$$

both `Θ((rM)^{-1})`. The separation is about the surrogate the paper criticises, and it
holds at **uniform variance** `M = 1`: it is driven by how many alternatives the surrogate
declines to look at, not by conditioning.

**Scope.** What is *not* established: the passage from these range-and-contrast alternative
sets to the observation model's own alternative class, through the actual response map.

*Lean: `proxyAlt_ne_frozenAlt`, `four_sq_lower_one`, `energy_wUnif`, `frozenValue_unif_ge`,
`frozenValue_le`, `frozen_games_theta`.*

---

## A4. From starvation to a leakage bound, without a monotonicity modulus

The starvation theorems assumed `AnchorMonotone`: raising *any one* anchor weight strictly
increases the surrogate. The real frozen-linear surrogate fails that at the boundary — with
another essential anchor still unmeasured, raising the first can leave the value at zero. So
a bound derived from it would not apply to the object being criticised.

Positive homogeneity does apply and suffices. Let `a = Σ_{anchors} w_e` and let `w̃` zero the
pair cells and rescale the anchors by `1/a`. The surrogate reads only the anchors and is
homogeneous of degree one in them, so `J(w̃) = J(w)/a`.

**Claim.** If `w` is within `ε` of the surrogate's optimum and `J(w) > 0`, then the mass off
the anchors is at most `ε/J(w)`.

**Proof.** `w̃` is a legal allocation, so near-optimality gives `J(w)/a = J(w̃) ≤ J(w) + ε`,
i.e. `J(w) ≤ a(J(w)+ε)`. Since the middle mass is `1 − a` and `a ≤ 1`,

$$(1-a)J(w)\;\le\;a\varepsilon\;\le\;\varepsilon .$$

Dividing by `J(w) > 0` gives the bound; at a near-optimum with `J(w) ≥ Γ_proxy − ε` it reads
`ε/(Γ_proxy − ε)`. ∎

This is the bridge from *static* starvation to the *exploration cost* of a policy: what the
true alternatives can be measured with is the off-anchor mass, not the design's optimality.

**Scope.** Homogeneity is used as a hypothesis; deriving it from the frozen-linear formula
is a short calculation that is not written. Requires `ε ≥ 0` (otherwise `aε ≤ ε` fails).

*Lean: `anchorMass_add_pairMass`, `renormAnchors_isAlloc`, `middle_mass_le_of_homogeneous`,
`middle_mass_le_of_near_optimum`.*

---

## B1. The per-pair test bound, derived rather than assumed

An upper bound that *assumes* a per-pair error level assumes the result. Here the test is
exhibited and its error computed.

Let `p,q` be two candidate laws on a finite observation alphabet, `P,Q` their `N`-fold
products. The test declares the first world exactly on the sequences it makes at least as
likely.

**Step 1 — the error is an identity, not a bound.** On a sequence where `Q ≤ P` the test
says `p`, so it errs only under `q`, contributing `Q(t)`; on the complement it errs only
under `p`, contributing `P(t)`. Summing,

$$\mathrm{err}_{\mathrm I}+\mathrm{err}_{\mathrm{II}}=\sum_t\min\big(P(t),Q(t)\big).$$

**Step 2 — minimum to geometric mean.** For `a,b ≥ 0`, `min(a,b)² ≤ ab`, so
`min(a,b) ≤ √(ab)`.

**Step 3 — tensorisation.** `√(P(t)Q(t)) = ∏_i √(p(t_i)q(t_i))`, and summing a product over
all sequences factorises:

$$\sum_t\prod_i\sqrt{p(t_i)q(t_i)}=\Big(\sum_o\sqrt{p(o)q(o)}\Big)^{N}=(1-H^2)^N,$$

where `H² = 1 − Σ_o √(p q)` is the squared Hellinger distance.

**Step 4 — exponential.** `1 − x ≤ e^{−x}`, so `(1−H²)^N ≤ e^{−NH²} ≤ e^{−Nc}` whenever
`H² ≥ c`. Taking `N ≥ log(K/δ)/c` makes this at most `δ/K`.

**Step 5 — per world, then union.** Both error types are non-negative and their *sum* is at
most `δ/K`, so **each** is at most `δ/K`. Summing over `K` pairs, each error type totals at
most `δ`. (Bounding the *average* of the two would bound neither world's own error.)

With `c = c₀h^{2r}` this reads `N = O(h^{−2r}\log(K/δ))` — the same exponent in `h` that the
lower bound produces.

**Scope.** Finite observation alphabet. The separation `c₀h^{2r} ≤ H²` is an *input* here;
it is what the order law supplies on the linear class, and the two are not yet composed into
one statement. A non-degenerate pair with `0 < H² < 1` is exhibited, so the theorem is not
vacuous.

*Lean: `err_eq_sum_min`, `affinity_prodLaw`, `err_le_affinity_pow`, `lrt_error_le`,
`lrt_error_each`, `identify_sample_complexity`, `decoder_total_error`, `separation_nonvacuous`.*

---

## B2. Two observation orders, and why they separate

Write `θ ∼_s λ` for indistinguishability at order `s`, and `class_s(θ)` for the induced
class. Two facts pin the orders, on the real `selectedRadius` geometry.

**Safe order is 1.** At order `0` every world is in one class, and no single answer is safe
for all of them — so the order-`0` class is an *obstruction*. At order `1` each class has a
common safe answer. Hence `s_safe = 1`.

**Identification order is `m−1`, exactly.** `θ ∼_s λ` implies `θ = λ` for all `θ,λ` **iff**
`s ≥ m−1`. The `iff` is what makes `m−1` tight on both sides rather than an upper estimate.

**Why the geometry is the interesting one.** Any two worlds share a safe answer (`m ≥ 3`),
while no answer is safe for all of them. Overlapping-but-not-nested safe sets are precisely
what makes the safe order small and the identification order large; if the safe sets were
nested or disjoint the two orders would coincide.

**Scope — and this is the important caveat.** `∼_s` is defined on the world *index*
("equal, or both at index ≥ s"). The geometry is the model's, but the partition is *posited*,
not derived from what the queries can resolve at order `s`. Turning `s_safe = 1` and
`s_id = m−1` into a sample-complexity separation needs `∼_s` identified with the relation
induced by the moments visible up to order `s`; only then do the lower bound and B1 attach
to it. Neither implication is proved. The two orders must not be quoted as sample
complexities.

*Lean: `identifiableAt_iff`, `decidableAt_of_one_le`, `not_decidableAt_zero`,
`decide_order_lt_identify_order`, `safe_sets_overlap`, `no_common_safe_all`,
`obstruction_at_order_zero`.*

---

## B3. The crossover: why the two scales add instead of interfering

For the widened probe `g_η = (z₄+z₅+z₆+ηz₄z₅)/(3+η)` against the hidden character
`χ = z₄z₅z₆`, the three moments are exact:

$$\mathbb E[\chi g_\eta]=0,\qquad
\mathbb E[\chi g_\eta^2]=\frac{2\eta}{(3+\eta)^2},\qquad
\mathbb E[\chi g_\eta^3]=\frac{6}{(3+\eta)^3}.$$

The density difference between `v = +1` and `v = −1` then has an **odd** channel
`A(y) = f''(y−1) − f''(y+1)` at coefficient `ηh²/(3+η)²`, and an **even** channel
`B(y) = f'''(y−1) − f'''(y+1)` at coefficient `h³/(3+η)³`.

**Claim.** The cross term of the leading quadratic form vanishes.

**Proof.** The base density `p₀` is even. `A` is odd and `B` is even, so `AB/p₀` is odd, and
the integral of an odd integrable function over the line is zero. Hence

$$\int\frac{(\alpha A+\beta B)^2}{p_0}
=\alpha^2\int\frac{A^2}{p_0}+\beta^2\int\frac{B^2}{p_0},$$

with no interference term. Substituting the two coefficients gives exactly `η²h⁴ + h⁶`. ∎

This is a *parity* cancellation — it holds identically, not to leading order, and no
estimate is involved. A sweep of fitted slopes cannot establish it, because a sweep cannot
see whether a cross term is absent or merely small.

**Scope.** Three things stand between this mechanism and the law, none of them proved: that
`A` and `B` are not identically zero, that the two integrals are finite, and that the
remainder is bounded **uniformly in `(h,η)`**. It is also a law for the single probe `g_η`;
a class-level crossover needs the widened class defined and a uniform upper bound over it.

*Lean: `moment_one/two/three`, `integral_odd_eq_zero`, `cross_term_vanishes`,
`quadratic_splits`, `two_scale_shape`, `crossover_balance`.*

---

## B4. The query class is a theorem-level restriction, not a convenience

It is tempting to state the order law for all probes of degree at most `r−1`, reasoning that
a probe below degree `r` cannot contain the degree-`r` parity. That reasoning is wrong, and
one probe refutes it.

At `r = 3` take `g = (z₄z₅ + z₆)/2`, which is legal (degree 2, `‖g‖_∞ ≤ 1`). Then

$$g^2=\frac{1+z_4z_5z_6}{2},\qquad\text{so}\qquad \mathbb E[\chi g^2]=\tfrac12 .$$

The *square* of a degree-2 probe contains the parity. On the script's own observation model
this gives `E₊[Y³] − E₋[Y³] = 3h²` exactly, and with sixth moments bounded uniformly for
`h ≤ 1`, Cauchy–Schwarz yields `H² ≥ ch⁴`. So no uniform `H² ≤ Ch⁶` can hold on the
degree-capped class. Measured order on that class: `3.94`, against the `6` the law would
need.

This is a counterexample, so nothing is assumed. Note the direction: a local search returns
a value **attained** by a legal probe, hence a *lower* bound on the supremum — which is
exactly the direction that can refute an upper-bound law, and can never certify one.

---

## C1. `hsec` discharged: a positive-mass trajectory *is* a ranking

This was the load-bearing assumption of the flow-to-ranking reduction, so it is given in
full.

**Setup.** State space `V = {0,…,m}^d`, the count vectors. `ty : [m] → [d]` gives each item's
type. `F` is a layered flow whose edge weights vanish off the relation "exactly one
coordinate rises by one".

**Claim.** Every trajectory `t` with `F.trajLaw(t) ≠ 0` that starts at `0` and ends at the
multiplicity vector of `ty` is the layer-count map of an actual permutation of the items.

**Proof, in three steps.**

*(i) Positive mass forces legal steps.* The flow's Markov kernel is `f/x` where `x > 0` and
`0` otherwise, so it vanishes wherever `f` does; hence it is supported on the increment
relation. A trajectory's mass is the product of its kernel factors, so if any factor sat on
a non-increment edge the product would be zero. Induction on the horizon gives: every
consecutive pair of a positive-mass trajectory is an increment.

*(ii) A legal count-path is a type sequence.* At step `i` exactly one coordinate rises; call
it `τ_i`, and set `s = (τ_0,…,τ_{m−1})`. Both `t_i(τ)` and `layerCount(s,i,τ)` start at `0`
and increase by `1` exactly when `τ_i = τ`, so they agree at every `i` by induction. At
`i = m` the multiplicities of `s` are the path's endpoint.

*(iii) Matching multiplicities glue to a permutation.* By hypothesis the endpoint is the
multiplicity vector of `ty`, so for each type `τ` the fibres `{k : s_k = τ}` and
`{j : ty(j) = τ}` have equal cardinality. Choose a bijection between them for each `τ` and
glue:

$$[m]\;\cong\;\coprod_\tau s^{-1}(\tau)\;\cong\;\coprod_\tau ty^{-1}(\tau)\;\cong\;[m].$$

The resulting `ω` satisfies `ty(ω(k)) = s_k`, so its layer counts are exactly `t`. ∎

The section is therefore a *function* with its defining property proved, and the reduction
carries no such hypothesis. The group it symmetrises over is the type-preserving subgroup
`{g : ty ∘ g = ty}`, under which the layer map is invariant — the only property the
symmetrisation needs.

*Lean: `kernel_stepSupported`, `trajLaw_stepC`, `legal_path_realised`,
`realised_multiplicities`, `matchPerm_type`, `hsec_count_states`, `exists_rank_section`,
`countSec_layer`, `rankLayer_smul`, `pathDecomposition_count_states`.*

---

## C2. Below the breakpoint the value strictly exceeds the free value

**Odd `m`.** Every feasible `P` satisfies the per-ranking counting inequality
`2 + 2·lastPos(x) ≤ tot(x)`. Taking expectations and using the band bound
`E_P[lastPos] ≥ (m−1)(1−η)/(2m)`,

$$\mathbb E_P[\mathrm{tot}]\;\ge\;2+\frac{(m-1)(1-\eta)}{m},
\qquad\text{so}\qquad
\frac{\mathbb E_P[\mathrm{tot}]}{D(m-1)}\;\ge\;\frac{2}{D(m-1)}+\frac{1-\eta}{Dm}.$$

The right-hand side exceeds the free value `2/(D(m−1))` for every `η < 1`. The margin is
uniform over the whole band-feasible set, so the infimum inherits it — **no compactness, no
attainment, no window.**

**Even `m`.** Below `η_*(m) = (m−2)/(2(m−1))` the two end budgets alone already exceed the
free value, by the same expectation argument with `r₁ + r_m = (2/D)·big`.

**A second, independent route.** On a compact feasible set a continuous value attains its
minimum, so "no feasible distribution achieves `V_free`" already yields a positive uniform
margin. This shows the manuscript's earlier posture — lower side and attainment proved at
every `m`, yet the strict gap called open — was never coherent: on a compact set those are
the same statement. The domain must be the **band-feasible subset**, not the whole simplex:
on the whole simplex `V_free` is attained, so the hypothesis is unsatisfiable and the
statement vacuous.

**Scope.** The counting inequality and the band bound are *hypotheses* of these theorems.
They are properties of the concrete family, argued in the text and not formalised. So the
statement is: *for any family with those two properties*, the strict gap holds at every `m`
and both parities. Instantiating them at the concrete family is the remaining combinatorial
debt, and the breakpoint should be cited as two-sided **modulo** that instantiation.

*Lean: `O2_strict_odd`, `O2_strict_even`, `strict_gap_of_compact`, `simplex_compact_nonempty`,
`breakpoint_strict_below`, `breakpoint_strict_below_nonvacuous`.*

---

## C3. The cost law in cumulative exploration

`J_true(w*_proxy) = 0` does **not** by itself give `Eτ = Ω(log²(1/α))`: the algorithm may
add linear exploration, the estimated extrema may move, and an approximate oracle may hand
mass to cells the surrogate ignores. The rate turns on exactly those, so the statement is a
law in the cumulative exploration, with `log²` a corollary at one exponent.

Four links. Two were already available: a neighbourhood of the true world on which every
proxy optimum has the same extrema and the same starved support; and the accounting that
telescopes the movable-cell count into `#{bad rounds} + Σ_s(ρ_s + ε_s)`. The other two:

*Bad rounds are boundedly many.* If the per-round probability of leaving the neighbourhood
decays at the inverse-square rate the confidence sequence supplies, then by telescoping
`1/(s+2)² ≤ 1/(s+1) − 1/(s+2)` the total over any horizon is at most `1` — a constant,
uniform in the horizon.

*Leakage is `O(ε)`.* This is A4 above.

Assembling, `N_mov(t) ≤ C_r + 2√t + ε̄t`. The Jensen inversion runs at `a = 1/2` — giving
`Ω(log²(1/α))` — exactly while `ε̄t ≤ 2√t`, that is for `t ≤ (2/ε̄)²`; past that the linear
term takes over and only `Ω(log(1/α))` follows.

**Scope.** The change-of-measure bound `E N_mov(τ) ≥ (2r/d²)·kl(1−α,α)` is an input. The
inverse-square per-round rate is assumed at the rate the confidence sequence supplies, not
instantiated at the algorithm's own confidence set. So this is the *shape* of the cost law
with its exponent identified, not a finished lower bound on `Eτ`.

*Lean: `inv_sq_shift_sum_le`, `expected_bad_rounds_bounded`, `offsupport_mass_le`,
`cumulative_exploration_bound`, `sqrt_dominates_until`.*

---

## C4. The rate at `Γ − η`, and the one thing that blocks `1/Γ`

For each `0 < η < Γ`: a per-round increment of at least `Γ − cε` accumulates at that rate;
the expected-stopping bound holds for *any* non-negative budget `b`, so the threshold's
extra terms (the `½Σ_e log(1+N_e/a)` penalty, estimation, oracle, tracking) go inside `b`
rather than being dropped; with `b = log(1/α) + s(α)` and `s(α) = o(log(1/α))` the ratio is
eventually within `ε` of `1/(Γ−η)`; and `1/(Γ−η) → 1/Γ` as `η ↓ 0`.

**The logical caution.** A bracket of width `ε` gives `0 ≤ Γ − J(w) ≤ ε`. It does **not**
give `Γ − J(w) ≥ ε`: the design may be exactly optimal with all the slack in a loose upper
certificate. So a positive gap does not show the learner is slower — only that the rate one
can *certify* is weaker. Statements here are about the certifiable bound, not the algorithm.

*Lean: `increment_deficit_gives_eta`, `expected_stopping_bound_general`, `rate_limsup_eta`,
`eta_to_zero`, `rate_floor_of_eps_floor`.*

---

## What is not proved anywhere in this corpus

1. **A — the observation-model bridge.** Centring puts the world in the class where energy
   is the Gaussian KL, but the alternatives are still defined by ranges and by the frozen
   contrast, not by the observation model's own alternative class.
2. **A — the learner.** The rate bounds are not attached to the implemented algorithm; the
   per-step confidence guarantee is not instantiated at its own confidence set.
3. **B — the transcript.** The per-query bound is not carried to a continuous adaptive
   randomised transcript. The chain rule is proved only for a finite alphabet.
4. **B — the partition.** `∼_s` is posited on the world index, not derived from the query
   model, so the two orders are not sample complexities.
5. **C — the instantiation.** The counting inequality and band bound of C2 are hypotheses,
   not proved for the concrete family.
6. **C — robustness.** Only a floor is proved. The collapse scale is not located, and an
   adversarial search gives an upper bound on the worst case, so failing to find a worse
   perturbation is not evidence of robustness.
