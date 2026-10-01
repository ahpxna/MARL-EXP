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

## A5. The centred construction: the frozen game exactly, and starvation from one bound

A4 buys starvation with a hypothesis (`AnchorMonotone`, then homogeneity). On the *centred*
world it comes free, because the surrogate's game has a closed form.

**Setup.** Cells are `4 + 2r`: arm `A`'s two extrema, arm `B`'s two extrema, and `r` pairs
of middle cells. Put

$$\theta_A=(-\tfrac12,+\tfrac12),\qquad \theta_B=(-\tfrac18,+\tfrac18),\qquad
\theta_{\text{middle}}=0 .$$

Both arms sum to zero, so the world lies in the centred class where the per-cell Gaussian KL
*is* the squared gap and `energy` is the information. Variances are `1` on the four extrema
and `M` on the middles. The frozen contrast starts at margin
`g = range(A) − range(B) = 1 − 1/4 = 3/4`. Write `a(w)` for the mass on the four extrema.

**Claim 1 (the surrogate's game, exactly).** For every `M > 0`, `Γ_frozen = g²/32 = 9/512`.

**Proof.** *Upper.* Shift the four extrema by `(+g/4, −g/4, −g/4, +g/4)`. That closes the
contrast exactly, keeps both arms centred, and leaves the middles untouched, so it is a
frozen alternative; each of the four moves costs `(g/4)²` at unit variance against weight
`w_e`, giving energy `(g²/32)·a(w)`. An infimum is below any one point, so
`J_frozen(w) ≤ (g²/32)a(w)`, and `a(w) ≤ 1` for an allocation. *Lower.* At the
uniform-extrema design `w = (¼,¼,¼,¼,0,…)` the energy of any `λ` is
`(Σ_{i<4}(λ_i−θ_i)²)/8`, and a four-term Cauchy–Schwarz bounds that below by `g²/4/8` on
the constraint set. The two sides meet. ∎

**Claim 2 (starvation, from the upper bound alone).** If `J_frozen(w) ≥ 9/512` then
`a(w) = 1`, so `w` puts **exactly zero** mass on all `2r` middle cells. If `w` is only
within `ε`, the middle mass is at most `(512/9)ε`.

**Proof.** `9/512 ≤ J_frozen(w) ≤ (9/512)a(w)` forces `a(w) ≥ 1`, hence `= 1`; the middle
mass is `1 − a(w)`. For the `ε` version, `9/512 − ε ≤ (9/512)a(w)` gives
`1 − a(w) ≤ (512/9)ε`. ∎

No monotonicity modulus and no homogeneity hypothesis appears. That is the whole point of
centring the construction.

**Claim 3 (the true game is cheap here too, and not free).**

$$\frac{9}{128(4+2rM)}\;\le\;\Gamma_{\rm true}\;\le\;\frac1{8Mr},
\qquad\text{hence}\qquad
\frac4{4+2rM}\;\le\;\frac{\Gamma_{\rm true}}{\Gamma_{\rm frozen}}\;\le\;\frac{64}{9rM}.$$

**Proof of the upper bound.** Take the closed true-alternative set
`{λ : range_A(λ) ≤ range_B(λ)}` — the worlds where `A` is no longer the answer. Moving one
pair `j` to `(+d, −d)` leaves arm `A` at range `1` and sends arm `B` to range `≥ 2d`, so
`d = ½` already lands in the set. Only the two moved cells contribute, both at variance `M`,
so the energy is exactly `pairWeight(w,j)·d²/(2M) = pairWeight(w,j)/(8M)`. The `r` pair
weights are disjoint and sum to at most `1`, so some pair carries at most `1/r`; that pair's
alternative costs at most `1/(8Mr)`. ∎

**Proof of the lower bound.** A lower bound needs one design that is hard for *every*
alternative. Take weight proportional to variance, `w_e = σ_e²/(4+2rM)` — an allocation,
since the variances total `4·1 + 2r·M`. There the energy collapses to the plain squared
distance,

$$I_w(\theta,\lambda)=\frac{\sum_e(\lambda_e-\theta_e)^2}{2(4+2rM)} .$$

Let `λ` reverse the decision and let `p, q` be the extremes of `λ` over arm `B`'s cells, so
`range_B(λ) = λ_p − λ_q`. Writing `δ = λ − θ` and using `range_A(θ) = 1`,
`θ_p − θ_q ≤ 1/4`:

$$1+\delta_1-\delta_0\;\le\;\mathrm{range}_A(\lambda)\;\le\;\mathrm{range}_B(\lambda)\;\le\;\tfrac14+\delta_p-\delta_q
\quad\Longrightarrow\quad
\tfrac34\;\le\;\delta_0-\delta_1+\delta_p-\delta_q .$$

The four cells are distinct (arm `B`'s cells are none of arm `A`'s), so Cauchy–Schwarz on
them gives `Σ_e δ_e² ≥ (3/4)²/4 = 9/64`, and the energy is at least
`(9/64)/(2(4+2rM)) = 9/(128(4+2rM))`. If `p = q` the `B`-range is zero, the contrast lives on
arm `A` alone, and two squares give `9/32`, which is larger. Taking the supremum over
designs — one design suffices for a lower bound — and dividing by Claim 1 gives the ratio. ∎

Note where the `3/4` comes from: arm `A`'s range is `1` and arm `B`'s is `1/4`, so the
margin is `g = 3/4`, the same `g` that sets `Γ_frozen = g²/32`. The two sides of the
separation are driven by the same number.

**Claim 4 (the consequence — this is the link that matters).** At any `w` attaining the
surrogate's optimum, `J_true(w) = 0` exactly. At any `w` within `ε` of it,

$$J_{\rm true}(w)\;\le\;\frac{64\,\varepsilon}{9Mr} .$$

**Proof.** Claim 2 gives middle mass `0`, hence every pair weight `0`, hence by the identity
in Claim 3 zero energy against every pair alternative; the value is non-negative, so it is
zero. For the `ε` version the middle mass is `≤ (512/9)ε`, so the lightest pair carries at
most `(512/9)ε/r` and its alternative costs at most `(512/9)ε/(8Mr) = 64ε/(9Mr)`. ∎

**Why Claim 4 and not Claim 1 is the contribution.** Two different game *values* do not make
the surrogate harmful: an objective off by a constant still picks the right optimiser. Claim
4 says the surrogate's optimiser collects **no** information about the true decision, and —
the part a sequential argument actually needs — that an *approximate* optimiser, which is
what a learner running on the surrogate has, is still starved, at `ε` times the full
separation factor. The leak vanishes with the learner's own suboptimality.

**Scope.** One world, one variance profile, and the alternative sets taken closed (which is
what the closure-exchange theorem licenses) — and that the closed set is not carrying the
argument is proved rather than asserted: for every `δ > 0` the shift by `½+δ` is a
*strictly* alternative world lying in `Θ₀`, so the bound is approached from inside. Both
games are infima over subsets of the **same** `Θ₀`; since restricting an infimum *raises*
it, the unrestricted bounds do not transfer for free, and they transfer here only because
both witnesses are themselves centred. The step from `J_true(w) = 0` to a *sample
complexity* separation is **not** here: that needs the cumulative-exploration law (C3), whose
count bound remains an input. Satisfiability is proved, not assumed — the uniform-extrema
design attains `9/512` and starves the pairs, so Claim 4's hypotheses are met somewhere.

*Lean: `thetaC_centred`, `frozen_margin`, `energy_lamStar`, `frozenValueC_le`,
`frozenGameC_eq`, `starvation_at_optimum`, `near_optimal_starvation`,
`pairShiftC_mem_trueAlt`, `energy_pairShiftC`, `trueGameC_le`, `centred_ratio_le`,
`starved_trueValueC_zero`, `frozen_optimum_true_value_zero`,
`near_optimal_trueValueC_le`, `centred_starvation_witness` — `LeanPaperACentredV1`.*

---

## A6. The repair frontier: what it costs at the surrogate to buy back true information

A5 is a negative result — the surrogate's optimum is uninformative. The operational question
is the exchange rate. Let

$$\mathcal F(\beta)=\sup\{\,J_{\rm true}(w)\;:\;w\text{ an allocation},\ J_{\rm fr}(w)\ge(1-\beta)\Gamma_{\rm fr}\,\}$$

be the most true information obtainable while keeping a `(1−β)` fraction of the surrogate's
value. One structural fact drives both sides.

**Lemma (concavity).** Each game's value is an infimum of functions **linear** in the
design, hence concave in the design.

**Proof.** `energy(w, λ)` is linear in `w` for fixed `λ` — the weights enter once,
multiplicatively. For a mixture `w_t = (1−t)w₁ + tw₂` and any `λ`,
`energy(w_t,λ) = (1−t)energy(w₁,λ) + t·energy(w₂,λ) ≥ (1−t)J(w₁) + tJ(w₂)`, since each
infimum is below its own point. Taking the infimum over `λ` on the left preserves it. ∎

**Claim (upper).** `F(β) ≤ β/(8rM)`.

**Proof.** Put `ξ = βΓ_fr = 9β/512` into the near-optimal starvation bound
`J_true ≤ 64ξ/(9rM)`: it reads `64·(9β/512)/(9rM) = β/(8rM)`. ∎

**Claim (lower).** `F(β) ≥ 9β/(128(4+2rM))`, witnessed explicitly.

**Proof.** Mix the surrogate's optimum with the design certifying the true lower bound,

$$w_\beta=(1-\beta)\,w_{\rm unif}+\beta\,w_{\rm cert},$$

a legal allocation. Concavity and `J_fr ≥ 0` give
`J_fr(w_β) ≥ (1−β)J_fr(w_unif) ≥ (1−β)Γ_fr`, so `w_β` is feasible; concavity and
`J_true ≥ 0` give `J_true(w_β) ≥ βJ_true(w_cert) ≥ 9β/(128(4+2rM))`. ∎

Together, for `rM ≥ 1`,

$$\frac{9\beta}{128(4+2rM)}\;\le\;\mathcal F(\beta)\;\le\;\frac{\beta}{8rM},
\qquad\text{so}\qquad \mathcal F(\beta)=\Theta\!\Big(\frac{\beta}{rM}\Big).$$

At `β = 0` the upper bound is `0`, so the frontier **collapses to the starvation theorem**:
the two results are one family, and no sacrifice buys nothing.

**Why this is the contribution and mixing designs is not.** Convex-combining two designs is
routine. What is not routine is that on this problem the trade-off is pinned from *both*
sides at the *same* order, and that the order is the separation factor itself: the price of
repair is linear in the sacrifice and carries the same `1/(rM)` the mispricing does. The
practitioner's reading is direct — giving up a `β` fraction of the surrogate's value buys
back at most a `β` fraction of the true game's ceiling, and a `β` fraction is actually
attainable.

**Scope.** One construction, one variance profile, both games on the same `Θ₀`. The
statement is about information at a design; it is not a sample-complexity statement.

*Lean: `mixW_isAlloc`, `energy_mixW`, `value_concave`, `frontier_upper`, `frontier_lower`,
`frontier_two_sided`, `frontier_at_zero` — `LeanPaperAFrontierV1`.*

---

## A7. The construction is an observation model, not only a parameter class

The games of A5–A6 are infima of `energy` over subsets of a parameter class. That is not yet
compression: the class, the response and the observation law in the *information* theorem
have to be the ones in the *compression* theorem. Showing the true world is realisable does
not do it.

**Setup.** Two arms: `A` with two cells, `B` with `2+2r`. The response is additive,
`F_λ(a,b) = λ_A(a) + λ_B(b)`, against the uniform product reference. Retaining an arm means
explaining the response by that arm's own marginal and paying the oscillation of the rest.

**Claim 1 (why `Θ₀` is the class, stated as an equivalence).** The marginal of the additive
response is `Q_A^λ(a) = λ_A(a) + mean_b(λ_B)`, so

$$Q_A^\lambda=\lambda_A\ \text{ for every }a
\iff
\textstyle\sum_b\lambda_B(b)=0,$$

and symmetrically for `B`. Hence `λ ∈ Θ₀` **iff** both marginals recover their coordinates.
Centring is not a convenience attached to the construction; it is exactly the condition
under which the uniform-product marginal *is* the coordinate.

**Claim 2 (the loss is a range).** On `Θ₀` the residual after retaining `A` is literally
`λ_B` — it does not depend on `a` — so its oscillation over the grid is arm `B`'s range and

$$L_\lambda(\{A\})=\tfrac12\mathrm{range}(\lambda_B),\qquad
L_\lambda(\{B\})=\tfrac12\mathrm{range}(\lambda_A).$$

**Claim 3 (the decision, with its tolerance and its sign).** Retaining `A` is `ε`-unsafe iff
`L_λ({A}) > L_λ({B}) + ε`, i.e.

$$\boxed{\ \mathrm{range}(\lambda_B)>\mathrm{range}(\lambda_A)+2\varepsilon.\ }$$

The inequality is **strict**, and at `ε = 0` it is `range(λ_A) < range(λ_B)`. The closed set
`{range(λ_A) ≤ range(λ_B)}` that the games are solved over therefore **strictly contains**
the unsafe set: a tie lies in the closed set and is *not* unsafe. That gap is what
`closure_exchange` has to license, and it is recorded here rather than absorbed.

**Scope.** What is proved is the equivalence between the class, the marginals, the losses and
the range condition. What is *not* yet proved is that the games' infima over the closed set
equal the infima over the strict unsafe set; the corpus has strict witnesses inside `Θ₀`
(`pairShiftC_strict_alt`), which is the ingredient, not the conclusion.

*Lean: `sum_tblA`, `sum_tblB`, `margA_eq`, `margA_eq_tblA_iff`, `margB_eq_tblB_iff`,
`centred_iff_marginals`, `residA_eq`, `exists_bCell`, `rangeB_eq_osc`, `lossRetainA_eq`,
`unsafeA_iff_range_gap`, `unsafeA_zero_iff`, `unsafe_subset_closed` —
`LeanPaperACentredModelV1`.*

---

## A8. The alternative set is exactly a union of polyhedra

An oracle that solves the inner problem region by region is an oracle for *compression* only
if the decomposition is an **equality** with the set of worlds at which the retained answer
is wrong — both inclusions, derived from the loss. A7 supplies the missing half.

**Claim.** For every tolerance `ε` and every centred `λ`,

$$\text{retaining }A\text{ is }\varepsilon\text{-unsafe}
\iff
\exists\,p,q\in B:\quad
\lambda_1-\lambda_0+2\varepsilon<\lambda_p-\lambda_q
\ \text{ and }\
\lambda_0-\lambda_1+2\varepsilon<\lambda_p-\lambda_q .$$

**Proof.** By A7, unsafe means `range(λ_B) > range(λ_A) + 2ε`. That range condition is
equivalent to an existential over pairs: forward, take the cells realising `B`'s supremum
and infimum, whose difference *is* the range; backward, any pair's gap is at most the range,
so a pair already exceeding forces the range to exceed. Each pair's condition then splits
into two linear inequalities because `|x| < y` is `x < y` together with `−x < y`. ∎

**The absolute value is where a cover goes wrong, and this is not hypothetical.** Building
the numerical certificate for the same set, I first covered it by treating the two
inequalities as *alternatives* — one half-space per sign. That cover contains the true world
itself: take `p,q` two middle cells, both at `0`, and the sign pointing away from arm `A`'s
gap. The certificate then collapses to zero and the rule never stops. Simultaneous, not
alternative.

**Non-vacuity.** Each polyhedron is inhabited: a pair shift by `d > 1/2` lands in its own
pair's polyhedron.

**Scope.** This is the covering half of the oracle. Per-region closure validity as a general
statement, and the outer certificate bounding every design, are not here.

*Lean: `range_gap_iff_exists_pair`, `pair_region_linear`, `unsafe_iff_union_of_polyhedra`,
`polyhedron_nonvacuous` — `LeanPaperARegionV1`.*

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

## B2b. The observation-order partition, derived rather than posited

`IndistAt s θ λ := θ=λ ∨ (s≤θ ∧ s≤λ)` is a definition on the world *index*. Every
consequence drawn from it is conditional on that partition being what an observer actually
faces. Here it is derived, for an explicit family, in both directions.

**Setup.** World `i` is the one whose first non-vanishing moment sits at order `i+1`:
`m_k(i) = 1` if `k = i+1`, else `0`. A *query of order at most `s`* is a linear functional
supported on moments `1..s`: a vector `q` with `q_0 = 0` and `q_k = 0` for `k > s`, read
against the world's moments.

**Claim 1.** Moments agreeing on orders `1..s` is exactly the index condition.

**Proof.** If `θ = λ` there is nothing to check; if `s ≤ θ` and `s ≤ λ` then for `1 ≤ k ≤ s`
neither `k = θ+1` nor `k = λ+1` can hold, so both moments are `0`. Conversely, suppose the
moments agree and `θ ≠ λ`. If `θ < s` then `k = θ+1` satisfies `1 ≤ k ≤ s`, and there
`m_k(θ) = 1` while `m_k(λ) = 0` because `θ+1 ≠ λ+1` — contradicting agreement. So `s ≤ θ`,
and symmetrically `s ≤ λ`. ∎

**Claim 2.** A query of order `≤ s` takes the same value at two worlds of the same class,
and for **every** pair outside the class some query of order `≤ s` separates them.

**Proof.** The first half is Claim 1 termwise: the summand vanishes at `k = 0` and at
`k > s` because `q` does, and elsewhere the two moments agree. For the second, `θ ≠ λ` and
at least one of them, say `θ`, has `θ < s`. Take `q` the indicator at order `θ+1`, which is
of order `≤ s`. Its value is `m_{θ+1}(·)`, namely `1` at `θ` and `0` at `λ`. ∎

Together: `IndistAt s θ λ` **iff** no query of order at most `s` separates `θ` from `λ`.
That is the statement the geometry section needs in place of a definition.

**Scope, and it is not a detail.** The moment vectors are *prescribed*; no distribution
realising them is constructed here. Joining this to the moment-matching laws is the
remaining half of "one family, with `F_θ`, support, loss and observation law". Nor does this
touch the safe-set family used by the obstruction experiment, whose safe sets are equal
within `u` and disjoint across `u` — a different family from the intersecting one the
geometry theorems are about.

*Lean: `momentOf_self`, `agreeUpTo_iff_indistAt`, `query_blind_of_indistAt`,
`exists_query_separating`, `indistAt_iff_no_separating_query` — `LeanPaperBIndistV1`.*

---

## B2c. Attainment by characteristic functions — a derivation, **not yet Lean-checked**

Everything else in this file is proved in Lean. This section is not: it is a proof sketch,
verified numerically to machine precision, recorded so the formalisation has a target. It is
labelled that way deliberately — it must not be cited as proved.

**Why bother.** The obvious estimator for a degree-`r` signal is `Y^{r+1}`, whose variance
is enormous and whose concentration argument is correspondingly delicate. A characteristic
function avoids it entirely: `cos(t₀Y)` is bounded by `1`, so Hoeffding applies directly.

**Setup.** `Z` uniform on `{±1}^{3+r}`, noise `ξ ~ N(0,σ²)`,

$$F_{u,v}(z)=3uz_1-2z_2-2z_3+v\prod_{\ell=4}^{r+3}z_\ell,\qquad
Y=F_{u,v}(Z)+h\,g(Z)+\xi .$$

Take the tail query `g(z) = (1/r)Σ_{ℓ≥4} z_ℓ`. Write `φ_v(t) = E[e^{itY}]`.

**Claim.**

$$\varphi_{+}(t)-\varphi_{-}(t)
=2i\sin(t)\cos(3t)\cos^{2}(2t)\,e^{-\sigma^{2}t^{2}/2}\bigl(i\sin(th/r)\bigr)^{r}.$$

**Proof.** The coordinates are independent, so `φ_v` factorises. For `z ∈ {±1}`,
`E[e^{iaz}] = cos a` and `E[z e^{iaz}] = i sin a`. The `z₁` factor gives `cos(3ut) = cos(3t)`
(cosine is even), and `z₂, z₃` give `cos(2t)` each; the noise gives `e^{-σ²t²/2}`. For the
tail block, write `P = ∏_{ℓ≥4} z_ℓ` and `S = Σ_{ℓ≥4} z_ℓ`. Since `P² = 1`,

$$e^{itvP}=\cos(t)+iv\sin(t)P ,$$

so

$$E\bigl[e^{i(tvP+(th/r)S)}\bigr]
=\cos(t)\prod_{\ell}E\bigl[e^{i(th/r)z_\ell}\bigr]
+iv\sin(t)\prod_{\ell}E\bigl[z_\ell e^{i(th/r)z_\ell}\bigr]
=\cos t\,\cos^{r}\!\tfrac{th}{r}+iv\sin t\,\bigl(i\sin\tfrac{th}{r}\bigr)^{r}.$$

Only the second term carries `v`, and subtracting the two values of `v` doubles it. ∎

**What it buys.** At a fixed small `t₀` avoiding the zeros of `sin t`, `cos 3t`, `cos 2t`,
the magnitude is `≍ h^r`, because `sin(t₀h/r) ≍ t₀h/r`. Taking the real or imaginary part
according to the parity of `r` gives a **bounded** statistic `f(Y) = cos(t₀Y)` or
`sin(t₀Y)`, `|f| ≤ 1`, whose two means differ by `≍ h^r`. Hoeffding then gives a genuine
test at

$$N\;\ge\;C_r\,h^{-2r}\log(1/\delta),$$

and the same argument on the head query `g(z)=z₁`, whose difference is
`-2\sin(3t)\sin(ht)\cos^{2}(2t)\cos(t)e^{-σ²t²/2} ≍ h`, needs only `N ≳ h^{-2}\log(1/δ)`.

**Numerical check of this section** (not a proof, a guard against algebra slips): the
identity matches a brute-force sum over the cube to `|lhs−rhs| ≤ 1.3e-16` at
`r ∈ {2,3,4}`, and the fitted order in `h` is `1.99983`, `2.99989`, `3.99991` against the
claimed `r`, with the head query at `0.99952` against `1`.

**The cube half is now proved in Lean**, and for every `r` rather than at checked values:
`cube_sum` and `cube_difference` in `LeanPaperBCubeV1`, resting on `exp(aP) = cosh a + P sinh a`
from `P² = 1` and a coordinate-by-coordinate factorisation. What remains is the Gaussian
factor, the choice of `t₀` away from the zeros, the parity split when taking a real part, the
bounded-statistic concentration and the decoder's budget — none of which is here.

---

## B2d. The safe-observation-order law

How deep must an observer resolve worlds before every class it can still confuse admits one
answer safe for all of them? This is the geometry–query link, and it is a theorem.

**Setup.** Finitely many worlds; for each a finite set of safe answers; and a *resolving
order* `sep(θ,λ)`, the first order at which some admissible query tells them apart. A set is
**together at level `s`** when no pair in it is resolved by order `s` — it is still one class
for an order-`s` observer — and **unsafe** when its worlds share no safe answer. Write
`SafeAt s` for: every set together at level `s` has a common safe answer.

**Claim.** `SafeAt s` **iff** every unsafe set already contains a pair resolved by order `s`.

**Proof.** If some unsafe `H` had all pairs unresolved at `s`, it would be together at `s`
and unsafe, contradicting `SafeAt s`. Conversely if `H` is together at `s` and unsafe, the
hypothesis hands a pair with `sep ≤ s`, contradicting togetherness. ∎

Equivalently `s_safe = max over unsafe H of min over pairs of H of sep`.

**Why "all unsafe sets", not "minimal" ones.** Unsafety is upward closed — a superset shares
no answer either — and enlarging a set can only lower its pairwise minimum. So the maximum
is attained on minimal unsafe sets anyway, and quantifying over all of them removes the need
to define minimality. The minimal-obstruction reading is the corollary, and it is the form
to use in prose.

**Two edge cases the law must name.** If no set is unsafe there is a globally safe answer and
order `0` suffices — the decision costs no observation. And `SafeAt` is monotone in `s`.

**The overlapping construction, geometry half.** With `safe(w) = everything but w` and at
least three worlds: every pair of safe sets meets, the total intersection is empty, and the
whole world set is the **only** unsafe set. The law then collapses to

$$\mathrm{SafeAt}(s)\iff \min_{\theta,\lambda}\mathrm{sep}(\theta,\lambda)\le s,$$

the simplest instance it has.

**Scope, and it is the substance.** `sep` is an **input**. Deriving it from the densities of
an actual observation model — the coefficient of `h^k` in the expansion, uniformly over the
admissible query class — is Paper B's central obligation and is not done here. The law says
what follows *from* a resolving-order table, not that the model has one. Likewise the parity
mask showing query `j` resolves world `j` at order `j` is the construction's other half and
is unproved. And at this family a query-free guess already achieves worst-case error `1/m`,
so a positive sample-complexity lower bound must restrict `δ` below that floor.

*Lean: `safeAt_iff`, `unsafe_mono`, `safeAt_mono`, `safeAt_zero_of_no_unsafe`,
`coSafe_pairwise_meet`, `coSafe_univ_unsafe`, `coSafe_proper_safe`, `coSafe_safeAt_iff` —
`LeanPaperBSafeOrderV1`.*

---

## B2e. The decoder, and the uniformity a class test needs

An upper bound needs a *decoder*, not a collection of pairwise error bounds. Two things have
to be right, and the second is the one that is easy to skip.

**A test between two classes is not a test between two representatives.** What must hold is

$$\sup_{\theta\in C}\Pr_\theta(\text{test says }D)\le\delta',\qquad
\sup_{\lambda\in D}\Pr_\lambda(\text{test says }C)\le\delta',$$

uniformly over each class. Choosing one world from each class and testing those two says
nothing about the rest.

**Claim (uniform composite test).** Let `m(θ)` be a statistic's mean at world `θ`. If
`|m(θ) − μ_C| ≤ R` for **every** `θ ∈ C`, `|m(λ) − μ_D| ≤ R` for every `λ ∈ D`, and
`μ_C + 2R + 2·tol < μ_D`, then the threshold at `(μ_C+μ_D)/2` puts every world of `C` strictly
below and every world of `D` strictly above, whenever the empirical mean is within `tol` of
its own world's mean.

**Proof.** For `θ ∈ C`: `x ≤ m(θ) + tol ≤ μ_C + R + tol < μ_D − R − tol ≤ (μ_C+μ_D)/2`, the
middle step being the separation hypothesis. Symmetrically for `D`. ∎

The only probabilistic input is per-world concentration through `tol`; the class uniformity
is carried by `R`, not by a representative.

**The output has to exist.** After elimination the survivors are still together at level `s`,
and `SafeAt s` is exactly the statement that such a set shares a safe answer — so the decoder
has something to return, and since the truth is among the survivors, what it returns is safe
at the truth. This is the step a pairwise-error accounting does not give: correctness of the
*output*, not of the tests.

**Scope.** Not here: the concentration itself (a bounded statistic and Hoeffding), the queries
realising the separation at each order, and the **total** sample budget — the number of
distinct queries, the number of tests, and the per-test sample count are three different
quantities and must not be reported as one.

*Lean: `composite_test_low`, `composite_test_high`, `composite_test_separates`,
`separation_of_gap`, `decoder_output_exists`, `decoder_is_safe_at_truth` —
`LeanPaperBDecoderV1`.*

---

## B2f. From an envelope to a KL bound — the step that must not be skipped

The lower-bound chain needs `KL(P_θ^q ‖ P_λ^q) ≤ C h^{2s}` uniformly over the query class.
The corpus's envelope work bounds `∫(p−q)²/ℓ` for a floor `ℓ`. **A Hellinger bound does not
give a KL bound, and neither does the envelope by itself.** One extra inequality is needed,
and it is elementary.

**Claim (pointwise).** For `p ≥ 0` and `q > 0`,

$$p\log\frac pq\;\le\;\frac{(p-q)^2}{q}+(p-q).$$

**Proof.** `log x ≤ x − 1` at `x = p/q` gives `p log(p/q) ≤ p(p/q) − p`. And
`(p−q)²/q + (p−q) = [(p−q)² + q(p−q)]/q = (p−q)p/q = p(p/q) − p` — an *identity*, so nothing
is given away a second time. ∎

**Claim (the floor).** If `0 < ℓ ≤ q` then `(p−q)²/q ≤ (p−q)²/ℓ`.

**Claim (integrated).** For two densities against a common measure, the linear term
integrates to `∫p − ∫q = 0`, so

$$\mathrm{KL}(p\|q)\;\le\;\int\frac{(p-q)^2}{\ell}.$$

**Why Hellinger cannot substitute.** The chi-squared integrand exceeds the Hellinger one by
the factor `(√p+√q)²/q`, which is unbounded as `p/q` grows. So no inequality runs from a
Hellinger integral to a KL integral without a further hypothesis — this is recorded as a
lemma rather than a remark.

**Scope.** The pointwise steps are unconditional. The integral form carries its
integrability hypotheses explicitly — the KL integrand, the envelope, the difference, and
`∫(p−q) = 0` — because that is where the work sits for Gaussian mixtures on the line.
Instantiating them at the actual observation model, **uniformly over the admissible query
class**, is Paper B's obligation and is not done here.

*Lean: `kl_integrand_le`, `chi_integrand_mono`, `kl_integrand_le_floor`, `kl_le_envelope`,
`hellinger_integrand_le_chi` — `LeanPaperBKLV1`.*

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

## C0. The extra ranking the even construction needs

The even-`m` upper bound mixes the `m−1` insertion rankings with one more,

$$(-3,\ +1,\ -1,\ +1,\ -1,\ \dots,\ +1,\ -1,\ +3),$$

whose defining property is that its excess is **exactly `2` at every budget** — a flat `2`
across `k = 1,…,m−1`, not a single spike. That is what makes the mixture's per-budget
expectation `2/m + 2/m = 4/m` rather than budget-dependent.

**Claim.** For `1 ≤ k ≤ m−1`, the prefix sum is `−3` when `k` is odd and `−2` when `k` is
even; hence the excess, which subtracts `k mod 2`, is `2` at every budget.

**Proof.** Induction on `k`. At `k=1` the prefix is the first weight, `−3`, and `1` is odd.
For the step, the weight at position `n` is `+1` when `n` is odd and `−1` when `n` is even
(positions strictly between the ends), so the prefix alternates: from `−3` at odd `n` add
`+1`... — precisely, if `n` is even the prefix at `n` is `−2` and the weight at `n` is `−1`,
giving `−3` at the odd budget `n+1`; if `n` is odd the prefix is `−3` and the weight `+1`,
giving `−2` at the even budget `n+1`. ∎

**The total is a corollary of the same pattern, not a separate count.** At `k = m` with `m`
even, `m−1` is odd, so the prefix there is `−3`; the final weight is `+3` and closes it to
zero. That is exactly what membership in the even family requires, so no counting of `+1`s
against `−1`s is needed.

**Scope.** This is the extra ranking, not the construction. The mixture itself — equal mix
of the `m` rankings, then the sign flip at ratio `1/2`, then uniform relabelling within each
weight type — its per-item retained marginals, and the resulting bound
`V_m(0) ≤ 4/(m(m+4))`, are not here. Verified numerically at `m = 4,6,8,10,12` before
formalising.

*Lean: `flatEven`, `flatEven_prefix`, `flatEven_excess`, `flatEven_total`,
`flatEven_weights` — `LeanPaperCEvenV1`.*

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

**Retraction, added after the fact.** Every step above is still correct, and the section is
still a function with its defining property proved. What is wrong is the last sentence of the
last paragraph: the reduction `pathDecomposition_count_states` is stated over `CountFeasible`,
and **that class is empty** — §C25. A conditional with unsatisfiable hypotheses proves
nothing, so the reduction is withdrawn as a statement about flows, together with
`pathDecomposition_at_count_states` and everything in `LeanPaperCPathV1` stated over the same
domain. Discharging `hsec` and having a non-empty feasible class are two separate debts; only
the first was paid here. The second is paid in §C25 on the repaired domain.

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

## C5. The band hypothesis is the band, added up

(O2) was proved *for any family with two properties*, and the aggregate band bound was not
instantiated. It is not an extra assumption — but getting it right needs the constraint the
paper actually imposes, and an earlier version of this section got two things wrong.

**The constraint is on retained prefixes, not positions.** Paper C imposes
`|Pr(i ∈ prefix_k) − k/m| ≤ η/m` for every item and budget. That is not equivalent to a
position band of the same width once `η > 0`, so the endpoint probabilities must be
*derived*:

$$\Pr(\pi_1=i)=\Pr(i\in\mathrm{prefix}_1)\ \ge\ \frac{1-\eta}{m},\qquad
\Pr(\pi_m=i)=1-\Pr(i\in\mathrm{prefix}_{m-1})\ \ge\ \frac{1-\eta}{m},$$

the first from the band's lower side at `k=1`, the second from its **upper** side at
`k=m−1`: `1 − ((m−1)/m + η/m) = (1−η)/m`. A one-sided band would not give the second.

**The odd side uses exclusivity, and it is true there.** `lastPos` counts whether the last
item is positive. The odd family has `(m−1)/2` items of positive weight, only one of them
can be last, and each is last with probability at least `(1−η)/m`. Summing over them and
exchanging the two finite sums gives `(m−1)(1−η)/(2m)`. ∎

**The even side does not, and the earlier claim that it did was false.** `big(π)` counts
heavy items at the two ends,

$$\mathrm{big}(\pi)=\sum_{i\in\{-3,+3\}}\bigl(\mathbf 1\{\pi_1=i\}+\mathbf 1\{\pi_m=i\}\bigr),$$

and **both** heavy items can sit at the two ends, so `big` reaches `2` and the four
indicators are not mutually exclusive. No disjointness is needed: the display is an
identity, expectation is additive, and each of the four terms is at least `(1−η)/m`, so
`E[big] ≥ 4(1−η)/m`. ∎

**Scope.** Exclusivity on the odd side enters as `occ i x = [i = last(x)]` — exactly one
item occupies a position, which is what a ranking is. The counts `(m−1)/2` and `2` are
properties of the family's weight multiset. Satisfiability is proved rather than assumed:
under the uniform law every exposure is exactly `1/m`, clearing `(1−η)/m` for every `η ≥ 0`.
Still a hypothesis on the even side: the identity `r₁+r_m = (2/D)·big`.

*Lean: `first_position_lower`, `last_position_lower`, `band_sum_lower`, `band_aggregate`,
`exclusive_sum_le`, `hband_odd_of_prefix_band`, `hband_even_of_endpoint_band`,
`O2_odd_from_prefix_band`, `O2_even_from_endpoint_band`, `uniform_item_band` —
`LeanPaperCBandV1`.*

---

## C6. The A-END chain, joined — and the window head nobody had paid for

Each link of the A-END argument was proved in isolation and nothing joined them, so the
expected-stopping bound that `rate_limsup_eta` consumes was an *input* to the development
rather than an output of it. Joining them exposes a cost that isolation hid.

The inclusion `{τ > t} ⊆ ⋃_{s ∈ [n,t)} good(s)ᶜ` needs the threshold strictly below
`G·t − 2Γ·n − C` at the window `n = ⌈√t⌉`. So the head of the window has to be paid for,
and at budget `b` the crossing time is **not** `b/G + O(1)` but `b/G + O(√b)`. The payment
is made explicit rather than absorbed into an asymptotic: for any `ε ∈ (0,1)`,

$$2\Gamma\sqrt t\ \le\ \varepsilon G t + \frac{\Gamma^{2}}{\varepsilon G},$$

which is `(εG√t − Γ)² ≥ 0` divided by `εG`. The window head therefore costs a factor
`(1−ε)` of the rate and an additive `Γ²/(εG)` of the budget. Collecting the constants,

$$\mathrm{winBudget} = C + 2\Gamma + \frac{\Gamma^{2}}{\varepsilon G} + 14(1-\varepsilon)G,$$

where the last summand is what forces the crossing time past `16` — the smallest `t` at
which the `√t` window is admissible at all. Then `E τ ≤ (b + winBudget)/((1−ε)G) + 19`,
and `rate_limsup_eta` turns that into the rate `1/((1−ε)Γ)`.

**What this does not give.** `ε = 0` is not available inside the argument: the split's
constant `Γ²/(εG)` blows up. So this is the `Γ − η` family again, and
`chain_rate_is_deficient` records that `1/Γ < 1/((1−ε)Γ)` strictly. The `s^{-4}`
confidence step remains a hypothesis, exactly as in C4.

*Lean: `sqrt_head_split`, `window_crossing`, `crossing_past_sixteen`, `chain_tail_bound`,
`expected_stopping_bound_window`, `chain_expected_bound`, `a7_chain_rate`,
`chain_rate_is_deficient` — `LeanPaperA7ChainV1`.*

---

## C7. `hdiff` was unsatisfiable; the two worlds that repair it

`kl_rate_of_mixture` carried the density-difference identification as a hypothesis,

$$p - q = \mathrm{iterDiff}\ q\ \text{shifts},$$

with `q` the same mixture on both sides, and asked separately for `p ≥ 0`. **That pair is
contradictory.** Take one Gaussian component and one shift `s > 0`. Then
`p(y) = q(y) + (q(y−s) − q(y+s))/2`, and at `y = −T` with `T = (s²+4σ²)/(2s)`,

$$\frac{q(T-s)}{q(T)} = \exp\Bigl(\frac{2Ts-s^{2}}{2\sigma^{2}}\Bigr) = e^{2} > 3
\ \ \ \text{while}\ \ \ q(T+s) \le q(T),$$

so `2q(T) + q(T+s) < q(T−s)` and `p(−T) < 0`. The hypotheses hold only at `h = 0`, where
the conclusion is empty. The old composition therefore said nothing wherever it was of
interest.

**The repair is to stop asking one density to be its own difference.** Write `v z` for the
signed shift sum of a sign pattern `z` and `parity z` for the product of its signs, and set

$$Q = 2^{-r}\sum_{z} M(\cdot - v z),\qquad
P = 2^{-r}\sum_{z} \bigl(1 + \mathrm{parity}\,z\bigr)\,M(\cdot - v z).$$

`P` keeps the even patterns at double weight and drops the odd ones; `Q` is the flat
average. Both are non-negative combinations of translates of one base, both carry the same
total mass, and

$$P - Q = 2^{-r}\sum_{z}\mathrm{parity}(z)\,M(\cdot - v z) = \mathrm{iterDiff}\ M\ \text{shifts}$$

by `iterDiff_eq_signSum`. So `hdiff` is an **identity** about the constructed pair, not a
hypothesis about a hoped-for one, and `p ≥ 0` is free.

**Uniformity is then the point, not an afterthought.** `Q` inherits the base's floor on the
shift window (`envLo σ (R+h₀) ≤ Q`, since every centre `c_j + v z` lies within `R + h₀`),
so `hellinger_rate_bound` applies with `ℓ = envLo` and gives

$$\int \frac{(P-Q)^{2}}{\mathrm{envLo}}\ \le\ h^{2r}\Bigl(\frac1r\Bigr)^{2r}\mathrm{klConst}(\sigma,R,h_{0},r),$$

with **no integrability hypothesis at all**, and `klConst` mentions neither the weights, nor
the centres, nor the shift profile. One constant, every admissible query. The KL form needs
two integrability side conditions on the constructed pair, which are properties of that pair
and not modelling assumptions.

**Scope.** Uniform over the class *as the box constraints define it*: centres within `R`,
`Σ_i |h a_i| ≤ h₀`, `Σ_i |a_i| ≤ 1`. That a given observation model's queries induce shifts
inside that box is the modelling step and is not proved.

*Lean: `self_difference_not_a_density`, `worlds_diff`, `worldQ_floor`, `mixDens_floor`,
`chi2_uniform`, `kl_uniform_over_queries` — `LeanPaperBWorldsV1`.*

---

## C8. The change of measure, with no alphabet assumption

`klPath_chain` sums over every length-`n` list of observations, so it needs a finite
observation alphabet, and it says so. The object that carries the argument without that
assumption is the likelihood ratio on the filtration, `L_t = dP|_{F_t}/dQ|_{F_t}`, stated
as an equality of trimmed measures because that is the form the integral lemmas consume.

Four facts, none needing the alphabet to be finite:

1. **Change of measure.** `∫ f dP = ∫ L_t · f dQ` for every `F_t`-measurable `f` — by
   `integral_trim`, the `withDensity` integral formula, and `integral_trim` back.
2. **Consistency.** `∫_A L_{t+1} dQ = ∫_A L_t dQ` for every `A ∈ F_t`, because both sides
   compute `P(A)` — apply (1) at `t` and at `t+1` to the indicator of `A`, legitimate
   since `F_t ⊆ F_{t+1}`.
3. **The tower property.** (2) *is* `L_t = E_Q[L_{t+1} | F_t]`, via the characterisation of
   conditional expectation by set integrals.
4. **Telescoping.** With `L_0 = 1` and each `log L_t` integrable under `P`,
   `E_P log L_n = Σ_{t<n} E_P log(L_{t+1}/L_t)`, hence `≤ n·B` under a per-step bound.

**The policy never appears.** In the list formulation the policy is an argument and its
cancellation is a step of the proof; here it is inside the filtration, so a policy reading
the entire past is already covered. That is a strengthening, not a gap.

**What is not here.** That the transcript law of a concrete adaptive Gaussian policy admits
such an `L_t` — the construction of the filtration and of the density from the policy's
kernels — is not proved.

*Lean: `change_of_measure`, `setIntegral_L_succ`, `condExp_L`, `kl_eq_sum_increments`,
`kl_le_horizon`, `L_zero_of_trivial` — `LeanPaperBChangeV1`.*

---

## C9. The odd family's window sums — and a number the corpus had wrong

The remaining budgets of the odd construction need the circular window sums. Working in
`Fin m` forces the wrap into the addition; working on `ℕ` with `%` puts it into a
`Finset.range` split instead, which is what the formalisation does:

$$W(a,k) = \bigl(P(\min(a+k,m)) - P(a)\bigr) + P(a+k-m),$$

with `P` the ordinary prefix sequence, whose only values are `P₀ = 0`, `P₁ = 3` and, for
`j ≥ 2`, `0` at even `j` and `−1` at odd `j`. Splitting the rotations at the wrap and
peeling the two special indices from each block gives, for `m` odd and `0 < k < m`,

$$\sum_{a<m}|W(a,k)| = \begin{cases} m+4, & k \text{ odd},\\ k+4, & k \text{ even}.\end{cases}$$

The even block's interior is constant `0` and its wrapped part alternates `0, 2, 0, 2, …`,
which is summed by `Σ_{i<2t} P(i+2) = −t`; the odd case is constant `1` throughout both
interiors.

**The baseline is what decides which budget is worst.** Every weight of the family is an
odd integer, so a length-`k` prefix sum has the parity of `k` and the per-budget baseline is
`b_k = k mod 2`. The family's *value* at budget `k` is therefore
`Σ_a|W(a,k)|/m − b_k`, which is

$$\frac{m+4}{m}-1=\frac4m \quad (k \text{ odd}),\qquad \frac{k+4}{m}-0 \quad (k \text{ even}),$$

so the maximum over `0 < k < m` is `(m+3)/m`, attained at `k = m−1` and nowhere else. At the
normaliser `D = m+4` that is `(m+3)/(m(m+4))` — the recorded `V_m(0)` for odd `m`, now
supported by the window sums rather than by one budget.

The cancellation is worth naming because it inverts the ranking of the budgets: the odd
budgets carry the *larger* raw sum (`m+4` against `k+4 ≤ m+3`) and the *smaller* value, since
`b_k = 1` there takes exactly `m/m` away. Reading the raw sums as the value makes the odd
budgets look worst; they are the best. Checked numerically at `m = 5,\dots,15`.

**What is in Lean and what is not.** The sums, the value at each budget, the maximum and its
attainment at `k = m−1` are all theorems (`LeanPaperCValueV1`). So is the side of the
baseline an upper bound needs: `baseline_le_abs_prefix` derives `|S_k| ≥ k mod 2` for *every*
ranking from the existing `prefixSum_parity`, so using `k mod 2` cannot *understate* the
regret — if the true per-budget optimum were larger, the bound would merely be conservative.
What is not proved is attainability: that some ranking meets `k mod 2` at each budget, which
is what would make `b_k` exactly the optimum rather than a valid lower estimate of it.

*Lean: `win_eq`, `preN_pattern`, `preN_alt_sum`, `win_abs_sum_odd`, `win_abs_sum_even`,
`win_abs_sum_odd_gt_even` — `LeanPaperCWindowV1`; `baseline_le_abs_prefix`, `winValue_odd`,
`winValue_even`, `winValue_le`, `winValue_at_last` — `LeanPaperCValueV1`.*

---

## C10. The headline, assembled — and which half is a theorem

The two exponents were proved separately and the headline was left in prose. Assembling it
is what makes visible which half is a theorem.

**Lower, and it is one.** With a per-step divergence at most `C h^{2s}`, a rule correct with
probability `1−δ` needs

$$N \ \ge\ \Bigl(\tfrac{1-\delta}{K}\log\tfrac1\delta - \tfrac2e\Bigr)\Big/ C \cdot h^{-2s},$$

the constant depending on the family and on the number of answers `K` alone — never on `h`
or on `δ`. It is applied at `s_safe` and at `s_id` with nothing differing but the exponent.

**Upper, and it is weaker in `δ`.** The Chebyshev budget `V/(36αh²)` suffices, i.e.
`O(h^{-2}/α)`.

**The separation is an identity.** At `s_safe = 1` and `s_id = t+1`,

$$\mathrm{lowerBudget}(t+1) = \frac{36\alpha c_\delta}{CV}\cdot\frac{1}{h^{2t}}\cdot\mathrm{safeSufficient},$$

and `separation_unbounded` says the factor exceeds any `M` once `h < √(A/M)`, with `A`
written down. Nothing here is asymptotic.

**What is not proved.** The two sides do not match in the confidence parameter:
`log(1/δ)` below, `1/α` above, with the ratio `VC/(36α c_α)` recorded as its own statement.
There is **no** theorem of the form `N* = Θ(h^{-2s} log(1/δ))` anywhere in this corpus, and
closing that gap needs a test whose error decays exponentially in `N` — the
characteristic-function route of §B2c, not formalised.

*Lean: `budget_lower`, `safe_upper`, `separation_ratio`, `separation_unbounded`,
`sides_do_not_match` — `LeanPaperBHeadlineV1`.*

---

## C11. The naming step for ranking → flow

The conservation statement is proved for an arbitrary finite law and an arbitrary pair of
observables, and its own header says the flow is what one gets *by naming the observables*.
The naming was the part left in prose. It is done at the layer map the rest of the corpus
already uses, `rankLayer ty k` — the count vector of the first `k` positions of a
permutation by type — so that

$$x_k(v) = P(\mathrm{rankLayer}_k = v),\qquad f_k(v,v') = P(\mathrm{rankLayer}_k = v,\ \mathrm{rankLayer}_{k+1} = v'),$$

and conservation in both directions, non-negativity, the unit total, the transport of the
objective and of the **whole budget vector at once** are instances rather than new
arguments. The last is what "the same optimisation" means when the objective is a maximum
over budgets: the per-budget expectations agree budget by budget, so their maxima agree.

**Scope.** `rankLayer` records how many items of each *type* have been served, not which
ones, so a per-item retained marginal is not a function of the composition. It becomes one
only after relabelling within each type group — the existing invariance route, not redone
here. What transports directly is the group occupancy.

*Lean: `flow_conservation_out`, `flow_conservation_in`, `flowX_total`,
`objective_transports`, `group_count_transports`, `budget_vector_transports` —
`LeanPaperCNamingV1`.*

---

## C12. The family, and why `|heavySet| = 2` is not a corollary

Everything in the C development is stated for the *predicates* `IsEvenFamily` and
`IsOddFamily`: weights in `{−3,−1,1,3}` with total `0` or `−1`. Those predicates do not pin
the family, and in particular they do not force two heavy items —

$$(1,1,-1,-1)\ \text{satisfies } \mathtt{IsEvenFamily}\ \text{with an \emph{empty} heavy set,}$$

which `isEvenFamily_not_forcing_two_heavy` exhibits. Since the endpoint argument uses
`|heavySet| = 2`, that is a fact about the concrete family and has to be proved there.

So `g_m = (−3, −1×p, +1×q, +3)` with `p = ⌈(m−2)/2⌉ = (m−1)/2` on `ℕ` division is written
down. Its total is one computation: peel the two heavy endpoints, split the middle at the
sign change into `p` negatives and `n−p` positives, and read off `(m−2) − 2⌊(m−1)/2⌋`, which
is `0` at even `m` and `−1` at odd `m` — both predicates from the same line. Its heavy set is
exactly the two endpoints, hence of card `2`.

*Lean: `gFamily`, `gFamily_total`, `gFamily_isEvenFamily`, `gFamily_isOddFamily`,
`mem_heavySet_gFamily`, `gFamily_heavySet`, `gFamily_heavy_card`,
`isEvenFamily_not_forcing_two_heavy` — `LeanPaperCFamilyV1`.*

---

## C13. The window construction is a ranking of the family

The window sums are about `oddBase = (+3,−3,−1,+1,…)`. The value they support is a statement
about rankings of `g_m = (−3, −1×p, +1×q, +3)`. Those are different sequences, and nothing in
the corpus connected them — so, until this section, the computation was about an object the
claim did not name. That is load-bearing, not cosmetic: if they were not rearrangements of
one another the window sums would be evidence for nothing.

They are. Counting each weight on both sides gives

$$(+3,\,-3,\,-1,\,+1)\ \longmapsto\ \bigl(1,\ 1,\ \tfrac{m-1}2,\ \tfrac{m-3}2\bigr)$$

for both sequences, which is equality of the two multisets. The counting turns cardinality
into a `Finset.range` sum (`card_filter`, then `Fin.sum_univ_eq_sum_range`) and evaluates it
with the same peel-and-split the window sums use: peel the two heavy positions, and the
middle block is an alternating indicator on one side (`s+1` even residues, `s` odd) and an
interval indicator on the other (`s+1` below the cut, `s` above).

**What is proved and what is not.** `countVal_agree` is stated at *every* real weight, so the
case of a weight outside `{−3,−1,1,3}` is proved rather than waved at, and the statement is
genuinely multiset equality. The bijection realising the rearrangement is **not**
constructed; what is proved is that one exists, which is what "is a ranking of `g_m`" means.

*Lean: `count_ge`, `count_lt`, `count_even_range`, `count_odd_range`, `sum_ite_two`,
`countVal_oddBase`, `countVal_gFamily`, `countVal_agree` — `LeanPaperCRearrangeV1`.
Numerical: `EXP_paperC_window.py`, 7/7 self-checks, `paperC_window.json`.*

---

## C14. The freezing lemma, and the martingale at a random past

The one-step Gaussian identity is at a FIXED past. The process needs it at
`n = N_e(t)`, `s = S_e(t)`, both measurable in the past, and the tempting shortcut —
"`S_e` given `N_e` is Gaussian" — is **false** under adaptive sampling, because the count's
evolution depends on the observations.

The correct statement is the freezing lemma, which Mathlib does not have:

$$\mathbb E\bigl[f(X,Y)\,\big|\,\sigma(X)\bigr] \;=\; \Bigl(x\mapsto \int f(x,y)\,d\mathcal L(Y)\Bigr)\ \text{at}\ x=X,$$

for `Y` independent of `X`. It is built from three Mathlib facts: independence makes the
joint law a product; a product is a composition with a **constant kernel**; and `condDistrib`
is characterised by that composition. So the conditional distribution of `Y` given `X` is
constant, and `condExp_prod_ae_eq_integral_condDistrib'` finishes.

With the inner integral evaluated by `one_step_mean` pointwise in the frozen past,
`E[M_{t+1} | F_t] = M_t`.

**Integrability is derived, not assumed.** By the product criterion, the joint is integrable
exactly when the previous step is: the inner integrals are finite (the same completion of the
square that evaluates them shows the integrand is a constant times a Gaussian), and their
values are the previous process. So `E M_t = 1` and integrability propagate together, from
`M_0 = 1`.

**Scope.** The bookkeeping is taken in factorised form — counts, sums and query are
measurable functions *of the past* — which is what "measurable with respect to the
filtration" says, written the way an algorithm is written. `a` is fixed and the process is at
a fixed true parameter.

*Lean: `condDistrib_const_of_indepFun`, `condExp_freeze`, `condExp_freeze_apply` —
`LeanPaperAFreezeV1`; `martingale_step`, `mean_step`, `Mval_init`, `joint_integrable`,
`inner_integrable_law`, `Mstep_measurable` — `LeanPaperAAdaptMartV1`.*

---

## C15. The process is what the code thresholds

`Mval` **is** `Mstat`, the implementation's mixture, by `rfl`. Crossing `Q_t > b_t(δ)` forces
`M_t ≥ 1/δ` because the penalty `½Σ_e log(1+N_e/a)` appears on both sides and cancels — which
is precisely why the threshold carries the penalty rather than a bound on it. The one-step
conditional equalities assemble into a Mathlib `Martingale`, hence a supermartingale, and the
crossing event is contained in the event Ville bounds.

**What is still not proved**: that the code's `q_t`, `N_e(t)`, `S_e(t)` are the model's
`qf`, `Nf`, `Sf`. That is a statement about the implementation, and it is the only thing
between this and a rate attached to the running algorithm.

*Lean: `Mval_eq_Mstat`, `threshold_crossing`, `closed_form_error_bound` —
`LeanPaperAStopJoinV1`.*

---

## C16. The coefficient table, realised by densities

`coefOf i k = [k = i+1]` is not realisable as a table of raw moments, and the corpus says so.
It is meant as the table of expansion coefficients in `h`. Until a family of densities
realises it, the partition it induces rests on a table nobody has exhibited.

The family is a two-point mixture whose mixing weight is the scale:

$$\mathrm{dens}_i(h) \;=\; (1-h^{i+1})\,\varphi \;+\; h^{i+1}\,\varphi(\cdot-1).$$

Each member is a genuine probability density for `0 ≤ h ≤ 1` — non-negativity and unit mass
are immediate, needing no delicate integral beyond translation invariance — and its
`h`-expansion has coefficient `[k = i+1]·(φ(·−1) − φ)` at order `k ≥ 1`. That is `coefOf`
with one fixed profile.

The resolving order then follows **from the densities**, both directions:

$$|\mathrm{dens}_i(h)-\mathrm{dens}_j(h)| \le h^{\min(i,j)+1}\,|\text{profile}|,
\qquad
\ge \tfrac12 h^{\min(i,j)+1}\,|\text{profile}| \ \text{for small } h,$$

so `r(i,j) = min(i,j)+1`. At a family whose only unsafe subset is the whole world set, this
gives `s_safe = 1` and `s_id = m−1`.

**What this does and does not settle.** It settles that the reading is consistent and
supplies the orders in both directions from actual densities. It does **not** derive the
parity-mask construction's own observation law; that its densities have exactly these
coefficients is the remaining modelling step.

*Lean: `dens_nonneg`, `dens_integral_one`, `dens_vanishes_below`, `dens_separates_at`,
`coefOf_realised`, `s_safe_eq_one`, `s_id_eq` — `LeanPaperBDensityV1`.*

---

## C17. The four steps between the band and the value

`O2_even_from_endpoint_band` reduces (O2) to five inputs; the heavy-set cardinality is §C12
and the other four are here.

1. **Endpoint probabilities from the prefix band.** The band constrains prefixes, not
   positions. The first position IS the budget-1 prefix and the last position is the
   COMPLEMENT of the budget-`(m−1)` prefix, both pointwise identities about a permutation:
   `i = σ0 ⟺ σ⁻¹i < 1` and `i = σ(m−1) ⟺ ¬(σ⁻¹i < m−1)`. So the last position needs the
   band's **upper** side, which a one-sided band would not give.
2. **Actual regret is the normalised excess.** At the two budgets the baseline is `1` at
   both — `m` even makes `m−1` odd — which is the shape the breakpoint identity consumes.
3. **Two budgets bound the maximum.** The objective is `max_k E r_k`, and the average of any
   two budgets is at most the maximum over a budget set containing them.
4. **The infimum.** A bound at every feasible law bounds the value.

Assembled, (O2) holds at an actual law over rankings of `g_m` with every input discharged.

*Lean: `first_eq_inPrefix`, `last_eq_one_sub_inPrefix`, `endpoint_first_lower`,
`endpoint_last_lower`, `regret_odd_budget`, `hid_on_regret`, `avg_two_le_maxRegret`,
`le_value_of_forall`, `O2_even_at_ranking_law`, `O2_even_at_value` —
`LeanPaperCEndpointV1`.*

---

## C18. The region oracle's two traps

**Replacing `>` by `≥` is not free, and it is licensed by a segment.** A region's closure may
contain points its strict part does not. If the region *has* a strictly bad point `λ°`, then
for a boundary point `x` the segment `λ_t = (1−t)x + tλ°` stays in the ordering polyhedron
(convexity), is strictly bad for every `t > 0` (the badness constraint is affine, so
`g(λ_t) = (1−t)g(x) + t g(λ°) > 0`), and converges to `x` (continuity). Hence a lower bound
valid on the strict region is valid on the closure, and the two infima agree. A region whose
strict part is **empty** certifies nothing and must be dropped.

**Zero weights degenerate the Hessian.** A coordinate with `w_e = 0` does not appear in the
objective at all: the inner problem is unconstrained in it, and any formula that inverts the
Hessian is inapplicable. Stating that is what stops a positive-definite formula being applied
to a design with a starved cell.

*Lean: `exists_strict_near`, `lower_bound_transfers`, `empty_strict_contributes_nothing`,
`objective_indep_of_zero_weight`, `zero_weight_unbounded_below_direction` —
`LeanPaperAOracleRegionV1`.*

---

## C19. The surrogate learner's order in `log(1/α)`

Static starvation says the surrogate-optimal design measures nothing that separates the
compression alternatives. The operational consequence is an order, and it needs two inputs,
both named rather than assumed away:

* the learner's own middle-cell budget, `E N_mid(τ) ≤ C + C'·E√τ`, which is what forced
  exploration at rate `t^{-1/2}` produces;
* the stopped change-of-measure at the hidden pairs.

Jensen (`exploration_cost_law`) turns them into `E τ ≥ ((2r/d²·kl − C)/C')²`, and
`kl2_ge_log` replaces the binary divergence by `(1−α)log(1/α) − 2/e`. So the surrogate
learner is quadratic in `log(1/α)` where a true-oracle learner is linear, and the ratio grows
without bound.

**Scope.** This is a statement about a learner with *this* oracle, *this* exploration rate
and *this* tracker. Nothing here says every method using a surrogate pays it.

*Lean: `surrogate_cost_quadratic`, `kl_at_correctness`, `surrogate_omega_log_squared`,
`separation_diverges` — `LeanPaperASurrogateV1`.*

---

## C20. The decision lower bound, and the floor it is conditional on

At a class `H` still unresolved at order `s−1` whose worlds share no safe answer, pigeonhole
gives an answer returned with probability at least `(1−δ)/K` under `θ₀ ∈ H`; that answer is
wrong at some `λ ∈ H`; and data processing on the binary event `{answer = a}` turns the
transcript divergence into a bound on the binary divergence, which the budget arithmetic
converts into `Ω(h^{-2s}log(1/δ))`.

**The floor.** With overlapping safe answers the bound is conditional on `δ`, and not as a
technicality. With `A_w = [m]∖{w}` a decoder that asks *nothing* and guesses uniformly is
unsafe with probability exactly `1/m`. So a statement of the form "`N = Ω(h^{-2s}log(1/δ))`
for every `δ < 1/2`" is **false** for this geometry, and the theorem must restrict `δ` below
`1/m`.

**The decoder.** Elimination needs two inclusions — the truth survives, and nothing outside
its class does — and then the output exists by the definition of `s_safe`. The cost is the
**sum** over tests, not the per-test sample size.

*Lean: `decision_lower_from_class`, `zero_query_floor`, `no_lower_bound_above_floor`,
`candidate_contains_truth`, `candidate_within_class`, `decoder_output_exists_of_common`,
`union_bound_tests` — `LeanPaperBDecideV1`.*

---

## C21. Attainment by a bounded statistic

`sin x ≥ 3x/4` on `(0,1]` (from `x − x³/6 < sin x` and `x³ ≤ x`), so the tail factor's `r`-th
power is at least `(3x/4)^r`: the mean gap is `Θ(h^r)` with an explicit constant, which is a
theorem about the characteristic function and not a fitted slope.

The statistic `cos(t₀Y)` or `sin(t₀Y)` is bounded by one whatever `r` is, so its variance is
at most one. That is the whole reason to use it: the `Y^{r+1}` moment estimator's variance
grows with `r`, and this one does not. The midpoint threshold then classifies correctly once
both empirical means are within half the gap of their own population means.

**A correction.** This section previously said the `log(1/δ)` form needs a Hoeffding-type
inequality "which Mathlib does not have". That was false on the pin we build against.
`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc` is Hoeffding's lemma and
`ProbabilityTheory.measure_sum_range_ge_le_of_iIndepFun` is the Hoeffding inequality for
independent sub-Gaussian summands. Since the statistic lies in `[-1,1]`, its centred version
is sub-Gaussian with proxy `1`, so

    Pr(midpoint test errs)  ≤  exp(-N g² / 8),      hence  N ≥ 8 log(1/δ) / g²  suffices,

which is `bounded_subgaussian`, `decoder_error_le_exp`, `exp_bound_at_budget` and
`log_budget_suffices` (`LeanPaperBHoeffdingV1`). With `g = κ h^r` from `gap_at_scale` this is
`budget_at_scale`: `N = O(h^{-2r} log(1/δ))`, the same exponent as the lower bound and the
same `log(1/δ)`. Running `J` tests costs `8 log(J/δ)/g²` by `union_budget_value` and
`union_error_le` (`LeanPaperBScopeV1`).

`sides_match_in_delta` then bounds `hoeffdingSufficient / lowerBudget` by
`32 K C h^{2s} / g²`, in which `δ` does not appear — so the gap `sides_do_not_match` recorded
is closed in the confidence parameter. It is **not** closed in evidence: only one `(m,h)`
cell of `paperB_decoder.json` certifies both decoders, so there is no measured
identification-rate curve, and the reported ratio is a ratio of budgets meeting a ladder
standard.

The Chebyshev bound `budget_from_gap` is kept: it assumes only a variance and is the
fallback where sub-Gaussianity is not available.

*Lean: `sin_lower_small`, `gap_from_sin_power`, `gap_at_scale`, `bounded_statistic_variance`,
`threshold_decoder_correct`, `budget_from_gap` — `LeanPaperBAttainV1`;
`bounded_subgaussian`, `tail_centred_sum`, `decoder_error_le_exp`, `exp_bound_at_budget`,
`log_budget_suffices`, `budget_at_scale`, `upper_over_log_is_constant`,
`sides_match_in_delta` — `LeanPaperBHoeffdingV1`.
Numerical: `EXP_paperB_decoder.py`, `paperB_decoder.json`.*

---

## C22. The parity-mask channel, and the orders read off it

`K_w = {0, tip_w}` gives `tip_j ∈ K_w` exactly when `j = w`, so the mask value
`v(j,w) = 1 − 2·[j = w]` is `−1` precisely at the named world. Query `j` returns

$$Y_j = v(j,w)\prod_{\ell\le j} Z_\ell + \frac hj\sum_{\ell\le j} Z_\ell + \xi,$$

a Gaussian mixture over the sign cube. Its characteristic function is `cube_sum` at
`a = it·v` and `c = ith/j`, so the difference between the two mask values is

$$2^{j+1}\,\sinh(it)\,\sinh(ith/j)^j,$$

which is `cube_difference` verbatim, of magnitude `Θ(h^j)`. The `v`-dependent term is real
for odd `j` and imaginary for even `j`, which is why the statistic is `cos` or `sin` by
parity.

Reading the orders off: query `j` decides `w = j` versus `w ≠ j`, so a pair resolves at
`min(w,w')`, the classes at level `s` are `{1},…,{s},{s+1,…,m}`, and `s_safe = 1`,
`s_id = m−1`.

**Scope.** This is a *second* observation channel, on support membership. It is not the raw-`F`
query law of the four-world family, and the paper must present both as instantiations of the
same order law rather than as one model.

*Lean: `maskVal_eq_neg_one_iff`, `parity_cf_difference`, `parity_gap_order`,
`query_separates_iff`, `parity_s_safe`, `parity_s_id`, `parity_classes` —
`LeanPaperBParityV1`.*

---

## C23. The band transports, and what the robustness bound really certifies

The flow records how many items of each *type* have been served, so a per-item marginal
becomes a function of the composition only after relabelling within the group: the marginals
are then constant on the group, the group's total is the flow's occupancy, and dividing gives
the per-item value. That is the band constraint in the only form the flow supports.

On robustness, the Lipschitz estimate gives a ratio bound, and the two conclusions it
supports point in opposite directions:

* at `ε ≤ 1/(2m)` the ratio is still at least `(m−1)/3` — the linear-in-`m` price survives a
  perturbation that shrinks with the size;
* at **fixed** `ε` the same bound never exceeds `2/ε`, bounded in `m` — it certifies nothing
  linear at all.

The second is stated because the first is the tempting one to quote, and because band
relaxation at fixed `η` is a *different* robustness result that must not be combined with
weight perturbation.

*Lean: `per_item_from_flow`, `ratio_lower_of_perturbation`, `ratio_linear_at_small_eps`,
`ratio_bounded_at_fixed_eps` — `LeanPaperCTransport2V1`.*

---

## C24. The breakpoint's attainment side, by counting

Insert the heavy pair at position `p+1`, `p` uniform on `{0,…,m−2}`. Then `+3` lies in the
prefix of length `k` exactly when `p < k`, and `−3` exactly when `p < k−1`, so the retained
marginals are `k/(m−1)` and `(k−1)/(m−1)` — derived from the insertion law by counting, not
posited.

For odd `m` both deviate from `k/m` by at most `1/m`, which is `η_* = 1`. For even `m`, mixing
with the sign flip at ratio `1/2` averages them to `(2k−1)/(2(m−1))`, whose deviation is
exactly `|2k−m|/(2m(m−1))` — largest at the end budgets, where it equals `(m−2)/(2m(m−1))`,
i.e. `η_*/m` with `η_* = (m−2)/(2(m−1))`.

**What is not yet assembled.** The passage from these marginals to the mixture's *value* at
every budget needs the per-budget excess of each insertion ranking, which is not here.

*Lean: `count_lt_real`, `plus_marginal`, `minus_marginal`, `plus_deviation`,
`minus_deviation`, `flip_marginal`, `flip_deviation`, `flip_deviation_max` —
`LeanPaperCAttainV1`.*

---

## C25. `CountFeasible` is empty — a conservation count — and the finite-horizon repair

This section exists because the corpus carried a vacuous reduction and the acceptance gate
could not see it. The gate certifies statements; a conditional whose hypotheses cannot all
hold is a statement, and a true one.

**Setup.** State space `V = {0,…,m}^d`, the count vectors; `ty : [m] → [d]` the item types.
`StepC v w` says exactly one coordinate rises by one. `CountFeasible ty F`
(`LeanPaperCFinalV1`, line 146) asks a layered flow `F` for unit mass, for edge weights
vanishing off `StepC` **at every layer `k : ℕ`**, and for positive-mass trajectories to start
empty and end at the multiplicities.

**Claim.** No `F` satisfies it: `CountFeasible ty F → False`.

**Proof.** Write `R(v) = Σ_τ v_τ`, the number of items the state has served.

*(i) The count is bounded.* Each coordinate is at most `m` and there are `d` of them, so
`R(v) ≤ d·m` for every state.

*(ii) A legal step serves exactly one more item.* If `StepC v w` then one coordinate rises by
one and the rest are equal, so `R(w) = R(v) + 1`.

*(iii) The mass stays at one.* `inflow` and `outflow` give `Σ_w x_{k+1}(w) = Σ_v Σ_w f_k(v,w)
= Σ_v x_k(v)`, so by induction every layer carries mass one.

*(iv) Hence the expected count grows without bound.* Expand `Σ_w R(w) x_{k+1}(w)` through
`inflow`, swap the sums, and replace `R(w)` by `R(v) + 1` on every edge — legal by (ii) where
`f_k(v,w) ≠ 0`, and vacuous where it is zero. With `outflow` and (iii) this gives

$$\mathbb{E}_{k+1}[R] \;=\; \mathbb{E}_k[R] + 1, \qquad\text{so}\qquad \mathbb{E}_k[R] \;=\; \mathbb{E}_0[R] + k .$$

*(v) Contradiction.* By (i) and (iii), `E_k[R] ≤ d·m` at every `k`; by (iv) at `k = dm+1` it
is at least `dm+1`. ∎

**What this retracts.** `pathDecomposition_count_states` (`LeanPaperCFinalV1`) and
`pathDecomposition_at_count_states` (`LeanPaperCPathV1`) say nothing about any flow, and the
whole of `LeanPaperCPathV1` is affected — its `NoRelabel`, `secOf` and `hsec_secOf` results
are stated over the same empty domain. The `hsec` argument of §C1 is untouched.

*Lean: `served`, `served_le`, `served_step`, `mass_one`, `served_grows`,
`countFeasible_empty` — `LeanPaperCVacuityV1`.*

### The repair, with non-emptiness proved rather than asserted

The defect is that legality is demanded after the items run out. `CountFeasibleH` asks for it
only while `k < m`, requires the flow to idle afterwards (`f_k(v,w) = 0` for `v ≠ w` once
`m ≤ k`), and adds the LP's own capacity constraint `v_τ ≤ mult ty τ` on the support.

Two things then change. First, **the start and end conditions stop being hypotheses.**
`served_grows_H` is (iv) up to the horizon; `mult_sum` says the multiplicities sum to `m`,
because every item has exactly one type, so the capacity constraint makes the ceiling exactly
`m` (`served_le_m`); a count that starts at `E_0[R]`, rises by one a layer and is at most `m`
at layer `m` must have `E_0[R] = 0` (`expected_served_zero`), and the capacity then pins the
state itself at both ends — `start_empty` and `end_full`.

Second, **the new domain is proved inhabited, which is the entire point.** `horizonFlow` is
the deterministic flow that serves item `0`, then item `1`, and so on to item `m−1`, then
stands still (this witness was, for a while, promised by the module's prose before it was a
theorem — `CLAIMS.md` §X3; the mathematics was never at issue, the record was): `stC ty k` is the state after the first `min(k,m)` items, `cnt ty k τ` counts
how many of the first `k` items have type `τ`, `cnt_succ` says serving one more item raises
exactly one count, `stC_step` makes each step before the horizon legal and `stC_idle` makes
each step after it a self-loop, and `cnt_le_mult` is the capacity constraint. `horizon_flow`
is the statement `CountFeasibleH ty (horizonFlow ty)`.

**What is still owed.** The retracted path-decomposition results have not been restated over
`CountFeasibleH`. `trajLaw_stepC` and the section need finite-horizon versions first; the
combinatorics under them — `legal_path_realised`, `matchPerm`, `hsec_count_states` — survives
the change unaltered.

*Lean: `mult_sum`, `CountFeasibleH`, `served_grows_H`, `served_le_m`, `expected_served_zero`,
`start_empty`, `end_full`, `cnt`, `cnt_le_mult`, `cnt_succ`, `stC`, `stC_step`, `stC_idle`,
`horizonFlow`, `horizon_flow` — `LeanPaperCHorizonV1`.*

---

## C26. The band, derived from a weight-preserving relabelling

§C5 added the band up; this section derives it. It removes the `hband` hypothesis from Paper
C's even side, which was the last place that side rested on an assumption rather than a
construction.

**Setup.** A base family `base : R → Perm[m]` with law `q`, and an index set `Γ` of
permutations that (a) leave every weight where it is, (b) is closed under left translation,
and (c) acts transitively on each weight class. Average the base family over `Γ`: the law
`(c,x) ↦ q(x)/|Γ|` on the family `(c,x) ↦ c·base(x)`.

**Step 1: the objective does not move.** If `ρ` fixes every weight then `rankOf g (ρ·σ) =
rankOf g σ`, pointwise — `g((ρ·σ)p) = g(σ p)` is exactly the weight-preserving property at
`σ p`. So the averaging changes no value and nothing has to be recomputed
(`regret_relabel_sum`).

**Step 2: but the item does move.** `inPrefixInd (ρ·σ) k i = inPrefixInd σ k (ρ⁻¹ i)`:
relabelling by `ρ` carries item `i`'s prefix indicator to item `ρ⁻¹i`'s.

**Step 3: so the averaged marginal is constant along each orbit.** By (b), left translation
by any `c ∈ Γ` is a bijection of `Γ`; reindexing the average by it and using Step 2 gives
`relMarg(i) = relMarg(c·i)` for every `c`. With (c), `relMarg` is constant on each weight
class.

**Step 4: and the class total is unchanged.** Each `ρ ∈ Γ` permutes a weight class, so summing
the averaged marginal over a class gives the same number as summing the base marginal over it
(`relMarg_class_sum`).

**Conclusion.** A quantity constant on a class whose total over that class is `|C|·k/m` equals
`k/m` at every member — `marginal_eq_occupancy_div_card`, giving `relMarg_eq_uniform`. Stated
as membership in the band at `η = 0`, that is `band_zero_of_relabelling`, with no band
hypothesis.

**The hypotheses are satisfiable, and this is proved, not argued.** A conditional whose three
conditions cannot hold together would be worth nothing, so one `Γ` meeting all three is
exhibited: `WPerm g`, the full subgroup of permutations fixing every weight. `wperm_inv` gives
its inverses, `wperm_trans` the closure under left translation as an explicit equivalence, and
`wperm_orbit` the transitivity — the transposition `swap i j`, which preserves weights exactly
when `g i = g j`. `band_zero_at_weight_group` is the instantiation.

**What this does NOT close, stated so it is not mistaken for closed.**
`band_zero_at_weight_group` still takes `hclass`, the per-weight-class occupancy
`Σ_{j : g j = w} baseMarg(k,j) = |{j : g j = w}|·k/m`. `uniformMix_heavy` and
`uniformMix_light` (`LeanPaperCUniformV1`) compute exactly that for the even-`m` mixture, but
the instantiation is not written. And `witness_for_Vm_eq_at_zero` (`LeanPaperCPermV1`) still
takes `hvalue`, and still carries its own `hband`: that hypothesis is the pointwise identity
`= k/m` for `permFamily g r hcount`, while `band_zero_at_weight_group` concludes membership in
`FeasibleAt … 0` for the averaged family, and nothing in the corpus joins the two.

*Lean: `rankOf_relabel`, `inPrefixInd_relabel`, `relMarg_eq_avg`, `relMarg_const_of_orbit`,
`relMarg_class_sum`, `relMarg_eq_uniform`, `regret_relabel_sum`, `band_zero_of_relabelling`,
`WPerm`, `wperm_inv`, `wperm_trans`, `wperm_orbit`, `band_zero_at_weight_group` —
`LeanPaperCRelabelV1` (13 theorems).*

---

## What is not proved anywhere in this corpus

Maintained as the single place a reader can look, and reconciled against the corpus after
the three link-closing rounds recorded in `CLAIMS.md` §L1--L26. Of the eighteen entries the
previous revision carried, **twelve are now closed and one was withdrawn as my own error**;
what remains is six, listed with the exact blocker rather than a gesture. Four earlier
entries turned out to be **stale** -- already proved elsewhere in the corpus -- and saying so
is part of the accounting, not a way of shrinking the list.

**This revision an entry got WORSE, not better.** Entry 6's old blocker was in fact already
discharged, so it was due to come off the list -- but the class the theorems quantify over,
`CountFeasible`, turns out to be empty (§C25), which is a strictly worse defect than the one
it replaced. The entry is rewritten around the retraction rather than deleted. A list that
only ever shrinks is not being kept honestly.

### Paper A

1. **The observation-model bridge.** `energy = ` Gaussian KL is proved at the witness, not
   for every `λ ∈ Θ₀`, and the alternatives are still defined by ranges and by the frozen
   contrast rather than by the observation model's own alternative class.
   **Blocker:** the alternative class of the response map has to be formalised and the
   families carried through it. That is a new development, not an assembly of existing
   pieces. (The two bridges the manuscript called "asserted" are NOT part of this: `a_T` is
   defined from `F, q, T` with `residual_eq_inner` the identity, `loss_eq_half_range` is the
   displayed loss, and `selectedRadius_eq_compressionLoss` joins them to the corpus's own
   selected radius.)
2. **The learner, end to end (A-H4).** `a7_chain_rate` still takes `hgood`, `hinit`,
   `hEsum`, `hsup`.
   **Blocker:** a per-round lower bound on the information the concrete certificate
   accumulates. That is the substance of the learner's analysis. Separately, the tail bound
   must be joined to a hitting time that may be infinite (`hitTime : ℕ∞` versus
   `τ : Ω → ℕ`) before termination follows.
   *Closed on this path since the last revision:* the `n^{-4}` confidence step
   (`LeanPaperAConfStepV1`), the identification of the code's three accumulators with the
   model's (`LeanPaperAIdentifyV1`), and the threshold hypothesis, which was FALSE for the
   implementation and is now repaired by a shift costing an arbitrarily small rate
   (`LeanPaperA7ThresholdV1`).

### Paper B

3. **The continuous adaptive transcript.** The finite-alphabet version is proved and
   constructive for ANY adaptive policy (`LeanPaperBTranscriptV1`), and data processing for
   it is proved from scratch (`kl2_le_klChain`, `LeanPaperBDataProcV1`).
   **Blocker:** building `hdens` and the per-step `klIncr` from a Gaussian policy's own
   kernels in the measure-theoretic setting.
4. **`N_safe(h) = Θ(h^{−2 r_safe})` for an ARBITRARY family.** Established on the
   constructed family only.
   **Blocker:** none that is actionable -- this is a claim about arbitrary families, which
   the papers do not make. It is listed so the scope is not mistaken for a gap, and it is
   not counted as a debt.

### Paper C

5. **The wrapper's remaining half.** `Vm_eq_at_zero` (`LeanPaperCLowerZeroV1`) reduces
   C-H1's even side to exhibiting ONE feasible law of the right value: the lower side is the
   budget-1 identity holding for every feasible law, and all the arithmetic -- type counts,
   the band at `η = 0`, the value -- is proved.
   **Blocker, now narrower and stated exactly.** The relabelling inside each weight type is
   no longer missing: §C26 derives the band from it (`band_zero_of_relabelling`) and exhibits
   a subgroup satisfying every hypothesis (`WPerm`, `wperm_inv`, `wperm_trans`,
   `wperm_orbit`, `band_zero_at_weight_group`). What is left is two hypotheses and one
   composition: `hclass`, the per-weight-class occupancy, undischarged for the concrete
   even-`m` mixture although `uniformMix_heavy`/`uniformMix_light` compute it; `hvalue` in
   `witness_for_Vm_eq_at_zero`; and the join between `band_zero_at_weight_group`'s conclusion
   (membership in `FeasibleAt … 0` for the averaged family) and
   `witness_for_Vm_eq_at_zero`'s `hband` (the pointwise identity for `permFamily`), which
   nothing in the corpus writes.
   *Also repaired on this path since the last revision:* `FeasibleAt` itself was empty --
   the band was quantified over all `k : ℕ`, and at `k = m+1` the left side is `1` against
   `k/m = 1 + 1/m` -- so `Vm_ge_at_zero` and `Vm_eq_at_zero` were vacuous. That was my own
   defect. The quantifier is bounded to `k ≤ m` and the set is proved inhabited by
   `feasible_zero_nonempty`, on `cyclicPerm`/`cyclicLaw`/`cyclic_marginal`
   (`LeanPaperCValueSetV1`).
6. **E1--E3, the path decomposition -- RETRACTED, not merely open.** The previous revision
   listed this as needing `sec`/`hsec` composed. That debt was in fact paid
   (`countSec`, `countSec_layer`), and the entry should have come off the list. It does not,
   because a worse defect was underneath it: the class those theorems quantify over,
   `CountFeasible`, is **empty** -- `countFeasible_empty` (§C25). So
   `pathDecomposition_count_states`, `pathDecomposition_at_count_states` and the results of
   `LeanPaperCPathV1` stated over that domain (`NoRelabel`, `secOf`, `hsec_secOf`) are
   withdrawn as statements about flows.
   **Blocker:** restating them over the repaired domain `CountFeasibleH`, which is proved
   non-empty by `horizon_flow` and on which `start_empty` and `end_full` are derived rather
   than assumed (`LeanPaperCHorizonV1`, §C25). Concretely that needs finite-horizon versions
   of `trajLaw_stepC` and of the section; the combinatorics beneath them
   (`legal_path_realised`, `matchPerm`, `hsec_count_states`) carries over unchanged.

### Closed since the previous revision

`log(1/δ)` upper side and the two sides matched in `δ`; the box on the channel's queries; a
concrete adaptive policy with an explicit `L_t`; the `n^{-4}` confidence step; the code's
accumulators; the threshold repair; the closure exchange; the separation order read off the
query model; the decoder's own pair, its componentwise envelope and the normalisation of
`gkern`; the divergence's monotonicity; data processing from scratch and `hchange` with it;
the matching lower bound at uniform marginals; the value lemmas instantiated at `V_m(η)`;
the robustness collapse scale, located by a matching lower bound; a measured
identification-rate curve; and the band at `η = 0` derived from a weight-preserving
relabelling with its own hypotheses exhibited (§C26). **Withdrawn:** my own note that the
`η = 0` mixture might contradict the even breakpoint -- it does not, and
`free_value_lt_uniform_value` is the proof. **Retracted, in the other direction:** the
flow-to-ranking path decomposition, whose feasible class is empty (§C25); and, separately,
`FeasibleAt`'s unbounded band, which made `Vm_ge_at_zero`/`Vm_eq_at_zero` vacuous until the
quantifier was bounded and the set exhibited. Both were vacuity defects that a clean
acceptance gate cannot detect, which is why they are recorded here and not only in the Lean. **Stale entries removed:** the outer certificate over every design, the endpoint
assembly, the two A model bridges, and `|heavySet| = 2` for `g_m`, all of which were already
proved.
