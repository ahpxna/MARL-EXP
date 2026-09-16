# The price of a calibration query

**Draft — every mathematical claim below is machine-checked in Lean 4 unless the sentence
says otherwise. Theorem names in `monospace` are the formal statements; the module is
given in brackets.**

---

## Abstract

We study a decision problem in which the answer is a threshold set — which items of a
population lie above a fixed level — and the experimenter buys observations under a
budget. The population is partitioned into `K` groups of `m` items. An *ordinary* query
on an item returns its value corrupted by noise; a *calibration* (control) query on a
group returns the group's common offset, at a price `κ` relative to an ordinary query.

We prove two things. First, a **dichotomy**: without a calibration query the problem has
value exactly zero on a group, because two worlds with different answers produce
identical means under every ordinary query. Second, a **price law**: once a calibration
query is bought, the optimal value under a unit budget is exactly

$$\Gamma^\* \;=\; \frac{\Delta^2}{2K\,(\sqrt{m}+\sqrt{\kappa})^2},$$

proved as a lower bound, as an upper bound over all unit-budget designs, and as attained
by an explicit symmetric design — so the constant is exact, not an order of magnitude.

---

## 1. What is new here, and what is not

This section is deliberately placed first, because the machinery this paper uses is old
and the contribution is narrow.

**Prior art, read at theorem level.**

*Dette and Titoff, "Optimal discrimination designs", Ann. Statist. **37** (2009)
2056–2082.* Their Theorem 2.1 states

> $\sup_\xi \Delta(\xi) = \sup_\xi \inf_{\theta_{(2)}} \Delta(\theta_{(2)},\xi)
>  = \inf_{\theta_{(2)}} \lVert \eta - \eta_2(\cdot,\theta_{(2)})\rVert_\infty^2,$

and their Theorem 2.2 characterises *all* T-optimal designs by a linear system. Their
criterion (2.4) is itself a profiled quantity, and the local-alternative noncentrality is
$\delta^2=\theta_{(0)}^{\mathsf T}M_{11.2}(\xi)\theta_{(0)}$ with $M_{11.2}$ a **Schur
complement**.

Consequently the following are **not** contributions of this paper and are cited, not
claimed: profiling a nuisance parameter out of a discrimination criterion; the
Schur-complement form of the information, which is the same shape as our
$I_u = D_u - M_u^2/(2K)$; the existence of a closed-form value for an optimal
discrimination criterion; and the characterisation of optimal designs and their
non-uniqueness.

What Dette–Titoff do **not** contain: any price attached to an observation *type* — their
design space is fixed and all support points cost the same, so no parameter plays the
role of `κ`; any statement that a design problem has value zero without a particular kind
of query; and any rate in the structural parameters `(K, m, κ)`. A Chebyshev
approximation constant is not such a rate.

*Bennouna et al., arXiv:2505.21692.* Their Theorem 1 states that a data set `D` is
sufficient for uncertainty set `C` and decision set `X` **iff** `Δ(X,C) ⊆ span D`;
Theorem 2 that `span Δ(X,C) = dir(X*(C))`; Theorem 3 that their construction terminates
in at most `d` steps. Every result is existential — whether a *fixed* data set suffices.
No theorem gives a rate or a cost as a function of a budget or a price, no nuisance
parameter is profiled, and the query set `Q` is **predefined**: the theorems say which
queries from `Q` are required, never when `Q` itself must be enlarged.

The identifiability half of our anchor witness is exactly the kind of statement this
prior characterises in general, and is credited to it.

**What is left, and is this paper's claim.** The calibration query lies *outside* the
ordinary query set. We prove when adding it becomes mandatory, and what it costs. That
is the price law; nothing else here is offered as new.

---

## 2. Model

A population of `K·m` items carries unknown values `θ_i`. Items are partitioned into `K`
groups; group `g` carries an unknown common offset `b_g`. The answer to be returned is
the threshold set `{i : θ_i > 1/2}`.

* An **ordinary query** on item `i` observes `θ_i + b_{g(i)}` with variance `v`, at unit
  price. It sees the value and the offset only in combination.
* A **calibration query** on group `g` observes `b_g` with variance `ν`, at price `κ`.

Write `a = x/v` for the ordinary precision bought on an item and `b = z/ν` for the
control precision bought on its group. `Δ` is the separation of the two worlds to be
distinguished, `s_m = √m`, `s_κ = √κ`.

---

## 3. The dichotomy: without calibration the value is zero

Take four items, two per group, and the two worlds

$$\theta^{(0)}=(1,\,0,\,0,\,1),\quad b^{(0)}=(0,0)
\qquad\text{versus}\qquad
\lambda=(\tfrac14,\,-\tfrac34,\,0,\,1),\quad b^{(1)}=(\tfrac34,0).$$

**Theorem 3.1** (`hidden_shift_means` [`LeanMasterCalibrationLawV1`]).
For every item `i`, `θ⁽⁰⁾_i + b⁽⁰⁾_{g(i)} = λ_i + b⁽¹⁾_{g(i)}`.

**Theorem 3.2** (`hidden_shift_answers_differ`, same module).
`{i : 1/2 < θ⁽⁰⁾_i} ≠ {i : 1/2 < λ_i}`.

`hidden_shift_answers` locates the disagreement exactly: item 0 is above threshold in the
first world and below it in the second, while item 3 is above in both.

Together (`hidden_shift_witness`) these say: **every ordinary query has the same mean in
both worlds, and the answers differ.** No amount of ordinary sampling separates them, so
on such a group the attainable value is `Γ = 0`. The calibration query is not an
efficiency improvement; without it the problem is unsolvable.

The witness is exhibited in exact rationals, so this is a certificate, not a numerical
observation.

---

## 4. Profiling the group offset

**Theorem 4.1** (`profiled_information` [`LeanMasterCalibrationLawV1`]).
For `a, b > 0`,

$$\inf_{t\in\mathbb R}\Big[\tfrac{a(\Delta-t)^2}{2}+\tfrac{b t^2}{2}\Big]
= \frac{ab\,\Delta^2}{2(a+b)},$$

and the infimum is attained at `t = aΔ/(a+b)`. Both halves are proved: the inequality for
every `t`, and the value at the minimiser.

**Theorem 4.2** (`profiled_information_form`, same module).
`Δ²/(2(1/a + 1/b)) = abΔ²/(2(a+b))` — the harmonic form the model states.

This is where the Schur-complement shape enters, and per §1 the *shape* is Dette–Titoff's.
What is ours is that the two precisions being combined are of two different **priced**
query types.

---

## 5. The cost of one group

A group that must deliver profiled information `h` obeys the information constraint
`h(x+z) ≤ xz`.

**Theorem 5.1, lower bound** (`group_cost_lower` [`LeanMasterCalibrationLawV1`]).
If `h(x+z) ≤ xz` with `x, z, h > 0`, then

$$h\,(\sqrt m+\sqrt\kappa)^2 \;\le\; m\,x + \kappa\,z .$$

The proof is Cauchy–Schwarz on `(s_m x − s_κ z)²`. No optimiser and no multiplier
theorem is consulted.

**Theorem 5.2, attainment** (`group_cost_attained`, same module).
The split `z/x = √(m/κ)` meets the information constraint with equality and spends
exactly `h(√m+√κ)²`.

So `(√m+√κ)²` is the exact price of one unit of profiled information in a group — the
arithmetic mean of the two query prices weighted by their square roots, which is the
signature of a two-resource harmonic trade-off.

---

## 6. The price law

**Theorem 6.1, upper bound** (`calibration_rate_upper` [`LeanMasterCalibrationLawV1`]).
Let `x_g, z_g > 0` for each of `K` groups, with the unit budget
`Σ_g (m x_g + κ z_g) ≤ 1` and the per-group information requirement
`(2V/Δ²)(x_g + z_g) ≤ x_g z_g`. Then

$$V \;\le\; \frac{\Delta^2}{2K(\sqrt m+\sqrt\kappa)^2}.$$

The statement quantifies over **every** unit-budget design, not over a parametric family.

**Theorem 6.2, attainment** (`calibration_rate_attained`, same module).
The symmetric design attains the bound, so the constant `1/(2K(√m+√κ)²)` is exact.

Together these give

$$\boxed{\;\Gamma^\* = \frac{\Delta^2}{2K(\sqrt m+\sqrt\kappa)^2}\;}$$

as an identity, not an order of magnitude. Two readings are immediate and are the
practical content of the paper:

* **κ → 0.** `Γ* → Δ²/(2Km)`: free calibration recovers the cost of the ordinary queries
  alone.
* **κ large.** `Γ* ≍ Δ²/(2Kκ)`: the calibration query dominates the budget. The crossover
  is at `κ = m`, where the two square roots are equal and each query type takes half the
  group's budget.

---

## 7. The anchor is mandatory

§3 shows a group can be blind. The companion statement is that on a *specific* instance
no anchor-free design can match an anchored one, with both sides certified in exact
rationals.

**Theorem 7.1** (`anchorFree_le` [`LeanMasterAnchorInstanceV1`]).
Every anchor-free feasible design is capped at `U₀ = 1/8`, and `anchorFree_attained`
shows `1/8` is reached — so the cap is tight.

**Theorem 7.2** (`anchored_value`, `anchored_budget`, `gap_positive`, same module).
An explicit anchored design with budget `9/20 + 9/20 + (1/10)·1 = 1` attains
`L₁ = 261/1520`, and `261/1520 > 1/8`.

**Theorem 7.3** (`anchor_is_mandatory`, same module; `anchor_mandatory`
[`LeanMasterAnchorCertificateV1`]).
Consequently the anchor is mandatory on this instance. `anchor_mandatory` is stated for
an abstract design type: **no optimality of the anchored design is assumed**, and the
upper certificate `anchor_free_upper` holds for every anchor-free design including those
placing mass anywhere.

`1/8 = 0.125` against `261/1520 ≈ 0.171710…`: a gap of about 37%, in exact arithmetic.

---

## 8. Gain factorisation

**Theorem 8.1** (`hadamard_square_factor` [`LeanMasterGainFactorizationV1`]).
The entrywise square of a width-`r` product is a product of width `r²`; `hadamard_factor_symm`
and `hadamard_square_rank_one` give the symmetric and rank-one cases.

**Theorem 8.2** (`min_attained_on_active`, `inactive_dropped`, same module).
The slack law: the minimum after a perturbation is attained on the active set, and
inactive constraints may be dropped.

These are the structural facts that let the `K`-group sum in §6 be assembled from
per-group statements without a separate convexity argument.

---

## 9. Formal verification

Every theorem cited above is machine-checked in Lean 4 (toolchain
`leanprover/lean4:v4.34.0-rc2`, mathlib rev `1f495c611d05d2215058cd77c7897d625bc3b445`).
Acceptance for each module requires: `lean_exit = 0`, zero errors, the source hash
unchanged across the compile, the `.olean` newer than its source, at least one
`#print axioms`, and the axiom set contained in `{propext, Classical.choice, Quot.sound}`.
No module contains `sorry`.

| Module | Audited names | Accepted |
|---|---|---|
| `LeanMasterCalibrationLawV1` | 10 | yes |
| `LeanMasterAnchorCertificateV1` | 6 | yes |
| `LeanMasterAnchorInstanceV1` | 8 | yes |
| `LeanMasterGainFactorizationV1` | 5 | yes |

The receipts are in the repository beside each source file.

---

## 10. Scope, and what is not established

The following limits are stated in the source modules themselves and are repeated here so
that no reader has to reconstruct them.

1. **Homogeneity.** The law of §6 is proved for a common variance `v`, a common control
   variance `ν`, a common price `κ` and equal gaps. Heterogeneous `v_i`, `ν_g`, `κ_g` and
   unequal gaps are **not** covered.
2. **The anchor result is an instance.** §7 certifies one explicit instance in exact
   rationals. It is a *proof that anchor-free designs can be strictly beaten*, not a
   theorem that they always are.
3. **The dichotomy is a witness.** §3 exhibits two worlds that no ordinary query
   separates. It does not characterise the set of all such configurations.
4. **Finite-sample behaviour.** Everything here is an information/budget statement. No
   estimator, no confidence set and no finite-sample guarantee is claimed.
5. **The gain factorisation** of §8 is algebraic. It carries no probabilistic content.

---

## 11. Open

* The heterogeneous law: replace `(√m+√κ)²` by the corresponding weighted quantity, and
  determine whether it remains exactly attainable.
* A characterisation, rather than a witness, of the configurations on which the
  calibration query is mandatory.
* Whether the crossover `κ = m` has an operational meaning beyond the algebra.
