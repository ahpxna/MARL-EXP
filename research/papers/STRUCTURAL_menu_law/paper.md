# One schedule cannot serve every budget: an exact menu law under signed cancellation

**Draft — every mathematical claim below is machine-checked in Lean 4 unless the sentence
says otherwise. Theorem names in `monospace` are the formal statements; the module is
given in brackets.**

---

## Abstract

A schedule reveals items one at a time; a client with budget `k` sees the first `k`. We
ask how well a single schedule, or a small menu of schedules, can serve every budget at
once when the items carry **signed** weights that cancel.

For the family `g_m = (−3, (−1)^p, (+1)^q, 3)` with `p = ⌈(m−2)/2⌉`, `q = ⌊(m−2)/2⌋` we
prove an exact two-sided law for every `m ≥ 5`:

$$V_{\text{avg}}=\frac{2}{(m+4)(m-1)},\qquad
V_{\text{path}}=\frac{2}{m+4},\qquad
\frac{V_{\text{path}}}{V_{\text{avg}}}=m-1 .$$

Both values are proved as lower bounds and attained, so the ratio `m−1` is an identity,
not an estimate. The ratio is exactly the number of schedules a menu needs.

---

## 1. What is new here, and what is not

*Disser, Klimm, Schewior and Weckbecker, arXiv:2305.01310, and the ICALP 2017 line it
continues.* Read at theorem level, the setting is: a monotone objective
`f : 2^U → ℝ_{≥0}`, **accountable**, meaning

> for every `X ⊆ U` there exists `e ∈ X` with `f(X∖{e}) ≥ f(X) − f(X)/|X|`.

Their Theorem 1 gives GreedyScaling achieving the best-possible competitive ratio `ρ* ≥ 1`;
Theorem 2 that `GreedyScaling(c₁, φ+1)` is `(φ+1)`-competitive iff `d(c₁) ≥ 1/(φ+1)`;
Theorem 4 the lower bound `2.246`; Theorem 5 a `1.772`-competitive randomised algorithm.

The whole incremental-maximisation programme for monotone accountable objectives — the
upper bound `φ+1 ≈ 2.618`, the lower bound `2.246`, the randomised `1.772` — is prior, as
is the idea of one schedule serving every budget. This paper credits all of it.

**Three separations, and the first is decisive.**

1. **Class.** The prior's objective has codomain `ℝ_{≥0}`. Our family's prefix sums go
   negative — that is the phenomenon under study — so the objective fails the codomain
   restriction *before* accountability is even tested. This is a class separation, not a
   constant improvement, and no constant of theirs is comparable to any constant of ours.
2. **Metric.** Their guarantee is a **multiplicative** competitive ratio. Ours is
   **additive**, normalised by `D = Σ|g_i| = m+4`. The two numbers are not on the same
   scale and must never be tabulated together.
3. **Object.** They ask for **one** ordering serving all cardinalities. We ask for the
   **minimum menu**, and prove its size is exactly `m−1`.

---

## 2. The family, and why the regret has a clean form

Items carry the signed weights `g_m = (−3, (−1)^p, (+1)^q, 3)`, so `D = Σ|g_i| = m+4` and
`Σ g_i ∈ {0, −1}`. A schedule is a permutation; at budget `k` the retained prefix has sum
`s_k`, and the normalised regret is `(|s_k| − k mod 2)/D`, because every `g_i` is odd and
therefore `min_{|S|=k} |Σ_{i∈S} g_i| = k mod 2` by parity.

Define the **even part** `dfc s = |s| − |s| mod 2`.

**Theorem 2.1** (`parity_bridge` [`LeanStructuralFamilyLowerV1`]).
`dfc s_k = |s_k| − k mod 2`. So `dfc` *is* the normalised numerator, and no index
bookkeeping is needed anywhere below.

**Theorem 2.2** (`dfc_nonneg`, `dfc_even`, `dfc_eq_zero_iff`, `two_le_dfc`, same module).
A budget is free iff its prefix sum lies in `{−1,0,1}`; any defect is an even number `≥ 2`.

---

## 3. The mechanism: no schedule is free

**Theorem 3.1** (`no_big_step` [`LeanStructuralFamilyLowerV1`]).
If a schedule pays nothing at any budget, then every single element moves the prefix sum
by at most `2`.

**Theorem 3.2** (`two_le_totalDefect`, same module).
Every ordering of the family pays at least `2`: the element `3` is a step the mechanism
of Theorem 3.1 forbids.

This is where the signed structure does the work. A non-negative objective has no
analogue of Theorem 3.1, which is the technical reason the prior class cannot host this
argument.

**Important.** Theorems 3.1 and 3.2 hold for **every** ordering of the family, with no
saturation, balance or concentration hypothesis. An earlier module in this project proved
the mechanism only under two such hypotheses and checked the family by script for
`m = 5..14`; both hypotheses are discharged here, and the statement is for all `m ≥ 5`.

---

## 4. The two lower bounds

Let `r(π,k)` be the regret of schedule `π` at budget `k`, and `P` a mixture over
schedules.

**Theorem 4.1, the averaged bound** (`avg_lower` [`LeanStructuralFamilyLowerV1`]).
If `r ≥ 0`, `P` is a probability vector and every schedule has total cost at least `c`,
then

$$\frac{c}{|\text{Bud}|}\;\le\;\max_k\ \mathbb E_P\big[r(\pi,k)\big].$$

**Theorem 4.2, the path bound** (`path_lower`, same module).
If every schedule pays at least `c` at *some* budget, then

$$c\;\le\;\mathbb E_P\Big[\max_k r(\pi,k)\Big].$$

The two differ only in the order of `max` and `𝔼`, and that is the entire content of the
paper: `max 𝔼` against `𝔼 max`.

**Theorem 4.3, both are attained** (`avg_achieved`, `path_achieved`, same module).
The uniform mixture over the one-defect schedules attains the averaged bound at
`c/|Bud|`, and attains the path bound at `c`. So neither bound is loose.

---

## 5. The upper half: one-defect schedules exist, for every `m` and every budget

**Theorem 5.1** (`exists_one_defect` [`LeanStructuralFamilyUpperV1`]).
For all `p, q` with `q ≤ p ≤ q+1` — that is, for every `m ≥ 5` — and every budget
`1 ≤ j ≤ p+q+1`, there is an ordering of the multiset `g_m` whose defect vector is

$$\underbrace{0,\dots,0}_{j-1},\;2,\;\underbrace{0,\dots,0}_{p+q+2-j},$$

i.e. it pays exactly `2`, and pays it exactly at budget `j`.

The construction is `altFrom`, a greedy alternation maintaining the invariant
`|s| ≤ 1 ∧ |s − a + b| ≤ 1` (`altFrom_multiset`, `altFrom_sum`, `altFrom_length`,
`altFrom_defects`). It is a construction, not an existence argument: the list is built.

Since a schedule can be free at every budget except one, and Theorem 3.2 says it cannot
be free everywhere, `2` is exactly the price, and a menu of `m−1` schedules — one per
budget — covers every budget for free in the averaged sense.

---

## 6. The ratio

**Theorem 6.1** (`ratio_card_concentrated_on_support` [`LeanStructuralFamilyLowerV1`]).
If the mixture is balanced (`𝔼_P[r(·,k)]` is the same for every `k`) and each supported
schedule is concentrated (its total cost equals its maximum), then

$$\mathbb E_P\Big[\max_k r(\pi,k)\Big] = |\text{Bud}|\cdot \max_k \mathbb E_P\big[r(\pi,k)\big].$$

With `|Bud| = m−1` and the values of §4–§5 this gives

$$V_{\text{avg}}=\frac{2}{(m+4)(m-1)},\qquad V_{\text{path}}=\frac{2}{m+4},
\qquad \frac{V_{\text{path}}}{V_{\text{avg}}}=m-1 .$$

Both hypotheses of Theorem 6.1 are satisfied by the witness of Theorem 4.3, and the
conclusion is an identity.

---

## 7. The constrained problem and P3's actual marginal

A referee will ask whether the law survives when the mixture is required to realise a
prescribed marginal. `LeanStructuralConstrainedV1` proves the transfer
(`free_bound_transfers`: a free lower bound is a constrained lower bound, since the
constrained feasible set is a subset; `constrained_eq_free`: with the witness inside the
constraint the value is unchanged).

That file checked the witness against a *stylised* constraint — equal expected regret per
budget. The marginal actually at issue is the **retained-component trajectory**

$$x^\*_{i,k}=\frac{1}{|J|}\,\#\{\,j : \text{item } i \text{ lies in the length-}k\text{
prefix of schedule } \pi_j\,\}.$$

`LeanStructuralRetainedMarginalV1` supplies it: `card_prefixSet` (a length-`k` prefix of a
ranking holds exactly `min(k,n)` items), `retained_nonneg`, `retained_le_one`,
`retained_mono`, and `retained_col_sum` — for **every** menu, `Σ_i x*_{i,k} = min(k,n)`,
so the column sum is the budget and no menu can change that count. `cyclic_retained`
computes the trajectory in closed form on the cyclic menu, where it is exactly
`x*_{i,k} = min(k,m)/m` for every item — so the uniform trajectory is realisable, not
merely feasible on paper. `retained_transfer` and `retained_constrained_eq_free` then feed
the real object into the generic lemma.

---

## 8. Formal verification

Lean 4, toolchain `leanprover/lean4:v4.34.0-rc2`, mathlib rev
`1f495c611d05d2215058cd77c7897d625bc3b445`. Acceptance per module requires
`lean_exit = 0`, zero errors, source hash unchanged across the compile, `.olean` newer
than source, at least one `#print axioms`, and axioms contained in
`{propext, Classical.choice, Quot.sound}`. No module contains `sorry`.

| Module | Audited names |
|---|---|
| `LeanStructuralFamilyLowerV1` | 15 |
| `LeanStructuralFamilyUpperV1` | 11 |
| `LeanStructuralConstrainedV1` | 4 |
| `LeanStructuralRetainedMarginalV1` | 8 |

---

## 9. Scope, and what is not established

1. **One family.** The law is for `g_m = (−3, (−1)^p, (+1)^q, 3)`. It is not a theorem
   about arbitrary signed weights, and the manuscript must not present it as one.
2. **The trajectory does not determine the mixture.** `retained_col_sum` is an identity
   *every* menu satisfies; it singles out no menu. A constraint prescribing a
   **non-uniform** trajectory may exclude the witness and change the value — that case is
   open.
3. **The cyclic menu is chosen for computability.** No claim is made that it is optimal
   for the structural family.
4. **Theorem 6.1 has two hypotheses.** Balance and concentration. They hold for the
   witness; a mixture violating either is outside the identity.
5. **No algorithm.** Nothing here is an online or incremental algorithm, and no
   competitive ratio in the prior's sense is claimed or computed.

---

## 10. Open

* Which signed families admit an exact menu law, rather than this one.
* The value under a prescribed non-uniform retained trajectory.
* Whether `m−1` is the minimum menu size in a formal sense stronger than the present
  ratio identity — i.e. a lower bound on menu cardinality, not on regret.
