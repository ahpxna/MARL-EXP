# Functional–H_n: upper half PROVED, lower half exact on 140 configurations.

Module: `work/p13_conjectures/LeanFunctionalHeterogeneousCrossoverV1.lean`
Receipt: `lean_exit=0`, source hash unchanged, `.olean` newer, **4 audits, 0 nonstandard**.
Probe: `scripts/F2_heterogeneous_crossover_check.py`, exact `Fraction` throughout.

The proposal checks out, and the lower bound is **sharper than proposed**.

---

## 1. The bracket is right, and the slack factor is not needed

At the explicit allocation `u = c^2 H_n/(16 + c^2 H_n)`, `w_i ∝ sig_i/g_i^2`,
endpoints `(1-u)/4`:

    n * Gamma_n  =  c^2 / (32 + 2 c^2 H_n)    EXACTLY

in **140 of 140** configurations inside the stated domain — five values of `n`
(perfect squares 64…16384), five values of `c`, six middle families including
heterogeneous means, heterogeneous variances, and both together. Not "≥ the
bracket": equal, as rationals.

So the proposed lower bound
`c^2/[(32+2c^2 H_n)(1 + 3c^2/(4 n g_0^2))]` is correct but loose; the correction
factor can be dropped. The reason is visible in the pair structure: at this
allocation the **endpoint/endpoint pair is exactly the active one** (ratio
`1.000000` to the value) and every other pair type is strictly above it — for a
representative case, E/M at `1.060`, M/M same-type at `1.998`, M/M cross-type at
`4.992`. The EE witness and the EE pinch coincide, which is why the value is
exact rather than bracketed.

## 2. The `H_n` invariance claim holds

Three middle families with different distributions but the same `H_n = 4`
— `(z=0, sig=1)`, `(sig in {1/2,3/2})`, `(sig in {1/4,5/4})` — give the **same**
`n*Gamma_n` as exact rationals (`1/40` at `c=1`, `1/16` at `c=2`), at both
`n=256` and `n=4096`. The middle distribution enters only through the scalar.
This is the falsifiable check the assignment asked for, and it passes.

## 3. The domain condition is sharp, not a technicality

`g_0 >= d/2 = c/(2 sqrt n)` is exactly the condition that every middle cell sits
strictly inside the endpoints. In **all 10** configurations that violate it, the
value is strictly **below** the formula — so the formula is not a lower bound
there — and the active pair stops being endpoint/endpoint. The first witness
found was `n=64, c=4, z=±3/8`, where `g_0 = 1/8 < delta = 1/4` and the active
pair becomes middle/middle. Worth stating as a hypothesis in the theorem, not
skipping as an edge case.

---

## What is PROVED in Lean (the upper half)

`heterogeneous_upper`: for **every** allocation there is a flipping alternative
costing at most `d^2/(32 + 2 d^2 Splus)`, with
`Splus = sum_i sig_i/(g_i + d/2)^2`. Rescaled: `n Gamma_n ≤ c^2/(32 + 2c^2 H_n^+)`.

Three ingredients:
* `witness_EE` — moves the four endpoints to `±(1+rho)/4` and leaves every middle
  cell alone, costing `(endpoint mass)·d^2/32`. The middles' means and variances
  are irrelevant to it, and since middles can only widen the outsider's range the
  flip survives them.
* `witness_middle` — keeps the incumbent at `±1/2` and pushes cell `i` just past
  the opposite endpoint, in whichever direction is cheaper (case split on the
  sign of `z_i`), costing `w_i (g_i + d/2)^2/(2 sig_i)`.
* `min_middle_le` — the averaging step, no optimisation:
  `min_i a_i · 2 Splus ≤ sum_i a_i · 2 sig_i/(g_i+d/2)^2 = u`.

`FlipsH` is stated as "some pair of outsider cells is spread at least as far as
the incumbent" — `|lI1 - lI0| ≤ range` with the sup and inf unfolded to the
witnessing pair. That is what every witness actually exhibits, and it avoids a
`dite`-guarded `sup'` that made the first draft unusable.

Note the upper half needs **no** domain condition: it holds whether or not the
middle cells are inside the endpoints.

## WHAT THIS DOES NOT ESTABLISH

- **The lower half is NOT in Lean.** It is exact-verified on 140 configurations;
  that is numerical evidence, not a receipt. Formalising it needs the
  variance-weighted version of the `energy_ge_pairV` bridge already proved in
  `LeanFunctionalCrossoverLowerV1` — a direct re-run of that argument with
  `A = 1/(2(1/w_I0 + 1/w_I1))`, `B = 1/(2(sig_a/w_a + sig_b/w_b))` — plus the
  three pair-type inequalities at the explicit allocation. That is the next step.
- `Gamma` is not defined. Each statement is "for every allocation there EXISTS a
  flipping alternative costing at most X", which bounds an infimum from above
  without naming it.
- **No limit is taken and no `H_n -> H` hypothesis is used.** Everything is
  finite and holds at every `n`. The limit law `n Gamma_n -> c^2/(32 + 2c^2 H)`
  is not proved; the finite bracket is what is on offer.
- The probe covers `n` a perfect square (so `d` is rational), at most three
  distinct middle types, and `c` in `{1/2,1,2,4,8}`. Nothing outside that was
  swept.
- Nothing here concerns an algorithm, a stopping rule, or sample complexity, and
  the comparator experiment (full-extrema policy against LUCB and EECB on a
  **Top-1** panel) has NOT been run.

## Collision, recorded

`Shahverdikondori–Badri–Kiyavash, Best Group Identification in Multi-Objective
Bandits (2025)`: under `X -> (b + sX, b - sX)` the coordinate-wise maxima sum to
`2b + s(max_a theta_a - min_a theta_a)`, so the range objective reduces into
their model and "identify the group of largest capacity" is **not** novel on its
own. The defensible claim here is the sharp constant, the optimal allocation, and
the fact that the whole law collapses to one scalar `H_n` on a family that is no
longer symmetric. Priority is not claimed: the formula still needs its proof and
scope checked against the literature.
