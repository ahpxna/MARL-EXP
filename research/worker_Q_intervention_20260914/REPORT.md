# Q-Intervention closed, four broken modules repaired. 61 clean audits across six modules.

| module | audits | nonstd | status |
|---|---|---|---|
| `LeanFunctionalCrossoverLowerV1` (new) | 19 | 0 | accepted |
| `LeanQueryInterventionFloorV1` (new) | 7 | 0 | accepted |
| `LeanFunctionalCrossoverExactRegionV1` (was exit 1, 5/7 sorryAx) | 7 | 0 | accepted |
| `LeanStructuralRecourseUniformNestingV1` (was exit 1, no audit print) | 10 | 0 | accepted |
| `LeanD6WidthTransitionLocalV1` (was exit 1, 7 errors) | 10 | 0 | accepted |
| `LeanSupportPassiveAnswerMultiplicityV1` (was exit 1, 7/8 sorryAx) | 8 | 0 | accepted |

Every receipt: `lean_exit=0`, source hash unchanged, `.olean` strictly newer,
axioms only `{propext, Classical.choice, Quot.sound}`.

---

## 1. Q-Intervention — the randomized floor

`scripts/Q1_intervention_regret_floor.py` reproduces the supervisor's witness in
exact rational arithmetic on the corpus's own compensated world
(`k=3, t0=1/8, rho=1, T={0,1,2}, j=5, A={0,1,3}, B={0,2,3}`):

* the two worlds share the raw histogram EXACTLY — 32 atoms, total mass 1;
* the budget-1 loss table reproduces the supervisor's table digit for digit;
* own optimum `35169/32768` on both worlds, attained at `{2}` for `A` and `{1}`
  for `B` — DIFFERENT decisions, which is the whole difficulty;
* **randomized minimax regret = `2401/8192`**, both directions: the mixed rule
  `1/2` on `{1}` and `1/2` on `{2}` attains it on both worlds, and the uniform
  prior gives the matching Bayes value;
* contextual separation `E[(F_A - F_B)^2] = 28487865/536870912 > 0`.

**The size of the G4 error.** The deterministic `min_S max_A` at
`G4:412` gives `13983/32768 = 0.4267`; the true randomized value is
`2401/8192 = 0.2931`. The deterministic number is **1.456× too large**, so it
overstates the floor and may not be quoted as a bound for every algorithm.

`LeanQueryInterventionFloorV1` proves, over EVERY probability vector on the four
decisions:
* `regret_floor` — `max (regretA P) (regretB P) ≥ 2401/8192`, by the averaging
  argument (the max is at least the mean; every column of the summed regret
  vector has coefficient at least `19208/32768`);
* `regret_floor_attained` — the value is exact, not merely a bound;
* `deterministic_minimax_is_larger` — the deterministic quantity is strictly
  bigger, proved, so the correction is on the record inside Lean;
* `blind_procedure_floor` — the bridge: a procedure reading a transcript in a
  finite `Omega` and emitting a decision distribution uses ONE `mu` and ONE
  `rule` for both worlds, because the worlds induce the same transcript law, so
  the floor applies verbatim — any number of samples, adaptive or not, any
  internal randomisation, any history-dependent stopping.

### What Q-Intervention does NOT establish

- **The raw-law equality is not formalised.** It is verified exactly by the probe
  (all 32 atoms), and the loss table is transcribed from the same probe. The
  permutation transport `F_{pi A}(pi x) = F_A(x)` on `centeredWorld` is a
  separate obligation, NOT discharged. So the Lean results are theorems about the
  TABLE plus a bridge; they become statements about the worlds only once that
  equality is formalised. Steps Q1 and Q2 of the assignment are therefore open.
- `Omega` is finite with a probability vector; the Gaussian channel is not
  modelled.
- Nothing is proved about the contextual instrument: no sample-size bound, and
  the likelihood-ratio constant `C` is not computed. "The KL is positive so it
  suffices" is not an argument and is not made.
- One configuration, one pair of worlds, budget one. No law in `k`, nothing about
  `b_dec` or `b_id`.

`scripts/G4_fixed_world_observation_classes.py` was corrected: the key is now
`raw_deterministic_minimax_loss`, the randomized value is computed exactly for
two-member classes, and larger classes report `null` with the reason rather than
the deterministic number.

---

## 2. The four broken modules

**`LeanFunctionalCrossoverExactRegionV1`** — both failures were EQUALITIES that
`linarith`/`nlinarith` could not reach because they need `(sqrt 2)^2 = 2`.
Isolated the residual in a scratch module: `three_cost_identity` needs exactly
`linear_combination (-(q*u*p) - u*p^2 - u^2*p) * sqrt_two_sq`, and `star_JEM`
needs `unfold H; linear_combination (2*a) * sqrt_two_sq`. The Cauchy–Schwarz
identity is genuine: the slack is `p(xq-√2u)^2 + q(xp-2u)^2 + u(√2p-2q)^2` and
the residual was `(2 - s^2)(qup + up^2 + u^2p)`, zero exactly when `s^2 = 2`.

**`LeanStructuralRecourseUniformNestingV1`** — a `Finset.sum_sub_distrib` rewrite
applied to a goal already closed by `rfl`, and a no-progress `simp`. It then
compiled but still failed acceptance with `audits=0`: the file had NO
`#print axioms` lines at all. Added ten.

**`LeanD6WidthTransitionLocalV1`** — seven sites: two `simp` calls leaving
`1 + -mu = 1 - mu`, three `ring`s after a `field_simp` that had already closed
the goal, and two real inequalities. The first needed `eta ≤ 1/2` supplied as the
product hint `(q-1)·q·(1-2η) ≥ 0`; the second needed `(|T|-2)(1-η)V0 ≥ 0`
expanded so `linarith` could see the atoms.

**`LeanSupportPassiveAnswerMultiplicityV1`** — nine errors, mostly this Mathlib's
`Finset.card_sdiff : #(s \ t) = #s - #(t ∩ s)` taking no subset argument (use
`Finset.inter_eq_left.mpr`), a `not_iff_not` rewrite on a non-negation, a
motive-not-type-correct rewrite of `m` inside `Fin m`, and `((1-γ)^2)^N` versus
`((1-γ)^N)^2`.

**But compiling it does not close the package, and the header now says so.** The
supervisor is right. Added a "WHAT THIS FILE IS NOT" section naming the four
undischarged obligations: the i.i.d. sample law is never used; the posterior
under the uniform prior is not defined, so `symmetric_posterior_value` ASSUMES a
common posterior value and only averages it — an algebraic identity, not a
symmetry theorem; the attaining policy and the Bayes lower bound are absent; and
`missing_second_moment_bound` is an inequality about an EXPRESSION that is never
proved to be `E[L_N^2]`, because `L_N` is not a random variable in this file.
So `lambda/(a+1+lambda) ≤ R_N^* ≤ lambda/(a+lambda)` is NOT proved.

---

## 3. Structural C1 verdict — corrected

`research/worker_gopC_20260913/C1_eps_nest_dp.json` recorded
`max_eps_nest_found = "1/2"` with an explicit `argmax_matrix`, while its verdict
still read "no instance exceeding 1/4 was found". Re-verified independently by
enumerating all 24 rankings of

    F = [[0,-2,-2],[0,0,0],[0,0,0],[0,2,2]],   D = 4,

which gives `eps_nest(F) = 1/2` exactly. **The conjecture `eps_nest^star = 1/4`
is refuted.** The verdict was rewritten and the stale text kept as
`superseded_verdict`. The open question is now the sharp constant between the
lower witness `1/2` and the sketched top-span upper `2/3`; neither is a Lean
theorem, and the search covers only `m=4, d=3, entries in (-2..2)`.

---

## Still open from the audit list

- **B1's rational certificate for `r^z`** is NOT fixed.
  `scripts/B1_d6_width_transition_local.py:303` still takes floating-point
  `exp`/`log`, rationalises and multiplies by `1 - 1e-9`. That does not certify
  the lower direction and the downstream `Fraction` arithmetic cannot repair it.
  The fix is the one the supervisor specified — for rational `z = u/v` certify
  `c_lo^v ≤ r^u ≤ c_hi^v` in exact integer arithmetic, and directed-rounding
  interval arithmetic for general exponents.
- Q1 and Q2 of Q-Intervention (permutation transport and raw-law equality in Lean).
- The Support passive minimax bridge, per the four obligations above.
