# Batch complete: all six items. 74 clean audits over nine modules, 0 failures.

Every receipt: `lean_exit=0`, source hash unchanged, `.olean` strictly newer,
axioms only `{propext, Classical.choice, Quot.sound}`.

| module | audits | what it is |
|---|---|---|
| `LeanFunctionalCrossoverLowerV1` | 19 | actual-alternative bridge + sandwich, homogeneous |
| `LeanFunctionalHeterogeneousCrossoverV1` | 4 | heterogeneous UPPER half |
| `LeanFunctionalHeterogeneousLowerV1` | 3 | the bridge, variance-weighted |
| `LeanQueryInterventionFloorV1` | 7 | randomized regret floor `2401/8192` |
| `LeanSupportNormalizedToleranceV1` | 6 | the exact tolerance threshold `gamma_{a,b}` |
| `LeanFunctionalCrossoverExactRegionV1` | 7 | repaired (was exit 1, 5/7 sorryAx) |
| `LeanStructuralRecourseUniformNestingV1` | 10 | repaired (was exit 1, no audit print) |
| `LeanD6WidthTransitionLocalV1` | 10 | repaired (was exit 1, 7 errors) |
| `LeanSupportPassiveAnswerMultiplicityV1` | 8 | repaired, with an honest scope section |

---

## 1. Functional–H_n

**Upper half PROVED** (`heterogeneous_upper`): for EVERY allocation there is a
flipping alternative costing at most `d^2/(32 + 2 d^2 Splus)`, the middle
distribution entering only through `Splus = sum_i sig_i/(g_i + d/2)^2`. Needs no
domain condition.

**The bridge PROVED, variance-weighted** (`energyU_ge_pairV`): for an arbitrary
finite family of outsider cells with arbitrary means and arbitrary positive
variances, every flipping alternative costs at least the pinch value of some pair
of cells. The reason it is short: **the variance enters only through the
precision `w/sig`**, so `two_point` applies verbatim with precisions in place of
masses. Hypothesis `mean a - mean b < 1` is needed and stated.

**The lower half is sharper than proposed.** At the explicit allocation the value
is `c^2/(32 + 2 c^2 H_n)` **exactly** — 140 of 140 configurations inside the
domain — so the proposed factor `(1 + 3c^2/(4 n g_0^2))` can be dropped. At that
allocation the endpoint/endpoint pair is exactly active (ratio `1.000000`) and
every other pair type is strictly above, which is why the value is attained
rather than bracketed. Same `H_n`, different middle distributions gives the
identical rational value. The domain condition `g_0 >= c/(2 sqrt n)` is sharp: in
all 10 violating configurations the value drops BELOW the formula and the active
pair becomes middle/middle.

STILL OPEN: instantiating the bridge at the explicit allocation, i.e. the lower
half in Lean. No limit is taken anywhere. The EECB/LUCB Top-1 comparator
experiment has NOT been run.

## 2. D6 good-allocation sets

`zeta_blind = 1 - V_blind/Gamma` is **strictly positive in every cell**
(0.21–0.38), so the cost of learning `A` to choose an allocation is not zero and
steps 2–4 of the package are worth doing. Above the threshold — about `0.38` at
`q=3`, `mu <= 1/2` — no discovery is needed at all.

`Gamma` reproduces the published solver to 1e-7 in all six cells, which is the
correctness check on the evaluator; both quantities come from the SAME
cutting-plane loop on the SAME alternative set.

**Two structural findings, and they coincide.** `zeta_blind` is EXACTLY constant
(`0.380969` at `q=3` for `mu in [0.1, 0.55]`; `0.377338` at `q=4` for
`mu in [0.1, 0.6]`), and the optimal blind allocation sits entirely on ONE class
— joint queries of width `q` with `h = false`, uniformly, **no scalars** — over
precisely that same range. The support change and the end of the constant region
occur in the same grid interval, at both `q`. `Gamma` itself dips and rises
around there too.

One thing that had to be right: under the invariant restriction the normalisation
is `eqrow . m = 1`, so the dual bound is the max PER UNIT of that constraint. With
the raw max the cutting plane does not converge.

STILL OPEN: `L_zeta`, the information lower bound, and any algorithm. Float LP,
gap below 2e-8, not a rational certificate.

## 3. Query weak leakage

The criterion reduces to two finite conditions (`S_A = S_B` linear in `g`;
`T_A != T_B` quadratic), both exact. The deciding structure: `pi = (1 2)` maps `A`
to `B` with `F_B(x) = F_A(pi x)` and `p(pi x) = p(x)`, verified on all 64 points,
so **a pi-symmetric `g` separates at NO order**.

| class | dim | rank | kernel | pi-symmetric | breaking pi | order |
|---|---|---|---|---|---|---|
| linear | 7 | 1 | 6 | 6 | 0 | **r = 1** |
| quadratic | 22 | 4 | 18 | 16 | 2 | **r = 2** |
| all functions | 64 | 12 | 52 | 44 | 8 | r = 2 |

**In the linear class the kernel IS the pi-symmetric subspace**, so every linear
`g` either separates at `r = 1` or never separates: there is no weak-leakage
regime. Quadratic perturbations admit `r = 2` with second-order gap
`2401/131072`. So the exponent is fixed by which perturbations are physically
available, not chosen.

STILL OPEN: `KL = Theta(h^{2r})` is the reading of the expansion, not a proved
bound — no density is integrated, no remainder bounded. `N_context` is asserted,
not proved. Nothing formalised in Lean; the transport identity is checked
pointwise, not proved about `centeredWorld`.

## 4. Support: the normalized tolerance threshold — PROVED

Computed from `components` itself, not an abstract radius table. With
`b = |W| >= 2`, `a = m - b`:

    osc(component j) = m-1 if j in W, else 1      (`osc_component`)
    B_W = (b(m-1) + a)/2                          (`modular_span_eq`)
    normalized radius of a wrong decision = (m-1)/(b(m-1)+a) = gamma   (`normalized_radius_eq`)

and an exact phase transition: `no_query_needed` — if `eps >= gamma` every
singleton decision already meets the tolerance; `query_needed_below` — if
`eps < gamma` a decision meets the tolerance **iff** it is genuinely safe, so the
tolerance problem IS the safe-decision problem.

STILL OPEN: `b >= 2` assumed (`b = 1` changes the oscillation to `m-2`). The
active and passive minimax laws are NOT proved, so
`V_active(k) = gamma * C(b,k+1)/C(a+b,k+1)` and
`V_passive(N) = gamma * E[L_N/(a+L_N)]` are not established — this supplies only
the `gamma` both branches must be multiplied by, so they are finally quoted in
the same unit. Equal tip masses are essential to those laws and this
normalisation does not transfer to the unequal-mass family for free.

## 5. Structural: `V_avg` versus `V_path` — CERTIFIED SEPARATION

**First, a negative result that forces the right experiment.** On the cycle family
`min_pi max_k r(pi,k) = 0` for `m = 5, 7, 9`: some ranking is optimal at EVERY
budget. So without the marginal constraint both quantities are `0` and nothing
separates — the gap can only come from having to reproduce a given fractional
path's marginals. My first attempt used a constraint-free lower bound and
correctly certified nothing; both LPs carry the marginal constraint.

At `tau = 0`, `m = 5`, matrix `[[0,-2],[0,1],[0,1],[0,1],[0,0]]`:

    V_avg  <=  4/15        (an explicit feasible P, objective computed exactly)
    V_path >=  7/15        (rational dual, feasibility checked exactly)
    certified gap >= 1/5,  ratio 7/4

So the `V_avg`-optimal distribution is **75% worse** when a ranking is actually
drawn. A theorem for `inf_P max_k E[r]` does not transfer.

STILL OPEN: 60 random instances at `m in {4,5}`, `tau = 0`. No claim that the gap
grows with `m`, and no rounding/extraction theorem.

## 6. MASTER: three separated certification layers

Implemented and run on two families with different mechanisms. `sound` is never a
hypothesis: the lower end of every interval is obtained by EVALUATING real
alternatives.

* Functional — **both ends exact rational**: floor = the minimum over ordered
  pairs of the pinch, evaluated at the explicit allocation; ceiling = the
  two-witness bound valid for every allocation. At `n=256, c=2` the interval
  `[1/16, 81/1160]` is too wide and the rule returns **UNDECIDED** rather than
  accepting — which is the point of the layer.
* D6 — the interval is the solver's own primal-dual gap (6e-9 to 1e-8); the dual
  weights are checked non-negative and normalised, but the rows are not re-derived
  in exact arithmetic, so these ends are numerical.
* All three rules return UNDECIDED on a straddling interval; none picks a side
  from the sign of a float.

STILL OPEN, and this is the honest limit: **no algorithm is run.** There is no
transcript, no stopping time and no expected cost — only the layers a scheduler
would consult. An exact-rational reimplementation of the D6 coefficient matrix is
not done, and the calibration boundary is exercised on a synthetic interval, not
computed from the real kernel.

---

## Corrections carried in this batch

- `scripts/G4_fixed_world_observation_classes.py:412` computed a DETERMINISTIC
  min-max; on the witness it gives `13983/32768`, **1.456x** the true randomized
  value `2401/8192`. Renamed and the randomized value added for two-member
  classes; larger classes report `null` with the reason.
- `research/worker_gopC_20260913/C1_eps_nest_dp.json` had a stale verdict
  contradicting its own `max_eps_nest_found = 1/2`. Re-verified independently
  (all 24 rankings, `eps_nest = 1/2` exactly): **the conjecture
  `eps_nest^star = 1/4` is refuted**. Verdict rewritten, old text kept.
- My own `1/n` claim in `CORRECTIONS_REPORT.md` was wrong — the data is
  `n^(-1/2)` over the measured range, and two points cannot establish a rate.
  Retracted.

## Not done, named

`scripts/B1_d6_width_transition_local.py:303` still certifies `r^z` with
floating-point `exp`/`log` times `1 - 1e-9`. That does not certify the lower
direction. The fix is exact integer certification of `c_lo^v <= r^u <= c_hi^v`
for rational `z = u/v`, and directed-rounding interval arithmetic otherwise.
