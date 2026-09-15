# Closure targets for the four open items

Written 2026-09-11 against Mathlib pin `1f495c611d05d2215058cd77c7897d625bc3b445`
(toolchain `leanprover/lean4:v4.34.0-rc2`). Every Mathlib name below was read in
that pin, not recalled. Nothing here is proved; these are the obligations.

---

## Item 4 — matching discovery lower bound  *(tractable; one genuinely new lemma)*

### What is already in hand

| obligation | status |
|---|---|
| per-query KL over the adjacent-swap family | **PROVED**: `D6QueryWidthInformation.actual_average_width_bound`, giving `r/(2σ²(k−1))` at `μ=0` |
| KL adds over `N` observations | Mathlib `klDiv_compProd_eq_add` (`KullbackLeibler/ChainRule.lean`) |
| no decision rule increases KL | Mathlib `klDiv_comp_right_le (κ) [IsMarkovKernel κ] : klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv μ ν` |
| push to a binary event | Mathlib `klDiv_map_le (hg : Measurable g)` |
| Bayes risk lower-bounds minimax | Mathlib `bayesRisk_le_minimaxRisk`, wrapped as `CIGAMF.MinimaxRiskBridge.minimaxRisk_ge_of_equalizer` |

### The one missing piece

This pin has **no Pinsker inequality and no total-variation/KL comparison**. The
two-point route therefore needs the Bretagnolle–Huber step proved from scratch.
It is a self-contained real inequality, not a research question:

```lean
theorem two_point_error_lower (p q : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (a : ℝ)
    (hkl : p*Real.log (p/q) + (1-p)*Real.log ((1-p)/(1-q)) ≤ a) :
    (1:ℝ)/2*Real.exp (-a) ≤ p + (1-q)
```

`mul_log_le_klDiv` gets from the measure-level KL to the binary `p, q`; this
lemma is what converts binary KL into an error-sum bound.

### Then the chain

```lean
theorem discovery_sample_complexity_lower
    (q N : ℕ) (j : I (2*q+1)) (σ2 r : ℝ) (hσ : 0 < σ2) ... :
    minimaxRisk (discoveryLoss q j) (discoveryKernel q j N) ≥ ...
```
with the bound non-trivial as long as `N * r/(2σ2*(k-1)) ≲ log (#worlds)`.

**Assessment.** Bounded work. The only unknown is `two_point_error_lower`, and
it is a first-year-analysis inequality. Do this one first: it converts the
chain's upper bounds into a *rate*.

---

## Item 1 — total regret  *(blocked on a modelling choice, not a theorem)*

### Already compiled

* recommendation half: `D6ActualDoublingEpochRisk.actual_doubling_recommendation_bound`
* acquisition identity: `D6ActualMultiEpochRisk.doubling_acquisition_cost`,
  `4*d*r0*E + d*L0*(2^E - 1)`
* discovery-failure term: `eta d r0 = 2*d*exp(-r0/128)`

### The choice that must be made explicit

`d*L0*(2^E - 1) = Θ(T)` counts the cyclic design's queries **while deployed**.
Whether that is regret depends entirely on the benchmark:

* benchmark = an oracle that knows `A` and runs the *same* cyclic design
  → it pays the identical term → it cancels → total regret is `O(log T)`;
* benchmark = an oracle that pays nothing to measure
  → it does not cancel → total regret is `Θ(T)`.

Neither is more correct; the paper must state which it uses. Writing `O(log T)`
without stating it is exactly the overclaim the module docstrings warn about.

### Assembly obligation, once chosen

```lean
theorem actual_total_regret_bound (q : ℕ) (hq : 8 ≤ q) (j : I (2*q+1)) ... :
    E[acquisitionRegret] + E[∑ s < E, L s * R s] + E[misidentificationLoss]
      ≤ (benchmark-dependent expression)
```

**Assessment.** Small once the choice is made. Half a day of Lean.

---

## Item 2 — growing-q constants and learning the phase interval  *(new mathematics)*

Existing: `D6LocalCurvatureLimit`, `D6GrowingPhaseThreeRemainder`,
`D6CriticalScaleRemainder` (`≤ 64/q²` for `q ≥ 8`).

Missing, precisely:

1. a remainder estimate **uniform in `q`**, not one constant per `q`;
2. a procedure that *learns* `phaseInterval q` rather than receiving
   `hm : mu ∈ phaseInterval q` as a hypothesis — every current theorem takes it
   as given;
3. control of the error when the estimate crosses an interval boundary.

Obligation (2) is the one that is not proof engineering: it needs a confidence
sequence for `mu` whose width is uniform in `q`, and nothing in the corpus
currently produces one.

**Assessment.** Genuine research. Prerequisite for Item 3.

---

## Item 3 — termination and expected Γ rate  *(depends on Item 2)*

`D6ExpectedStoppingEpoch`'s own docstring names the three gaps; they are
reproduced here because they are the target list:

1. **`settleIndex` is not a stopping time.** It is the index after which no
   epoch is ever bad again, so it looks into the future and is not adapted to
   the natural filtration. Concrete fix, which changes the theorem's content and
   needs a new estimate: replace it by the first epoch after which the
   certificate is stable over a verified window of length `w`,
   ```lean
   def settleTime (w : ℕ) : Sample J → ℕ∞ := fun x =>
     sInf {s | ∀ t < w, certificateAgrees (s+t) x}
   ```
   which *is* measurable with respect to the filtration, then bound
   `E[settleTime w]`.
2. **Nothing about allocation inside good epochs.** The multi-epoch bridge
   bounds the recommendation loss given a correct label; it says nothing about
   the tracking error of the allocation actually played.
3. **Nothing about phase-interval crossings.** This is Item 2 obligation (3).

**Assessment.** (1) is bounded and worth doing on its own — an adapted stopping
time with a finite expectation is a real result. (2) and (3) are research and
(3) cannot start before Item 2.

---

## Order

1. `LeanMinimaxRiskBridgeV1` (written, uncompiled) — the hinge both halves need.
2. `two_point_error_lower` — the one missing inequality.
3. Item 4 chain. This is the item that upgrades the work from bounds to a rate.
4. Item 1 modelling choice, then assembly.
5. Item 3 obligation (1): the adapted stopping time.
6. Item 2, then Item 3 (2)–(3).

Steps 1–5 are bounded. Step 6 is not, and no estimate of it is offered here.

---

# REVISION, same day: the Item 2 / Item 3 assessment above was too pessimistic

## Pin bump does not deliver Pinsker

Checked against upstream `master` (`a95cac3a`) by tree listing, not by memory.
`Mathlib/InformationTheory/` there contains exactly the same four
KullbackLeibler files as the current pin. There is no Pinsker, no
total-variation/KL comparison, no Hellinger, no Rényi anywhere in Mathlib.
`two_point_error_lower` must be proved in this corpus regardless of pin.

A bump *would* deliver `Mathlib/Probability/Decision/Risk/RiskIncrease.lean`
(new on master): `riskIncrease ℓ P π`, the risk saved by having the observation
rather than discarding it, with data-processing inequalities
`riskIncrease_comp_le` and `riskIncrease_map_le`. That is a direct formalisation
of "what does a discovery query buy", i.e. of the acquisition side of Item 1,
and is worth the bump on its own.

## Item 2(b) is bounded work, not research

The earlier claim that "nothing in the corpus produces a confidence sequence
uniform in `q`" is withdrawn. The ingredients are all present:

* `D6CyclicPhaseLaw.estimate_law` gives the cyclic estimator an actual
  **Gaussian law** `gaussianReal mu v`, not merely a moment bound. Gaussian
  gives exponential tails directly; Chebyshev is not needed.
* `D6CyclicMeanSquare.cyclic_clipped_mean_square` gives the variance
  **explicitly in `q`**: `|C|/(L*q^4)`. Uniformity in `q` is therefore by
  construction, not something to be arranged.
* `LeanDyadicCertifiedStoppingV1` already carries the dyadic union-bound pattern
  the corpus uses for time-uniform statements.

Composing these gives a confidence sequence of width
`O(sqrt(|C|*log(1/δ)/(L*q^4)))` valid at all epochs simultaneously, with
explicit `q`-scaling. Obligation:

```lean
theorem cyclic_confidence_sequence (q L0 : ℕ) (delta : ℝ) (hd : 0 < delta) ... :
    P {x | ∀ s, |clip lo hi (estimate q (L0*2^s) (proj s x)) - mu| ≤ width q L0 s delta}
      ≥ 1 - ENNReal.ofReal delta
```

## Item 3(2) is a composition, not research

`D6AllocationTrackingStability.allocation_one_sided` is already proved:

```
allocationValue A j mu E w ≤ allocationValue A j mu E v
                              + informationCap q * (∑ e ∈ E, |w e - v e|)
```

That is an L1 Lipschitz modulus for the allocation value, with
`informationCap q = (q+2)^2/2` explicit. `LeanFiniteAllocationTrackerMeasurable`
supplies measurability and causality of the played schedule, and the tracker
experiment reports `0/720` violations of `formal_bound` across ten frozen seeds.

What is missing is only a bound on `∑ e ∈ E, |w e - v e|` in terms of the
estimation error of `mu` — and that is exactly what Item 2(b) delivers. So
Item 3(2) is a composition of two proved statements once the confidence
sequence exists.

## Item 3(3) = Item 2(c), and the fix is standard

A crossing of a phase-interval boundary is only dangerous if it is undetected.
With a confidence sequence in hand the standard device applies: widen the
working interval by the confidence width, so that a possible crossing is
*detected* rather than silently wrong, and charge the widened interval to the
remainder. No new mathematics.

## Corrected dependency structure

```
        Item 2(b)  confidence sequence      <-- THE single hinge, bounded
         /    |    \
   2(a)   2(c)=3(3)  3(2)                   <-- all compositions of proved statements
   
   3(1)  adapted stopping time              <-- independent, bounded
   4     discovery lower bound              <-- independent, bounded except two_point_error_lower
   1     total regret                       <-- independent, blocked only on the benchmark choice
```

Every box is bounded. The earlier statement that Item 2 could not be made
bounded was wrong, and the error was reading the module names instead of the
modules: `estimate_law` being a Gaussian *law* rather than a moment bound is the
fact that changes the assessment, and it is in the file.
