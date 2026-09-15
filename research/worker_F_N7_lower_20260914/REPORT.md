# F-N7-Lower — closed. 19 clean audits, receipt accepted.

Module: `work/p13_conjectures/LeanFunctionalCrossoverLowerV1.lean`
Receipt: `lean_exit=0`, source hash unchanged
(`2dd47802c2cf8084e88c60dacbfebfb99fa2afe135b5c8dbe5902dcd0d1d1b78`), `.olean`
strictly newer than source, 19 audits, every one on
`{propext, Classical.choice, Quot.sound}`, `accepted=True`.
Probe: `scripts/F1_crossover_lower_check.py`, 81 exact-`Fraction` configurations.

The supervisor's unblocking observation was right and it is what made this cheap:
**no symmetry theorem is needed for a matching lower bound.** `crossover_upper`
already quantifies over every allocation; a lower bound only has to exhibit ONE
allocation and show every flipping alternative is expensive at it.

---

## PROVED

### F1 — the actual-alternative bridge (`energy_ge_pairV`)

This is the step that was prose. For an arbitrary flipping alternative — arbitrary
incumbent means, arbitrary outsider means, **extrema anywhere** — there exist two
distinct outsider cells `a ≠ b` with

    pairV (w I0) (w I1) (w a) (w b) (meanO a - meanO b)  ≤  energy.

The acceptance condition the supervisor set ("stated directly on the inf over
real alternatives, not on `min J_EE (min J_EM J_MM)`") is met: the pair is
produced from the ALTERNATIVE'S OWN argmax and argmin, so nothing is assumed
about which cells carry the extrema. Extraction handles the degenerate case where
argmax = argmin (the range is then zero, every cell is equal, so any second index
serves).

Three ingredients, all proved:
* `two_point` — `w1 w2 (x-y)^2 ≤ (w1 x^2 + w2 y^2)(w1+w2)`, from `(w1 x + w2 y)^2 ≥ 0`.
* `pinch` — `A B (u+v)^2 ≤ (A u^2 + B v^2)(A+B)`, from `(A u - B v)^2 ≥ 0`.
* `meanO_diff_lt_one` — mean differences never reach `1` when `rho < 1`, which is
  what makes the `z ≥ 1` branch go through.

The proof splits on the alternative's new outsider range `z`:
`z < 1` uses both halves and the pinch with `u = 1-z`, `v = z-D`;
`z ≥ 1` uses the outsider half alone. `D` may be negative — the pinch identity is
valid for all real `u, v`, so no sign case is needed.

### F2 — the explicit allocation (`explicit_pairV_ge`, `explicit_allocation_lower`)

At `p = q = 2/S`, `u = n d^2/S`, `S = 4 + n d^2` (so each incumbent cell and each
outsider endpoint carries `1/S`, each middle cell `d^2/S`; `wExp_total` proves the
total mass is exactly `1`), every pair value is at least `L = d^2/(8 S)`.
Three pair types, four sign cases, only `0 < d ≤ 1` used:

    J_EE = L,    J_MM = L · 2/(1+d^2),    J_EM = L · (1+d)^2/(1+3 d^2),   min = L.

The probe re-derives these three identities in exact rational arithmetic from the
same harmonic-half formulas the N7 evaluator uses: **81/81 configurations, no
mismatch**, and `L ≤ U ≤ 2L` in every one.

### The sandwich, and the sharp ratio

`crossover_sandwich` (`0 < d ≤ 1`, `n ≥ 2`): the allocation is feasible, forces
every alternative to cost at least `L`, and every allocation admits one costing at
most `2 L`. Only `kappa ≤ 1/4` is used.

`crossover_sandwich_sharp` on `(1+d)^2 ≤ 2` (i.e. `d ≤ sqrt 2 - 1`,
`rho ≥ 2 - sqrt 2`), where `kappa (1-d) = (1+d)^2/8` exactly (`kappa_small`):

    L  ≤  value  ≤  (1+d)^2 · L,      L = d^2/(8(4 + n d^2)).

**The excess is exactly `n d^2 (2d + d^2) / (4(1+d)^2 + n d^2) ≤ 2d + d^2`, so the
ratio tends to `1` as `d → 0` UNIFORMLY IN `n`.** Measured: `U/L = 1.00001` at
`n=16, d=1/100` and `1.00049` at `n=1024, d=1/100`.

That uniformity is the substantive part. One finite formula `d^2/(8(4 + n d^2))`
governs all three regimes — `n d^2 → 0`, `n d^2 → lambda`, `n d^2 → infinity` —
simultaneously, rather than three separately-proved limits.

---

## WHAT THIS DOES NOT ESTABLISH

- **`Gamma_n` is not defined in the module.** `explicit_allocation_lower` is "one
  allocation, all alternatives"; `crossover_upper` is "all allocations, one
  alternative". Read together they bracket the sup-inf, but the sup-inf itself is
  not formalised, so the sandwich is stated as the pair of inequalities actually
  proved, not as a bound on a `Gamma`.
- **No limit is taken.** `n Gamma_n → kappa` and `n Gamma_n → c^2/(8(c^2+4))` are
  still not theorems. The sharp ratio gives the leading order on any `d → 0`
  sequence; it says nothing about the next term, so the claimed `n^(-1/2)`
  correction is NOT proved.
- The sharp ratio holds only on `(1+d)^2 ≤ 2`. Off that region only the factor `2`
  is available and `kappa` takes its other branch.
- Weights are assumed strictly positive; degenerate faces are excluded, not handled.
- `energy` is an information quantity. **Nothing here concerns an algorithm, a
  stopping rule, or sample complexity**, and `Gamma_n` may not be called the sample
  complexity of any running procedure.
- Independent of this file, the supervisor's standing correction applies: the panel
  has C_lucb at median N = 20.996 against C_anytime 29.884, so C_lucb is the
  comparator, and "beats uniform" is not a claim to lead with.

## Collisions to keep in the write-up

BAI on micro-observables: Huang–Ajallooeian–Szepesvári–Müller, 2017. Unknown
variance: Jourdan–Degenne–Kaufmann, 2023. Neither the max-min allocation nor the
Gaussian KL profile is novel. What is defensible here is the extrema/capacity
crossover with MATCHING finite bounds and an explicit allocation, and the
uniformity of `(1+d)^2` across the three `n d^2` regimes.
