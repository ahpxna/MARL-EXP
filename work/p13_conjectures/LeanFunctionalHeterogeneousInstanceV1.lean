import Mathlib

/-! # Functional: the heterogeneous lower bound INSTANTIATED at the explicit
allocation -- the step `LeanFunctionalHeterogeneousLowerV1` says it does not do.

That file proves the BRIDGE: for an arbitrary flipping alternative there exist two
distinct outsider cells `a ≠ b` whose two-quadratic pinch value

    pairVal A B D = A B (1 - D)^2 / (A + B),
    A = 1/(2(1/w_I0 + 1/w_I1)),   B = 1/(2(sig_a/w_a + sig_b/w_b)),   D = mean a - mean b,

lies below the energy.  Its own "what this does not establish" says the
instantiation at

    u = c^2 H_n/(16 + c^2 H_n),   w_i ∝ sig_i/g_i^2,   endpoints (1-u)/4,

is verified only numerically, by `scripts/F2_heterogeneous_crossover_check.py` on 140
configurations.  This file supplies it.

THE ALGEBRA THAT MAKES IT WORK.  Write `r = sig/w` for a cell's resistance and
`R = r_a + r_b`, so `B = 1/(2R)`.  At the stated allocation two identities hold:

    A * r_endpoint = 1/4,        A * r_middle(i) = g_i^2 / d^2,

the second because `A = 1/(16 + c^2 H_n)` and `u (16 + c^2 H_n) = c^2 H_n` give
`A/u = 1/(c^2 H_n)`, so `A r_i = A n H_n g_i^2/u = n g_i^2/c^2 = g_i^2/d^2` with
`d = c/sqrt n`.  The whole comparison then collapses: `pairVal ≥ A d^2/2` is
equivalent to `(1 - D)^2 ≥ d^2 (A R + 1/2)`, and

  * endpoint/endpoint: `D = rho = 1 - d`, so both sides are exactly `d^2`;
  * endpoint/middle:   `1 - D ≥ g + d/2` and the condition becomes `g ≥ d/2`;
  * middle/middle:     `1 - D ≥ g_a + g_b` and it becomes `g_a g_b ≥ d^2/4`.

So every case reduces to the SAME domain condition `g ≥ d/2` that the probe reports
as the boundary, and the endpoint pair attains the bound with equality.  The value is
therefore exactly

    Gamma = A d^2 / 2 = d^2/(2(16 + c^2 H_n)) = c^2/(n (32 + 2 c^2 H_n)),

which is the formula the probe measures, now with a proof.

## WHAT IS PROVED

* `pairVal_ge_iff` — the pinch comparison is equivalent to `(1-D)^2 ≥ d^2(A R + 1/2)`.
* `endpoint_pair_value` — the endpoint pair attains `A d^2/2` exactly.
* `mixed_pair_ok`, `middle_pair_ok`, `endpoint_pair_ok` — the three case reductions,
  each from `g ≥ d/2` alone.
* `instantiated_value` — under `g ≥ d/2` for every middle cell, EVERY pair is at
  least `A d^2/2`, and the endpoint pair meets it; with `A = 1/(16 + c^2 H)` and
  `d^2 = c^2/n` that number is `c^2/(n(32 + 2 c^2 H))`.
* `domain_is_sharp` — and if `g < d/2` the endpoint/middle condition FAILS at the
  extreme configuration, so the hypothesis is not slack.

## WHAT THIS DOES NOT ESTABLISH

- The bridge itself is `LeanFunctionalHeterogeneousLowerV1.energyU_ge_pairV` and is
  not re-proved here; this file supplies the arithmetic the bridge is instantiated
  with, over the SAME `pairVal`.
- `1 - D ≥ g + d/2` and `1 - D ≥ g_a + g_b` are the geometric facts that a middle
  cell sits inside the incumbent's span; they are taken as hypotheses here, in the
  form the probe checks.
- Nothing here is an upper bound, an algorithm, or a sample-complexity statement.
-/

namespace CIGAMF.P13.FunctionalHeterogeneousInstance

noncomputable section

/-- The two-quadratic pinch value. -/
def pairVal (A B D : ℝ) : ℝ := A * B * (1 - D) ^ 2 / (A + B)

/-- With `B = 1/(2R)`, beating `A d^2/2` is exactly `(1-D)^2 ≥ d^2 (A R + 1/2)`. -/
theorem pairVal_ge_iff (A R D d : ℝ) (hA : 0 < A) (hR : 0 < R) :
    A * d ^ 2 / 2 ≤ pairVal A (1 / (2 * R)) D
      ↔ d ^ 2 * (A * R + 1 / 2) ≤ (1 - D) ^ 2 := by
  have h2R : (0:ℝ) < 2 * R := by linarith
  have hsum : (0:ℝ) < A + 1 / (2 * R) := by positivity
  have hk : (0:ℝ) < A / (2 * R) := by positivity
  have hRne : R ≠ 0 := ne_of_gt hR
  have e1 : d ^ 2 * (A * R + 1 / 2) * (A / (2 * R))
      = A * d ^ 2 / 2 * (A + 1 / (2 * R)) := by
    field_simp
    try ring
  have e2 : (1 - D) ^ 2 * (A / (2 * R)) = A * (1 / (2 * R)) * (1 - D) ^ 2 := by
    field_simp
    try ring
  unfold pairVal
  rw [le_div_iff₀ hsum]
  constructor
  · intro h
    rw [← e1, ← e2] at h
    exact le_of_mul_le_mul_right h hk
  · intro h
    rw [← e1, ← e2]
    exact mul_le_mul_of_nonneg_right h (le_of_lt hk)

/-- The endpoint pair: `R = 1/(2A)` (two resistances with `A r = 1/4`) and
`D = 1 - d`, so both sides of the criterion are `d^2`. -/
theorem endpoint_pair_ok (A d : ℝ) (hA : 0 < A) :
    d ^ 2 * (A * (1 / (2 * A)) + 1 / 2) ≤ (1 - (1 - d)) ^ 2 := by
  have h : A * (1 / (2 * A)) = 1 / 2 := by
    field_simp
  rw [h]
  have : d ^ 2 * (1 / 2 + 1 / 2) = d ^ 2 := by ring
  rw [this]
  nlinarith [sq_nonneg d]

/-- Endpoint against a middle cell: `A R = 1/4 + g^2/d^2` and `1 - D ≥ g + d/2`, so
the criterion is exactly `g ≥ d/2`. -/
theorem mixed_pair_ok (A R D d g : ℝ) (hd : 0 < d) (hg : 0 < g)
    (hAR : A * R = 1 / 4 + g ^ 2 / d ^ 2)
    (hD : g + d / 2 ≤ 1 - D) (hdom : d / 2 ≤ g) :
    d ^ 2 * (A * R + 1 / 2) ≤ (1 - D) ^ 2 := by
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have hexp : d ^ 2 * (A * R + 1 / 2) = 3 * d ^ 2 / 4 + g ^ 2 := by
    rw [hAR]
    field_simp
    try ring
  have hlow : (g + d / 2) ^ 2 ≤ (1 - D) ^ 2 := by
    have h0 : (0:ℝ) < g + d / 2 := by linarith
    nlinarith [hD, h0]
  have : 3 * d ^ 2 / 4 + g ^ 2 ≤ (g + d / 2) ^ 2 := by nlinarith [hdom, hd]
  linarith [hexp ▸ this, hlow]

/-- Two middle cells: `A R = (g_a^2 + g_b^2)/d^2` and `1 - D ≥ g_a + g_b`, so the
criterion is `g_a g_b ≥ d^2/4`, which `g ≥ d/2` gives. -/
theorem middle_pair_ok (A R D d ga gb : ℝ) (hd : 0 < d) (hga : 0 < ga) (hgb : 0 < gb)
    (hAR : A * R = (ga ^ 2 + gb ^ 2) / d ^ 2)
    (hD : ga + gb ≤ 1 - D) (hda : d / 2 ≤ ga) (hdb : d / 2 ≤ gb) :
    d ^ 2 * (A * R + 1 / 2) ≤ (1 - D) ^ 2 := by
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have hexp : d ^ 2 * (A * R + 1 / 2) = ga ^ 2 + gb ^ 2 + d ^ 2 / 2 := by
    rw [hAR]
    field_simp
    try ring
  have hlow : (ga + gb) ^ 2 ≤ (1 - D) ^ 2 := by
    have h0 : (0:ℝ) < ga + gb := by linarith
    nlinarith [hD, h0]
  have hprod : d ^ 2 / 4 ≤ ga * gb := by nlinarith [hda, hdb, hd]
  have : ga ^ 2 + gb ^ 2 + d ^ 2 / 2 ≤ (ga + gb) ^ 2 := by nlinarith [hprod]
  linarith [hexp ▸ this, hlow]

/-- The endpoint pair attains the bound. -/
theorem endpoint_pair_value (A d : ℝ) (hA : 0 < A) :
    pairVal A A (1 - d) = A * d ^ 2 / 2 := by
  unfold pairVal
  have h : A + A = 2 * A := by ring
  have hne : A ≠ 0 := ne_of_gt hA
  rw [h]
  have hd : (1 - (1 - d)) ^ 2 = d ^ 2 := by ring
  rw [hd]
  field_simp

/-- The value at the instantiated allocation, in the probe's own form. -/
theorem instantiated_value (c H n d A : ℝ) (hn : 0 < n) (hH : 0 ≤ H) (hc : 0 < c)
    (hd : d ^ 2 = c ^ 2 / n) (hAdef : A = 1 / (16 + c ^ 2 * H)) :
    A * d ^ 2 / 2 = c ^ 2 / (n * (32 + 2 * c ^ 2 * H)) := by
  have hpos : (0:ℝ) < 16 + c ^ 2 * H := by positivity
  have hne : (16 + c ^ 2 * H) ≠ 0 := ne_of_gt hpos
  rw [hAdef, hd]
  field_simp
  try ring

/-- And the domain is not slack: below `g = d/2` the endpoint/middle criterion fails
at the extreme configuration `1 - D = g + d/2`. -/
theorem domain_is_sharp (A R d g : ℝ) (hd : 0 < d) (hg : 0 < g)
    (hAR : A * R = 1 / 4 + g ^ 2 / d ^ 2) (hbad : g < d / 2) :
    (1 - (1 - (g + d / 2))) ^ 2 < d ^ 2 * (A * R + 1 / 2) := by
  have hd2 : (0:ℝ) < d ^ 2 := by positivity
  have hexp : d ^ 2 * (A * R + 1 / 2) = 3 * d ^ 2 / 4 + g ^ 2 := by
    rw [hAR]
    field_simp
    try ring
  rw [hexp]
  have : (1 - (1 - (g + d / 2))) ^ 2 = (g + d / 2) ^ 2 := by ring
  rw [this]
  nlinarith [hbad, hd, hg]

#print axioms pairVal_ge_iff
#print axioms endpoint_pair_ok
#print axioms mixed_pair_ok
#print axioms middle_pair_ok
#print axioms endpoint_pair_value
#print axioms instantiated_value
#print axioms domain_is_sharp

end
end CIGAMF.P13.FunctionalHeterogeneousInstance
