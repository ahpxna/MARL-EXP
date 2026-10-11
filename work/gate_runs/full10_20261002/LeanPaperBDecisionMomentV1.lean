import «LeanPaperBFamilyLawV1»

/-!
# Paper B: the second moment of the decision probe, computed from the observation law

On the latent family `F_{u,v}(z) = 3 u z₁ - 2 z₂ - 2 z₃ + v χ_r(z_tail)` the decision probe is
`g = z₁` (`decH`, `decT r`), and the observation is `Y = F_{u,v}(Z) + h g(Z) + ξ` with `Z`
uniform on the sign cube and `ξ ~ N(0, σ²)`. Its law is `famLaw σ h u v decH (decT r)`
(`LeanPaperBFamilyLawV1`), the uniform mixture of `N(mean(p), σ²)` over the `8 · 2^r` latent
patterns `p`.

**What is proved here.**
* `integral_sq_gaussianReal`: `∫ x² dN(m, v) = m² + v`.
* `famLaw_integral_sq`: the second moment of any probe's law is the pattern average of
  `mean(p)² + σ²`.
* `decision_second_moment_famLaw`: for `u² = v² = 1` and every tail length `r`,
  `∫ y² d(famLaw σ h u v decH (decT r)) = 18 + σ² + 6 u h + h²`. The integral is the law's own
  integral: the Gaussian second moments are Mathlib's, the pattern average is computed on the
  cube (`dm_head_sq_sum`, `dm_head_sum`, `dm_parity_sq`), and no polynomial is written down by
  hand.
* `decision_gap_famLaw`: the two values of `u` sit exactly `12 h` apart, for every `v = ±1`,
  `σ`, `h` and `r`. `decision_gap_via_rates` derives the same gap through the arithmetic lemma
  `decision_moment_gap` of `LeanPaperBRatesV1`, whose two inputs are now computed integrals.
* `decision_second_moment_channel`: the same moment for the channel's observation law at any
  real query that uses the decision probe (`obsLawC_famChan`), with `u = uOf w`.

The hypotheses `u² = 1`, `v² = 1` are met by `u, v ∈ {1, -1}`, which is how the worlds are
built (`uOf`, `vOf`, `dm_uOf_sq`, `dm_vOf_sq`).
-/

namespace CIGAMF.P13.PaperBDecisionMoment

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBRates CIGAMF.P13.PaperBWorlds CIGAMF.P13.PaperBChannelPair
open CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityGap CIGAMF.P13.PaperBFamilyChannel
open CIGAMF.P13.PaperBFamilyLaw

/-! ## 1. One Gaussian -/

/-- **The second moment of a real Gaussian.** -/
theorem integral_sq_gaussianReal (m : ℝ) (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂gaussianReal m v = m ^ 2 + v := by
  have h := variance_eq_sub (μ := gaussianReal m v) (X := id)
    (memLp_id_gaussianReal' 2 (by norm_num))
  rw [variance_id_gaussianReal] at h
  simp only [Pi.pow_apply, id_eq, integral_id_gaussianReal] at h
  linarith

theorem integrable_sq_gaussianReal (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal m v) :=
  (memLp_id_gaussianReal' 2 (by norm_num)).integrable_sq

/-! ## 2. The mixture -/

/-- **The second moment of a probe's law** is the pattern average of `mean² + σ²`. -/
theorem famLaw_integral_sq {r : ℕ} (σ h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) :
    ∫ y, y ^ 2 ∂famLaw σ h u v aH aT
      = ∑ p : (Fin 3 → Bool) × (Fin r → Bool),
          (famW r).toReal * (famMean h u v aH aT p ^ 2 + σ ^ 2) := by
  unfold famLaw
  rw [integral_finsetSum_measure (fun p _ =>
    (integrable_sq_gaussianReal _ _).smul_measure (famW_ne_top r))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_measure, integral_sq_gaussianReal, var2_coe, smul_eq_mul]

/-! ## 3. Sums over the sign cube -/

theorem dm_cube_prod {n : ℕ} (F : Fin n → Bool → ℝ) :
    ∑ z : Fin n → Bool, ∏ i, F i (z i) = ∏ i, (F i true + F i false) := by
  rw [← Fintype.prod_sum]
  simp [Fintype.sum_bool]

/-- One sign averages to zero. -/
theorem dm_cube_sgn {n : ℕ} (i : Fin n) : ∑ z : Fin n → Bool, sgnB (z i) = 0 := by
  have h : ∀ z : Fin n → Bool, sgnB (z i) = ∏ k, (if k = i then sgnB (z k) else 1) := by
    intro z
    simp [Finset.prod_ite_eq']
  rw [Finset.sum_congr rfl fun z _ => h z, dm_cube_prod (fun k b => if k = i then sgnB b else 1)]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [sgnB])

/-- Two different signs are uncorrelated. -/
theorem dm_cube_sgn_mul {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∑ z : Fin n → Bool, sgnB (z i) * sgnB (z j) = 0 := by
  have h : ∀ z : Fin n → Bool, sgnB (z i) * sgnB (z j)
      = ∏ k, ((if k = i then sgnB (z k) else 1) * (if k = j then sgnB (z k) else 1)) := by
    intro z
    rw [Finset.prod_mul_distrib]
    simp [Finset.prod_ite_eq']
  rw [Finset.sum_congr rfl fun z _ => h z,
    dm_cube_prod (fun k b => (if k = i then sgnB b else 1) * (if k = j then sgnB b else 1))]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [sgnB, hij])

theorem dm_cube_one (n : ℕ) : ∑ _z : Fin n → Bool, (1 : ℝ) = 2 ^ n := by
  simp

theorem dm_card (r : ℕ) : (Fintype.card (Fin r → Bool) : ℝ) = 2 ^ r := by
  simp

/-- The head of the world averages to zero. -/
theorem dm_head_sum (c0 c1 c2 : ℝ) :
    ∑ zh : Fin 3 → Bool, (c0 * sgnB (zh 0) + c1 * sgnB (zh 1) + c2 * sgnB (zh 2)) = 0 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, dm_cube_sgn, dm_cube_sgn, dm_cube_sgn]
  ring

/-- **Parseval for the head**: the mean square is the sum of the squared coefficients. -/
theorem dm_head_sq_sum (c0 c1 c2 : ℝ) :
    ∑ zh : Fin 3 → Bool, (c0 * sgnB (zh 0) + c1 * sgnB (zh 1) + c2 * sgnB (zh 2)) ^ 2
      = 8 * (c0 ^ 2 + c1 ^ 2 + c2 ^ 2) := by
  have hexp : ∀ zh : Fin 3 → Bool,
      (c0 * sgnB (zh 0) + c1 * sgnB (zh 1) + c2 * sgnB (zh 2)) ^ 2
        = (c0 ^ 2 + c1 ^ 2 + c2 ^ 2) * 1 + (2 * c0 * c1) * (sgnB (zh 0) * sgnB (zh 1))
          + (2 * c0 * c2) * (sgnB (zh 0) * sgnB (zh 2))
          + (2 * c1 * c2) * (sgnB (zh 1) * sgnB (zh 2)) := by
    intro zh
    have h0 := sgnB_sq (zh 0)
    have h1 := sgnB_sq (zh 1)
    have h2 := sgnB_sq (zh 2)
    linear_combination c0 ^ 2 * h0 + c1 ^ 2 * h1 + c2 ^ 2 * h2
  rw [Finset.sum_congr rfl fun zh _ => hexp zh]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    dm_cube_one, dm_cube_sgn_mul 0 1 (by decide), dm_cube_sgn_mul 0 2 (by decide),
    dm_cube_sgn_mul 1 2 (by decide)]
  ring

/-- The tail parity squares to one. -/
theorem dm_parity_sq {r : ℕ} (z : Fin r → Bool) : parity z ^ 2 = 1 := by
  unfold parity
  rw [← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [sq]; exact sgnB_sq (z i)

/-- A double sum of `A x + B x C y` separates. -/
theorem dm_double_sum {α β : Type*} [Fintype α] [Fintype β] (A B : α → ℝ) (C : β → ℝ) :
    ∑ x, ∑ y, (A x + B x * C y) = (Fintype.card β : ℝ) * ∑ x, A x + (∑ x, B x) * ∑ y, C y := by
  rw [Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ## 4. The decision probe -/

/-- The mean at a latent pattern under the decision probe. -/
theorem dm_mean_dec {r : ℕ} (h u v : ℝ) (zh : Fin 3 → Bool) (z : Fin r → Bool) :
    famMean h u v decH (decT r) (zh, z)
      = ((3 * u + h) * sgnB (zh 0) + (-2) * sgnB (zh 1) + (-2) * sgnB (zh 2)) + v * parity z := by
  simp [famMean, headC, shiftOf, tailB, decT, decH, Fin.sum_univ_three]
  ring

/-- **The decision second moment, computed from the observation law.** -/
theorem decision_second_moment_famLaw (r : ℕ) (σ h u v : ℝ) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) :
    ∫ y, y ^ 2 ∂famLaw σ h u v decH (decT r) = 18 + σ ^ 2 + 6 * u * h + h ^ 2 := by
  rw [famLaw_integral_sq, Fintype.sum_prod_type, famW_toReal]
  have hterm : ∀ (zh : Fin 3 → Bool) (z : Fin r → Bool),
      (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r * (famMean h u v decH (decT r) (zh, z) ^ 2 + σ ^ 2)
        = (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r
            * (((3 * u + h) * sgnB (zh 0) + (-2) * sgnB (zh 1) + (-2) * sgnB (zh 2)) ^ 2
              + σ ^ 2 + v ^ 2)
          + ((2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r * (2 * v)
              * ((3 * u + h) * sgnB (zh 0) + (-2) * sgnB (zh 1) + (-2) * sgnB (zh 2)))
            * parity z := by
    intro zh z
    rw [dm_mean_dec]
    have hp := dm_parity_sq z
    linear_combination ((2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r * v ^ 2) * hp
  rw [Finset.sum_congr rfl fun zh _ => Finset.sum_congr rfl fun z _ => hterm zh z, dm_double_sum,
    dm_card]
  have hB : ∑ zh : Fin 3 → Bool, (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r * (2 * v)
      * ((3 * u + h) * sgnB (zh 0) + (-2) * sgnB (zh 1) + (-2) * sgnB (zh 2)) = 0 := by
    rw [← Finset.mul_sum, dm_head_sum, mul_zero]
  have hA : ∑ zh : Fin 3 → Bool, (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r
      * (((3 * u + h) * sgnB (zh 0) + (-2) * sgnB (zh 1) + (-2) * sgnB (zh 2)) ^ 2
        + σ ^ 2 + v ^ 2)
      = (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r
          * (8 * ((3 * u + h) ^ 2 + (-2) ^ 2 + (-2) ^ 2) + 8 * σ ^ 2 + 8 * v ^ 2) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, dm_head_sq_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hA, hB, zero_mul, add_zero]
  have h2 : (2 : ℝ) ^ r * (2 : ℝ)⁻¹ ^ r = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (two_ne_zero), one_pow]
  linear_combination ((2 : ℝ)⁻¹ ^ 3
      * (8 * ((3 * u + h) ^ 2 + (-2) ^ 2 + (-2) ^ 2) + 8 * σ ^ 2 + 8 * v ^ 2)) * h2
    + 9 * hu + hv

/-- **The two values of `u` sit `12 h` apart**, for every `v = ±1`, `σ`, `h` and tail length. -/
theorem decision_gap_famLaw (r : ℕ) (σ h v : ℝ) (hv : v ^ 2 = 1) :
    ∫ y, y ^ 2 ∂famLaw σ h 1 v decH (decT r) - ∫ y, y ^ 2 ∂famLaw σ h (-1) v decH (decT r)
      = 12 * h := by
  rw [decision_second_moment_famLaw r σ h 1 v (by norm_num) hv,
    decision_second_moment_famLaw r σ h (-1) v (by norm_num) hv]
  ring

/-- The same gap, through the arithmetic lemma of `LeanPaperBRatesV1`: its two inputs are the
computed second moments. -/
theorem decision_gap_via_rates (r : ℕ) (σ h v : ℝ) (hv : v ^ 2 = 1) :
    ∫ y, y ^ 2 ∂famLaw σ h 1 v decH (decT r) - ∫ y, y ^ 2 ∂famLaw σ h (-1) v decH (decT r)
      = 12 * h := by
  rw [decision_second_moment_famLaw r σ h 1 v (by norm_num) hv,
    decision_second_moment_famLaw r σ h (-1) v (by norm_num) hv]
  exact decision_moment_gap h σ

/-! ## 5. The channel -/

theorem dm_uOf_sq (w : Bool × Bool) : uOf w ^ 2 = 1 := by
  unfold uOf; rw [sq]; exact sgnB_sq w.1

theorem dm_vOf_sq (w : Bool × Bool) : vOf w ^ 2 = 1 := by
  unfold vOf; rw [sq]; exact sgnB_sq w.2

/-- **The channel's decision query**: at any real query `q` that uses the decision probe, the
second moment of the channel's observation law is `18 + σ² + 6 u h + h²` with `u = uOf w`. -/
theorem decision_second_moment_channel {r k : ℕ} (σ h : ℝ) (hσ : 0 < σ)
    (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ) (w : Bool × Bool)
    (q : Fin (k + 1)) (hq : (q : ℕ) ≠ 0) (hH : aH q = decH) (hT : aT q = decT r) :
    ∫ y, y ^ 2 ∂obsLawC (famChan σ h hσ aH aT) w q = 18 + σ ^ 2 + 6 * uOf w * h + h ^ 2 := by
  rw [obsLawC_famChan σ h hσ aH aT w q hq, hH, hT]
  exact decision_second_moment_famLaw r σ h (uOf w) (vOf w) (dm_uOf_sq w) (dm_vOf_sq w)

#print axioms integral_sq_gaussianReal
#print axioms famLaw_integral_sq
#print axioms dm_head_sq_sum
#print axioms decision_second_moment_famLaw
#print axioms decision_gap_famLaw
#print axioms decision_gap_via_rates
#print axioms decision_second_moment_channel

end CIGAMF.P13.PaperBDecisionMoment
