import «LeanPaperBDecisionMomentV1»

/-!
# Paper B: the identification moment gap, on the observation law itself

`identification_moment_gap_computed` (`LeanPaperBRatesV1`) computes the `v`-gap of the
`(r+1)`-st moment on the tail cube, with the head frozen to a constant `A` and no noise. The
observation of the latent family under the averaged tail probe (`tailH`, `tailT r`) has a
uniform random head `A(z_head) = 3u z₁ - 2 z₂ - 2 z₃` and Gaussian noise `N(0, σ²)`. Its law is
`famLaw σ h u v tailH (tailT r)`.

**What is proved here, for every `σ`, `h`, `u` and every tail length `r`.**
* `gauss_moment`: `∫ x^j dN(m, v) = Σ_k C(j,k) m^(j-k) ∫ x^k dN(0, v)`. This covers Gaussian
  moments of every order.
* `famLaw_moment`: the `j`-th moment of any probe's law is the pattern average of that
  polynomial in the pattern mean.
* `tail_moment_diff`: the `v`-difference of the `j`-th moment is
  `2^{-3-r} Σ_k C(j,k) E[ξ^k] Σ_head Σ_tail [(A + h g + χ)^(j-k) - (A + h g - χ)^(j-k)]`.
* `cube_diff_vanish`: on the tail cube, `Σ_z [(A + h g + χ)^n - (A + h g - χ)^n] = 0` for every
  `n ≤ r` and every constant `A`.
* **Orders covered.**
  - `tail_moment_vanish`: for every `j ≤ r` (so `j = 0, 1, …, r`) the `v`-difference of
    `E[Y^j]` under the law is exactly `0`.
  - `tail_moment_gap`: for `r ≥ 1` and `j = r + 1` it is exactly
    `2 (r+1) r!/r^r h^r`, the value `identification_moment_gap_computed` gives on the
    frozen-head, noiseless cube. It does not depend on `σ`, on `u`, or on the head.
  - `tail_moment_first_nonzero`: that value is nonzero when `h ≠ 0`, so `r + 1` is the first
    order at which the two values of `v` differ.
  - Orders `j ≥ r + 2` are not treated.
* `tail_moment_vanish_channel`, `tail_moment_gap_channel`: the same statements for the
  channel's observation law at any real query that uses the tail probe.
-/

namespace CIGAMF.P13.PaperBTailMoment

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBRates CIGAMF.P13.PaperBWorlds CIGAMF.P13.PaperBChannelPair
open CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityGap CIGAMF.P13.PaperBFamilyChannel
open CIGAMF.P13.PaperBFamilyLaw CIGAMF.P13.PaperBDecisionMoment
open CIGAMF.P13.UnifiedQueryOrder (chiS HasDeg moment_vanishes_below_order)

/-! ## 1. Gaussian moments of every order -/

theorem integrable_pow_gaussian (m : ℝ) (v : ℝ≥0) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal m v) := by
  have h : MemLp (id : ℝ → ℝ) (n : ℝ≥0∞) (gaussianReal m v) :=
    memLp_id_gaussianReal' (n : ℝ≥0∞) (ENNReal.natCast_ne_top n)
  refine (h.integrable_norm_pow').mono' (continuous_pow n).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  simp [norm_pow]

/-- The `k`-th moment of the centred noise. -/
noncomputable def gm (σ : ℝ) (k : ℕ) : ℝ := ∫ x, x ^ k ∂gaussianReal 0 (var2 σ)

theorem gm_zero (σ : ℝ) : gm σ 0 = 1 := by
  simp [gm]

/-- **Every moment of a shifted Gaussian** is a fixed polynomial in the shift. -/
theorem gauss_moment (m : ℝ) (v : ℝ≥0) (j : ℕ) :
    ∫ x, x ^ j ∂gaussianReal m v
      = ∑ k ∈ range (j + 1), (j.choose k : ℝ) * m ^ (j - k) * ∫ x, x ^ k ∂gaussianReal 0 v := by
  have hmap : gaussianReal m v = (gaussianReal 0 v).map (· + m) := by
    rw [gaussianReal_map_add_const, zero_add]
  rw [hmap, integral_map (by fun_prop) (continuous_pow j).aestronglyMeasurable]
  simp_rw [add_pow]
  rw [integral_finsetSum _ (fun k _ =>
    ((integrable_pow_gaussian 0 v k).mul_const _).mul_const _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_const, integral_mul_const]
  ring

/-- **Every moment of a probe's law** is the pattern average of that polynomial. -/
theorem famLaw_moment {r : ℕ} (j : ℕ) (σ h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) :
    ∫ y, y ^ j ∂famLaw σ h u v aH aT
      = ∑ p : (Fin 3 → Bool) × (Fin r → Bool), (famW r).toReal *
          ∑ k ∈ range (j + 1), (j.choose k : ℝ) * famMean h u v aH aT p ^ (j - k) * gm σ k := by
  unfold famLaw
  rw [integral_finsetSum_measure (fun p _ =>
    (integrable_pow_gaussian _ _ j).smul_measure (famW_ne_top r))]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_measure, gauss_moment, smul_eq_mul]
  rfl

/-! ## 2. The tail probe's mean -/

/-- The head of the world, frozen at a head pattern. -/
noncomputable def hd (u : ℝ) (zh : Fin 3 → Bool) : ℝ :=
  3 * u * sgnB (zh 0) - 2 * sgnB (zh 1) - 2 * sgnB (zh 2)

theorem tail_mean {r : ℕ} (h u v : ℝ) (zh : Fin 3 → Bool) (z : Fin r → Bool) :
    famMean h u v tailH (tailT r) (zh, z)
      = hd u zh + h * gavg z + v * chiS (Finset.univ : Finset (Fin r)) z := by
  have e1 : headC u h tailH zh = hd u zh := by
    simp [headC, hd, tailH, Fin.sum_univ_three]
  have e2 : shiftOf (tailB h (tailT r)) z = h * gavg z := by
    unfold shiftOf tailB tailT gavg
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [sgnB, CIGAMF.P13.UnifiedQueryOrder.sgn]
    ring
  have e3 : parity z = chiS (Finset.univ : Finset (Fin r)) z := by
    simp only [parity, chiS, sgnB, CIGAMF.P13.UnifiedQueryOrder.sgn]
  show headC u h tailH zh + v * parity z + shiftOf (tailB h (tailT r)) z = _
  rw [e1, e2, e3]
  ring

/-! ## 3. The cube -/

/-- **Below order `r + 1` the tail cube cannot see `v`.** -/
theorem cube_diff_vanish {r : ℕ} (A h : ℝ) (n : ℕ) (hn : n ≤ r) :
    ∑ z : Fin r → Bool, ((A + h * gavg z + chiS (Finset.univ : Finset (Fin r)) z) ^ n
      - (A + h * gavg z - chiS (Finset.univ : Finset (Fin r)) z) ^ n) = 0 := by
  classical
  have hpt : ∀ z : Fin r → Bool,
      (A + h * gavg z + chiS (Finset.univ : Finset (Fin r)) z) ^ n
        - (A + h * gavg z - chiS (Finset.univ : Finset (Fin r)) z) ^ n
      = ∑ i ∈ range (n + 1), ((n.choose i : ℝ) * (1 - (-1) ^ (n - i)))
          * (chiS (Finset.univ : Finset (Fin r)) z * (A + h * gavg z) ^ i) := by
    intro z
    rw [v_difference_pointwise (A + h * gavg z) (chiS (Finset.univ : Finset (Fin r)) z)
      (chi_pm_one z) n]
    have e1 := add_pow (A + h * gavg z) 1 n
    have e2 := add_pow (A + h * gavg z) (-1) n
    rw [show A + h * gavg z - 1 = A + h * gavg z + -1 by ring, e1, e2,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [one_pow]
    ring
  rw [Finset.sum_congr rfl fun z _ => hpt z, Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.mul_sum]
  by_cases hir : i < r
  · have hvan : ∑ z : Fin r → Bool,
        chiS (Finset.univ : Finset (Fin r)) z * (A + h * gavg z) ^ i = 0 :=
      moment_vanishes_below_order (hasDeg_affine A h) (by simpa using hir)
    rw [hvan, mul_zero]
  · have hin : i = n := by
      have := Finset.mem_range.mp hi
      omega
    subst hin
    simp

/-! ## 4. The law -/

/-- **The `v`-difference of every moment**, reduced to the cube. -/
theorem tail_moment_diff {r : ℕ} (j : ℕ) (σ h u : ℝ) :
    ∫ y, y ^ j ∂famLaw σ h u 1 tailH (tailT r) - ∫ y, y ^ j ∂famLaw σ h u (-1) tailH (tailT r)
      = (famW r).toReal * ∑ k ∈ range (j + 1), (j.choose k : ℝ) * gm σ k *
          ∑ zh : Fin 3 → Bool, ∑ z : Fin r → Bool,
            ((hd u zh + h * gavg z + chiS (Finset.univ : Finset (Fin r)) z) ^ (j - k)
              - (hd u zh + h * gavg z - chiS (Finset.univ : Finset (Fin r)) z) ^ (j - k)) := by
  rw [famLaw_moment, famLaw_moment, ← Finset.sum_sub_distrib]
  have hpt : ∀ p : (Fin 3 → Bool) × (Fin r → Bool),
      (famW r).toReal * (∑ k ∈ range (j + 1),
          (j.choose k : ℝ) * famMean h u 1 tailH (tailT r) p ^ (j - k) * gm σ k)
        - (famW r).toReal * (∑ k ∈ range (j + 1),
          (j.choose k : ℝ) * famMean h u (-1) tailH (tailT r) p ^ (j - k) * gm σ k)
      = ∑ k ∈ range (j + 1), (famW r).toReal * ((j.choose k : ℝ) * gm σ k)
          * (famMean h u 1 tailH (tailT r) p ^ (j - k)
            - famMean h u (-1) tailH (tailT r) p ^ (j - k)) := by
    intro p
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [Finset.sum_congr rfl fun p _ => hpt p, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  have hin : ∀ (zh : Fin 3 → Bool) (z : Fin r → Bool),
      famMean h u 1 tailH (tailT r) (zh, z) ^ (j - k)
        - famMean h u (-1) tailH (tailT r) (zh, z) ^ (j - k)
      = (hd u zh + h * gavg z + chiS (Finset.univ : Finset (Fin r)) z) ^ (j - k)
        - (hd u zh + h * gavg z - chiS (Finset.univ : Finset (Fin r)) z) ^ (j - k) := by
    intro zh z
    rw [tail_mean, tail_mean]
    ring_nf
  simp_rw [hin]
  ring

/-- **Orders `0, 1, …, r`: the law cannot see `v`.** -/
theorem tail_moment_vanish {r : ℕ} (j : ℕ) (hj : j ≤ r) (σ h u : ℝ) :
    ∫ y, y ^ j ∂famLaw σ h u 1 tailH (tailT r) - ∫ y, y ^ j ∂famLaw σ h u (-1) tailH (tailT r)
      = 0 := by
  rw [tail_moment_diff]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun k hk => ?_)
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun zh _ => cube_diff_vanish _ h _ ?_)
  have := Finset.mem_range.mp hk
  omega

/-- **Order `r + 1`: the gap is the frozen-head, noiseless value.** It does not depend on the
noise level, on `u`, or on the head. -/
theorem tail_moment_gap {r : ℕ} (hr : 0 < r) (σ h u : ℝ) :
    ∫ y, y ^ (r + 1) ∂famLaw σ h u 1 tailH (tailT r)
        - ∫ y, y ^ (r + 1) ∂famLaw σ h u (-1) tailH (tailT r)
      = 2 * ((r : ℝ) + 1) * ((r.factorial : ℝ) / (r : ℝ) ^ r) * h ^ r := by
  rw [tail_moment_diff, Finset.sum_range_succ']
  have hrest : ∑ k ∈ range (r + 1), ((r + 1).choose (k + 1) : ℝ) * gm σ (k + 1) *
      ∑ zh : Fin 3 → Bool, ∑ z : Fin r → Bool,
        ((hd u zh + h * gavg z + chiS (Finset.univ : Finset (Fin r)) z) ^ (r + 1 - (k + 1))
          - (hd u zh + h * gavg z - chiS (Finset.univ : Finset (Fin r)) z) ^ (r + 1 - (k + 1)))
      = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun zh _ => cube_diff_vanish _ h _ ?_)
    omega
  rw [hrest, zero_add]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, gm_zero]
  set G := 2 * ((r : ℝ) + 1) * ((r.factorial : ℝ) / (r : ℝ) ^ r) * h ^ r with hG
  have h2 : (2 : ℝ) ^ r ≠ 0 := by positivity
  have hcube : ∀ zh : Fin 3 → Bool, ∑ z : Fin r → Bool,
      ((hd u zh + h * gavg z + chiS (Finset.univ : Finset (Fin r)) z) ^ (r + 1)
        - (hd u zh + h * gavg z - chiS (Finset.univ : Finset (Fin r)) z) ^ (r + 1))
      = 2 ^ r * G := by
    intro zh
    have hgap := identification_moment_gap_computed hr (hd u zh) h
    rw [div_eq_iff h2] at hgap
    rw [Finset.sum_sub_distrib, hgap, hG]
    ring
  rw [Finset.sum_congr rfl fun zh _ => hcube zh, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul, famW_toReal]
  have hinv : (2 : ℝ) ^ r * (2 : ℝ)⁻¹ ^ r = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
  push_cast
  linear_combination ((2 : ℝ)⁻¹ ^ 3 * 2 ^ 3 * G) * hinv

/-- **`r + 1` is the first order that separates the two values of `v`.** -/
theorem tail_moment_first_nonzero {r : ℕ} (hr : 0 < r) (σ h u : ℝ) (hh : h ≠ 0) :
    (∀ j ≤ r, ∫ y, y ^ j ∂famLaw σ h u 1 tailH (tailT r)
        - ∫ y, y ^ j ∂famLaw σ h u (-1) tailH (tailT r) = 0)
      ∧ ∫ y, y ^ (r + 1) ∂famLaw σ h u 1 tailH (tailT r)
        - ∫ y, y ^ (r + 1) ∂famLaw σ h u (-1) tailH (tailT r) ≠ 0 := by
  refine ⟨fun j hj => tail_moment_vanish j hj σ h u, ?_⟩
  rw [tail_moment_gap hr σ h u]
  exact identification_gap_ne_zero r hr h hh

/-! ## 5. The channel -/

theorem tail_law_channel {r k : ℕ} (σ h : ℝ) (hσ : 0 < σ)
    (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ) (b vb : Bool)
    (q : Fin (k + 1)) (hq : (q : ℕ) ≠ 0) (hH : aH q = tailH) (hT : aT q = tailT r) :
    obsLawC (famChan σ h hσ aH aT) (b, vb) q
      = famLaw σ h (sgnB b) (if vb then 1 else -1) tailH (tailT r) := by
  rw [obsLawC_famChan σ h hσ aH aT (b, vb) q hq, hH, hT]
  rfl

/-- The channel's tail query: orders `0, …, r` do not see `v`. -/
theorem tail_moment_vanish_channel {r k : ℕ} (σ h : ℝ) (hσ : 0 < σ)
    (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ) (b : Bool)
    (q : Fin (k + 1)) (hq : (q : ℕ) ≠ 0) (hH : aH q = tailH) (hT : aT q = tailT r)
    (j : ℕ) (hj : j ≤ r) :
    ∫ y, y ^ j ∂obsLawC (famChan σ h hσ aH aT) (b, true) q
      - ∫ y, y ^ j ∂obsLawC (famChan σ h hσ aH aT) (b, false) q = 0 := by
  rw [tail_law_channel σ h hσ aH aT b true q hq hH hT,
    tail_law_channel σ h hσ aH aT b false q hq hH hT]
  simpa using tail_moment_vanish j hj σ h (sgnB b)

/-- The channel's tail query: order `r + 1` separates `v` by the exact value. -/
theorem tail_moment_gap_channel {r k : ℕ} (hr : 0 < r) (σ h : ℝ) (hσ : 0 < σ)
    (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ) (b : Bool)
    (q : Fin (k + 1)) (hq : (q : ℕ) ≠ 0) (hH : aH q = tailH) (hT : aT q = tailT r) :
    ∫ y, y ^ (r + 1) ∂obsLawC (famChan σ h hσ aH aT) (b, true) q
      - ∫ y, y ^ (r + 1) ∂obsLawC (famChan σ h hσ aH aT) (b, false) q
      = 2 * ((r : ℝ) + 1) * ((r.factorial : ℝ) / (r : ℝ) ^ r) * h ^ r := by
  rw [tail_law_channel σ h hσ aH aT b true q hq hH hT,
    tail_law_channel σ h hσ aH aT b false q hq hH hT]
  simpa using tail_moment_gap hr σ h (sgnB b)

#print axioms gauss_moment
#print axioms famLaw_moment
#print axioms cube_diff_vanish
#print axioms tail_moment_diff
#print axioms tail_moment_vanish
#print axioms tail_moment_gap
#print axioms tail_moment_first_nonzero
#print axioms tail_moment_vanish_channel
#print axioms tail_moment_gap_channel

end CIGAMF.P13.PaperBTailMoment
