import «LeanPaperBParityWorldV1»
import «LeanPaperBCriticalGameV1»

/-!
# Paper B: the critical constants of the parity channel

Query `j ≥ 1` of the parity channel has density
`p_v(y) = 2^{-j} Σ_z φ_σ(y - v χ(z) - (h/j) S(z))`, `v = ±1` the mask, `χ(z) = ∏ z_ℓ`,
`S(z) = Σ z_ℓ` (`pdens`, `LeanPaperBParityChiSqV1`). This module proves the leading-order
expansion of its information and the resulting critical constants.

* `pdens_sub`: `p_+ - p_- = Fd`, the cube average `2^{-j} Σ_z χ(z) g(S(z) h / j)` with
  `g(u) = φ_σ(y - 1 - u) - φ_σ(y + 1 - u)`.
* `iter_Fd`, `taylor_Fd`: its `k`-th derivative in `h` at `0` is
  `2^{-j} Σ_z χ(z) (S(z)/j)^k g^{(k)}(0)`, which vanishes for `k < j` and equals
  `j! j^{-j} g^{(j)}(0)` at `k = j`, by the parity cancellation
  (`parity_moment_lt`, `parity_moment_eq`). So the Taylor polynomial of order `j` is
  `h^j a_j(y)`.
* **`lead_limit`**: `(p_+ - p_-)(y)/h^j → a_j(y)` as `h → 0` (`h ≠ 0`), with
  `a_j(y) = j^{-j} g^{(j)}(0)`; `aj_eq`: `a_j(y) = (-1)^j j^{-j}(φ_σ^{(j)}(y-1) - φ_σ^{(j)}(y+1))`,
  the paper's formula. This is Mathlib's Taylor theorem (`taylor_tendsto`).
* `pdens_zero`: at `h = 0` both masks give `p_0 = (φ_σ(·-1) + φ_σ(·+1))/2`.
* **`chi_limit`**: `χ²_j(h)/h^{2j} → ∫ a_j²/p_0 = 2 c_j` as `h → 0⁺`, for either ordering of
  the masks. Dominated convergence, with the envelope `envUp²/envLo` of `parity_chiSq_le`.
* **`kl_limit`**: `KL_j(h)/h^{2j} → c_j = (1/2) ∫ a_j²/p_0`, either ordering. The pointwise
  step is `(1+r)log(1+r) - r = r²/2 + O(r³)` (from `Real.abs_log_sub_add_sum_range_le`), the
  domination `0 ≤ p log(p/q) - (p - q) ≤ (p-q)²/q`.
* **`cj_pos`**: `c_j ≥ Gc_j²/8 > 0`, from the per-query lower bound `par_chi_visible`
  (`LeanPaperBParityWorldV1`).
* **`parity_critical_game`**: for identification at world `w` (paper index `w + 1`), with
  `κ_q(λ; h)` the per-query KL of the parity channel between worlds `w` and `λ`
  (`kappa_eq_channel`), the rescaled game converges:
  `h^{-2s} max_α min_{λ ≠ w} Σ_q α_q κ_q(λ; h) → c_s`, `s = min(w + 1, m - 1)`.
  So `G* = c_w` for paper worlds `w ≤ m - 1` and `G* = c_{m-1}` for `w = m`. It is
  `critical_limit` fed by `expansion_hyps` (`LeanPaperBCriticalGameV1`).
-/

namespace CIGAMF.P13.PaperBParityCritical

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBRates CIGAMF.P13.PaperBWorlds CIGAMF.P13.PaperBChannelPair
open CIGAMF.P13.PaperBPairRate CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityChiSq
open CIGAMF.P13.PaperBVisible CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBParityChannel
open CIGAMF.P13.PaperBParityDecoder CIGAMF.P13.PaperBParityWorld CIGAMF.P13.PaperBCriticalGame

/-! ## 1. The cube, in real coordinates -/

theorem sgnR_abs (b : Bool) : |sgnR b| = 1 := by cases b <;> simp [sgnR]

theorem chrR_pm {j : ℕ} (z : Fin j → Bool) : chrR z = 1 ∨ chrR z = -1 := by
  have h : |chrR z| = 1 := by
    unfold chrR
    rw [Finset.abs_prod]
    simp [sgnR_abs]
  exact (abs_eq (zero_le_one' ℝ)).mp h

theorem sgnR_eq_neg_sg (b : Bool) : sgnR b = -((sg b : ℤ) : ℝ) := by
  cases b <;> simp [sgnR, sg]

theorem moment_cast (j k : ℕ) :
    ∑ z : Fin j → Bool, chrR z * csumR z ^ k
      = (-1) ^ (j + k) * ((∑ z : Fin j → Bool, (∏ l, sg (z l)) * (∑ l, sg (z l)) ^ k : ℤ) : ℝ) := by
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  unfold chrR csumR
  simp_rw [sgnR_eq_neg_sg]
  rw [Finset.prod_neg, Finset.sum_neg_distrib, neg_pow, Finset.card_univ, Fintype.card_fin]
  ring

/-- **The parity cancellation, real form**: orders below `j` vanish. -/
theorem mom_lt {j k : ℕ} (hk : k < j) : ∑ z : Fin j → Bool, chrR z * csumR z ^ k = 0 := by
  rw [moment_cast, parity_moment_lt j k hk]
  simp

/-- **Order `j` survives**: `Σ_z χ(z) S(z)^j = 2^j j!`. -/
theorem mom_eq (j : ℕ) : ∑ z : Fin j → Bool, chrR z * csumR z ^ j = 2 ^ j * j.factorial := by
  rw [moment_cast, parity_moment_eq]
  push_cast
  rw [← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-! ## 2. The density difference as a cube average -/

/-- The noise density `φ_σ`. -/
noncomputable def phi (σ x : ℝ) : ℝ := gaussianPDFReal 0 (var2 σ) x

theorem gpdf_eq (σ μ y : ℝ) : gaussianPDFReal μ (var2 σ) y = phi σ (y - μ) := by
  unfold phi gaussianPDFReal
  simp

/-- `g(u) = φ_σ(y - 1 - u) - φ_σ(y + 1 - u)`. -/
noncomputable def gfun (σ y u : ℝ) : ℝ := phi σ (y - 1 - u) - phi σ (y + 1 - u)

/-- The density difference of the two masks, as a function of the signal level `h`. -/
noncomputable def Fd (j : ℕ) (σ y h : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ j * ∑ z : Fin j → Bool, chrR z * gfun σ y (csumR z / j * h)

theorem mask_term (σ y s h : ℝ) (j : ℕ) (c : ℝ) (hc : c = 1 ∨ c = -1) :
    phi σ (y - (1 * c + h / j * s)) - phi σ (y - (-1 * c + h / j * s))
      = c * gfun σ y (s / j * h) := by
  unfold gfun
  rcases hc with rfl | rfl <;> ring_nf

/-- **`p_+ - p_-` is the cube average `Fd`.** -/
theorem pdens_sub (j : ℕ) (σ h y : ℝ) : pdens j 1 h σ y - pdens j (-1) h σ y = Fd j σ y h := by
  unfold pdens Fd
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [gpdf_eq, gpdf_eq]
  unfold obsMean
  exact mask_term σ y (csumR z) h j (chrR z) (chrR_pm z)

theorem contDiff_gfun (σ y : ℝ) (n : ℕ) : ContDiff ℝ n (gfun σ y) := by
  unfold gfun phi gaussianPDFReal
  fun_prop

/-- **The derivatives of `Fd` at `h = 0`.** -/
theorem iter_Fd (j : ℕ) (σ y : ℝ) (k : ℕ) :
    iteratedDeriv k (Fd j σ y) 0
      = (2 : ℝ)⁻¹ ^ j * (iteratedDeriv k (gfun σ y) 0 * (1 / (j : ℝ)) ^ k
          * ∑ z : Fin j → Bool, chrR z * csumR z ^ k) := by
  have hg := contDiff_gfun σ y k
  have hF : Fd j σ y = fun h => (2 : ℝ)⁻¹ ^ j *
      ∑ z : Fin j → Bool, chrR z * gfun σ y (csumR z / j * h) := rfl
  rw [hF, iteratedDeriv_const_mul_field]
  congr 1
  rw [iteratedDeriv_fun_sum (f := fun z h => chrR z * gfun σ y (csumR z / j * h))
    (fun z _ => (contDiff_const.mul (hg.comp (contDiff_const.mul contDiff_id))).contDiffAt)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul hg]
  simp only [mul_zero]
  ring

/-- The leading coefficient `a_j(y) = j^{-j} g^{(j)}(0)`. -/
noncomputable def aj (j : ℕ) (σ y : ℝ) : ℝ := (1 / (j : ℝ)) ^ j * iteratedDeriv j (gfun σ y) 0

/-- **The Taylor polynomial of `Fd` of order `j` is `h^j a_j`.** -/
theorem taylor_Fd (j : ℕ) (hj : 0 < j) (σ y h : ℝ) :
    taylorWithinEval (Fd j σ y) j Set.univ 0 h = h ^ j * aj j σ y := by
  rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_eq_zero]
  · simp only [iteratedDerivWithin_univ, iter_Fd, mom_eq, sub_zero, smul_eq_mul, zero_add]
    unfold aj
    have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    have h2 : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
    have h2' : (2 : ℝ)⁻¹ ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
    field_simp
    first
      | linear_combination (h ^ j * iteratedDeriv j (gfun σ y) 0) * h2
      | linear_combination (h ^ j * iteratedDeriv j (gfun σ y) 0) * h2'
  · intro k hk
    have hk' : k < j := Finset.mem_range.mp hk
    simp only [iteratedDerivWithin_univ, iter_Fd, mom_lt hk', mul_zero, smul_zero]

/-- **The leading coefficient of `p_+ - p_-`**: `(p_+ - p_-)(y)/h^j → a_j(y)` as `h → 0`. -/
theorem lead_limit (j : ℕ) (hj : 0 < j) (σ y : ℝ) :
    Tendsto (fun h => Fd j σ y h / h ^ j) (𝓝[≠] 0) (𝓝 (aj j σ y)) := by
  have hFd : ContDiff ℝ j (Fd j σ y) := by
    unfold Fd gfun phi gaussianPDFReal
    fun_prop
  have hT := Real.taylor_tendsto (f := Fd j σ y) (x₀ := 0) (n := j) convex_univ (Set.mem_univ 0)
    hFd.contDiffOn
  rw [nhdsWithin_univ] at hT
  have hT' := (hT.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).const_add (aj j σ y)
  rw [add_zero] at hT'
  refine hT'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := hh
  rw [taylor_Fd j hj σ y h, sub_zero]
  have hp : h ^ j ≠ 0 := pow_ne_zero _ hh0
  field_simp
  ring

/-- **The paper's formula for `a_j`.** -/
theorem aj_eq (j : ℕ) (σ y : ℝ) :
    aj j σ y = (-1) ^ j * (1 / (j : ℝ)) ^ j
      * (iteratedDeriv j (phi σ) (y - 1) - iteratedDeriv j (phi σ) (y + 1)) := by
  unfold aj gfun
  have h1 := contDiff_gfun σ y j
  have hp : ContDiff ℝ j (phi σ) := by unfold phi gaussianPDFReal; fun_prop
  have hA : ContDiffAt ℝ j (fun u => phi σ (y - 1 - u)) 0 :=
    (hp.comp (contDiff_const.sub contDiff_id)).contDiffAt
  have hB : ContDiffAt ℝ j (fun u => phi σ (y + 1 - u)) 0 :=
    (hp.comp (contDiff_const.sub contDiff_id)).contDiffAt
  rw [iteratedDeriv_fun_sub hA hB]
  have e1 := congrFun (iteratedDeriv_comp_const_sub (n := j) (f := phi σ) (s := y - 1)) 0
  have e2 := congrFun (iteratedDeriv_comp_const_sub (n := j) (f := phi σ) (s := y + 1)) 0
  simp only [sub_zero, smul_eq_mul] at e1 e2
  rw [e1, e2]
  ring

/-! ## 3. The density at `h = 0` -/

/-- `p_0 = (φ_σ(· - 1) + φ_σ(· + 1)) / 2`. -/
noncomputable def p0 (σ y : ℝ) : ℝ := (phi σ (y - 1) + phi σ (y + 1)) / 2

theorem phi_pos (σ x : ℝ) (hσ : 0 < σ) : 0 < phi σ x :=
  gaussianPDFReal_pos _ _ _ (var2_ne_zero σ hσ)

theorem p0_pos (σ y : ℝ) (hσ : 0 < σ) : 0 < p0 σ y := by
  unfold p0; have := phi_pos σ (y - 1) hσ; have := phi_pos σ (y + 1) hσ; positivity

theorem mask_zero (σ y v c : ℝ) (hv : v = 1 ∨ v = -1) (hc : c = 1 ∨ c = -1) :
    phi σ (y - v * c) = (phi σ (y - 1) + phi σ (y + 1)) / 2
      + v * c * ((phi σ (y - 1) - phi σ (y + 1)) / 2) := by
  rcases hv with rfl | rfl <;> rcases hc with rfl | rfl <;> ring_nf

/-- **Both masks give `p_0` at `h = 0`.** -/
theorem pdens_zero (j : ℕ) (hj : 0 < j) (σ v y : ℝ) (hv : v = 1 ∨ v = -1) :
    pdens j v 0 σ y = p0 σ y := by
  unfold pdens
  have hterm : ∀ z : Fin j → Bool, gaussianPDFReal (obsMean j v 0 z) (var2 σ) y
      = p0 σ y + v * ((phi σ (y - 1) - phi σ (y + 1)) / 2) * chrR z := by
    intro z
    rw [gpdf_eq]
    unfold obsMean p0
    rw [zero_div, zero_mul, add_zero, mask_zero σ y v (chrR z) hv (chrR_pm z)]
    ring
  rw [Finset.sum_congr rfl fun z _ => hterm z, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h0 : ∑ z : Fin j → Bool, chrR z = 0 := by
    have := mom_lt (j := j) (k := 0) hj
    simpa using this
  rw [h0, mul_zero, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_mul]

theorem continuous_pdens_h (j : ℕ) (σ v y : ℝ) : Continuous fun h => pdens j v h σ y := by
  unfold pdens obsMean gaussianPDFReal
  fun_prop

theorem pdens_tendsto (j : ℕ) (hj : 0 < j) (σ v y : ℝ) (hv : v = 1 ∨ v = -1) :
    Tendsto (fun h => pdens j v h σ y) (𝓝[>] 0) (𝓝 (p0 σ y)) := by
  have := (continuous_pdens_h j σ v y).tendsto 0
  rw [pdens_zero j hj σ v y hv] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem lead_limit_pos (j : ℕ) (hj : 0 < j) (σ y : ℝ) :
    Tendsto (fun h => Fd j σ y h / h ^ j) (𝓝[>] 0) (𝓝 (aj j σ y)) :=
  (lead_limit j hj σ y).mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)

/-! ## 4. The envelope bounds, uniform in `0 < h ≤ 1` -/

/-- The envelope ratio `envUp² / envLo` at level `h₀ = 1`. -/
noncomputable def envR (j : ℕ) (σ y : ℝ) : ℝ :=
  envUp σ (0 + 1 + 1) j y ^ 2 / envLo σ (0 + 1 + 1) y

/-- The constant in front of the envelope ratio. -/
noncomputable def KE (j : ℕ) (σ : ℝ) : ℝ := 4 * ((1 / (j : ℝ)) ^ j) ^ 2 / Zc σ

theorem envR_integrable (j : ℕ) (σ : ℝ) (hσ : 0 < σ) : Integrable (envR j σ) :=
  envRatio_integrable σ (0 + 1 + 1) hσ (by norm_num) j

theorem abs_Fd_le (j : ℕ) (hj : 0 < j) (σ h y : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    |Fd j σ y h| ≤ (Zc σ)⁻¹ * (2 * ((h / j) ^ j * envUp σ (0 + 1 + 1) j y)) := by
  rw [← pdens_sub, pdens_diff, abs_mul, abs_of_pos (inv_pos.mpr (Zc_pos σ hσ))]
  exact mul_le_mul_of_nonneg_left (diff_envelope j hj σ h 1 hσ hh hh1 y)
    (inv_nonneg.mpr (Zc_pos σ hσ).le)

/-- **The rescaled `χ²` integrand is dominated by `KE · envR`.** -/
theorem chi_integrand_le (j : ℕ) (hj : 0 < j) (σ h y v : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hv : v = 1 ∨ v = -1) :
    (Fd j σ y h / h ^ j) ^ 2 / pdens j v h σ y ≤ KE j σ * envR j σ y := by
  have hZ := Zc_pos σ hσ
  have hlo := envLo_pos σ (0 + 1 + 1) y
  have hfl := pdens_floor j hj σ h 1 hσ hh.le hh1 v hv y
  have hflpos : 0 < (Zc σ)⁻¹ * envLo σ (0 + 1 + 1) y := mul_pos (inv_pos.mpr hZ) hlo
  have hhj : 0 < h ^ j := pow_pos hh j
  have hE0 : 0 ≤ envUp σ (0 + 1 + 1) j y := envUp_nonneg σ _ j y (by norm_num)
  have habs : |Fd j σ y h / h ^ j| ≤ (Zc σ)⁻¹ * (2 * ((1 / (j : ℝ)) ^ j
      * envUp σ (0 + 1 + 1) j y)) := by
    rw [abs_div, abs_of_pos hhj, div_le_iff₀ hhj]
    refine (abs_Fd_le j hj σ h y hσ hh.le hh1).trans (le_of_eq ?_)
    rw [div_pow, one_div, inv_pow]
    field_simp
  have hsq : (Fd j σ y h / h ^ j) ^ 2 ≤ ((Zc σ)⁻¹ * (2 * ((1 / (j : ℝ)) ^ j
      * envUp σ (0 + 1 + 1) j y))) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc (Fd j σ y h / h ^ j) ^ 2 / pdens j v h σ y
      ≤ ((Zc σ)⁻¹ * (2 * ((1 / (j : ℝ)) ^ j * envUp σ (0 + 1 + 1) j y))) ^ 2
          / ((Zc σ)⁻¹ * envLo σ (0 + 1 + 1) y) :=
        div_le_div₀ (sq_nonneg _) hsq hflpos hfl
    _ = KE j σ * envR j σ y := by
        unfold KE envR
        field_simp
        ring

/-! ## 5. The `χ²` limit -/

/-- The `χ²` integrand of query `j`, reference mask `v'`: `(p_+ - p_-)² / p_{v'}`. -/
noncomputable def chiInt (j : ℕ) (σ v' h y : ℝ) : ℝ := (Fd j σ y h) ^ 2 / pdens j v' h σ y

/-- The constant `c_j = (1/2) ∫ a_j² / p_0`. -/
noncomputable def cj (j : ℕ) (σ : ℝ) : ℝ := (1 / 2) * ∫ y, aj j σ y ^ 2 / p0 σ y

theorem continuous_Fd_y (j : ℕ) (σ h : ℝ) : Continuous fun y => Fd j σ y h := by
  have : (fun y => Fd j σ y h) = fun y => pdens j 1 h σ y - pdens j (-1) h σ y := by
    funext y; rw [pdens_sub]
  rw [this]
  exact (continuous_pdens j 1 h σ).sub (continuous_pdens j (-1) h σ)

theorem chi_rescale (j : ℕ) (σ v' h y : ℝ) :
    chiInt j σ v' h y / h ^ (2 * j) = (Fd j σ y h / h ^ j) ^ 2 / pdens j v' h σ y := by
  unfold chiInt
  rw [div_pow, ← pow_mul, mul_comm j 2]
  ring

theorem chi_pointwise (j : ℕ) (hj : 0 < j) (σ v' y : ℝ) (hσ : 0 < σ) (hv : v' = 1 ∨ v' = -1) :
    Tendsto (fun h => (Fd j σ y h / h ^ j) ^ 2 / pdens j v' h σ y) (𝓝[>] 0)
      (𝓝 (aj j σ y ^ 2 / p0 σ y)) :=
  ((lead_limit_pos j hj σ y).pow 2).div (pdens_tendsto j hj σ v' y hv) (p0_pos σ y hσ).ne'

/-- **The rescaled `χ²` converges to `2 c_j`.** -/
theorem chi_limit (j : ℕ) (hj : 0 < j) (σ v' : ℝ) (hσ : 0 < σ) (hv : v' = 1 ∨ v' = -1) :
    Tendsto (fun h => (∫ y, chiInt j σ v' h y) / h ^ (2 * j)) (𝓝[>] 0) (𝓝 (2 * cj j σ)) := by
  have hc : 2 * cj j σ = ∫ y, aj j σ y ^ 2 / p0 σ y := by unfold cj; ring
  rw [hc]
  have heq : (fun h => (∫ y, chiInt j σ v' h y) / h ^ (2 * j))
      = fun h => ∫ y, (Fd j σ y h / h ^ j) ^ 2 / pdens j v' h σ y := by
    funext h
    rw [← integral_div]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => chi_rescale j σ v' h y)
  rw [heq]
  refine tendsto_integral_filter_of_dominated_convergence (fun y => KE j σ * envR j σ y) ?_ ?_
    ((envR_integrable j σ hσ).const_mul _) ?_
  · refine Filter.Eventually.of_forall fun h => ?_
    exact ((((continuous_Fd_y j σ h).div_const _).pow 2).measurable.div
      (continuous_pdens j v' h σ).measurable).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
    refine Filter.Eventually.of_forall fun y => ?_
    have hpos := pdens_pos j hj σ h 1 hσ hh.1.le hh.2 v' hv y
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le)]
    exact chi_integrand_le j hj σ h y v' hσ hh.1 hh.2 hv
  · exact Filter.Eventually.of_forall fun y => chi_pointwise j hj σ v' y hσ hv

/-! ## 6. Densities: positivity at every level, integrability, unit mass -/

theorem pdens_pos' (j : ℕ) (σ v h y : ℝ) (hσ : 0 < σ) : 0 < pdens j v h σ y := by
  unfold pdens
  exact mul_pos (by positivity) (Finset.sum_pos
    (fun z _ => gaussianPDFReal_pos _ _ _ (var2_ne_zero σ hσ)) Finset.univ_nonempty)

theorem pdens_integrable (j : ℕ) (σ v h : ℝ) (hσ : 0 < σ) :
    Integrable (fun y => pdens j v h σ y) := by
  have hm : AEMeasurable (fun y => ENNReal.ofReal (pdens j v h σ y)) :=
    (continuous_pdens j v h σ).measurable.ennreal_ofReal.aemeasurable
  have hI := integrable_toReal_of_lintegral_ne_top hm
    (by rw [lintegral_pdens j v h σ hσ]; simp)
  refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (pdens_nonneg j v h σ y)]

theorem pdens_integral (j : ℕ) (σ v h : ℝ) (hσ : 0 < σ) : ∫ y, pdens j v h σ y = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => pdens_nonneg j v h σ y)
    (continuous_pdens j v h σ).aestronglyMeasurable, lintegral_pdens j v h σ hσ]
  simp

/-- The two admissible mask orderings. -/
def MaskPair (v v' : ℝ) : Prop := (v = 1 ∧ v' = -1) ∨ (v = -1 ∧ v' = 1)

theorem maskPair_v' {v v' : ℝ} (h : MaskPair v v') : v' = 1 ∨ v' = -1 := by
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inr h
  · exact Or.inl h

theorem diff_sq (j : ℕ) (σ h y : ℝ) {v v' : ℝ} (hvv : MaskPair v v') :
    (pdens j v h σ y - pdens j v' h σ y) ^ 2 = Fd j σ y h ^ 2 := by
  rcases hvv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [pdens_sub]
  · rw [← neg_sub, neg_sq, pdens_sub]

theorem chiInt_integrable (j : ℕ) (hj : 0 < j) (σ v' h : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hv : v' = 1 ∨ v' = -1) : Integrable (fun y => chiInt j σ v' h y) := by
  have hb : Integrable (fun y => h ^ (2 * j) * (KE j σ * envR j σ y)) :=
    ((envR_integrable j σ hσ).const_mul _).const_mul _
  refine hb.mono' ((((continuous_Fd_y j σ h).pow 2).measurable.div
    (continuous_pdens j v' h σ).measurable).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun y => ?_
  have hp := pdens_pos' j σ v' h y hσ
  have hle := chi_integrand_le j hj σ h y v' hσ hh hh1 hv
  have hr := chi_rescale j σ v' h y
  have hhj : 0 < h ^ (2 * j) := pow_pos hh _
  rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ chiInt j σ v' h y from
    div_nonneg (sq_nonneg _) hp.le)]
  have hle' : chiInt j σ v' h y / h ^ (2 * j) ≤ KE j σ * envR j σ y := by rw [hr]; exact hle
  have hsplit : chiInt j σ v' h y = h ^ (2 * j) * (chiInt j σ v' h y / h ^ (2 * j)) := by
    field_simp
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left hle' hhj.le

/-! ## 7. The KL limit -/

/-- The KL integrand of query `j`, masks `v ‖ v'`. -/
noncomputable def klInt (j : ℕ) (σ v v' h y : ℝ) : ℝ :=
  pdens j v h σ y * Real.log (pdens j v h σ y / pdens j v' h σ y)

/-- **The per-query KL divergence** of the parity query `j` between masks `v` and `v'`. -/
noncomputable def parKL (j : ℕ) (σ v v' h : ℝ) : ℝ := ∫ y, klInt j σ v v' h y

theorem kl_pt_bounds (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    0 ≤ p * Real.log (p / q) - (p - q) ∧ p * Real.log (p / q) - (p - q) ≤ (p - q) ^ 2 / q := by
  have hpq : 0 < p / q := div_pos hp hq
  constructor
  · have h1 := Real.one_sub_inv_le_log_of_pos hpq
    rw [inv_div] at h1
    have h2 : p * (1 - q / p) ≤ p * Real.log (p / q) := mul_le_mul_of_nonneg_left h1 hp.le
    have e : p * (1 - q / p) = p - q := by field_simp
    linarith
  · have h1 := Real.log_le_sub_one_of_pos hpq
    have h2 : p * Real.log (p / q) ≤ p * (p / q - 1) := mul_le_mul_of_nonneg_left h1 hp.le
    have e : p * (p / q - 1) - (p - q) = (p - q) ^ 2 / q := by field_simp
    linarith

/-- `(1+r) log(1+r) - r = r²/2 + O(r³)`. -/
theorem log_cubic (r : ℝ) (hr : |r| ≤ 1 / 2) :
    |(1 + r) * Real.log (1 + r) - r - r ^ 2 / 2| ≤ 4 * |r| ^ 3 := by
  have hx : |(-r)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hx 2
  have e : (∑ i ∈ Finset.range 2, (-r) ^ (i + 1) / ((i : ℝ) + 1)) + Real.log (1 - -r)
      = Real.log (1 + r) - (r - r ^ 2 / 2) := by
    simp [Finset.sum_range_succ]
    ring
  rw [e, abs_neg] at h
  set E := Real.log (1 + r) - (r - r ^ 2 / 2) with hE
  have hr0 := abs_nonneg r
  have hden : 1 / 2 ≤ 1 - |r| := by linarith
  have hE2 : |E| ≤ 2 * |r| ^ 3 := by
    refine h.trans ?_
    rw [div_le_iff₀ (by linarith)]
    have h3 : |r| ^ (2 + 1) = |r| ^ 3 := by norm_num
    rw [h3]
    have := mul_le_mul_of_nonneg_left hden (pow_nonneg hr0 3)
    nlinarith [pow_nonneg hr0 3]
  have hid : (1 + r) * Real.log (1 + r) - r - r ^ 2 / 2 = -(r ^ 3 / 2) + (1 + r) * E := by
    rw [hE]; ring
  rw [hid]
  have h1r : |1 + r| ≤ 3 / 2 := by
    rw [abs_le] at hr ⊢; constructor <;> linarith
  have hA : |-(r ^ 3 / 2)| = |r| ^ 3 / 2 := by
    rw [abs_neg, abs_div, abs_pow]; norm_num
  calc |-(r ^ 3 / 2) + (1 + r) * E| ≤ |-(r ^ 3 / 2)| + |(1 + r) * E| := abs_add_le _ _
    _ = |r| ^ 3 / 2 + |1 + r| * |E| := by rw [hA, abs_mul]
    _ ≤ |r| ^ 3 / 2 + 3 / 2 * (2 * |r| ^ 3) := by
        have := mul_le_mul h1r hE2 (abs_nonneg _) (by norm_num)
        linarith
    _ ≤ 4 * |r| ^ 3 := by nlinarith [pow_nonneg hr0 3]

theorem klInt_integrable (j : ℕ) (hj : 0 < j) (σ v v' h : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hvv : MaskPair v v') : Integrable (fun y => klInt j σ v v' h y) := by
  have hb : Integrable (fun y => chiInt j σ v' h y
      + |pdens j v h σ y - pdens j v' h σ y|) :=
    (chiInt_integrable j hj σ v' h hσ hh hh1 (maskPair_v' hvv)).add
      ((pdens_integrable j σ v h hσ).sub (pdens_integrable j σ v' h hσ)).abs
  refine hb.mono' (((continuous_pdens j v h σ).measurable.mul
    (((continuous_pdens j v h σ).measurable.div
      (continuous_pdens j v' h σ).measurable).log)).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun y => ?_
  have hp := pdens_pos' j σ v h y hσ
  have hq := pdens_pos' j σ v' h y hσ
  obtain ⟨b0, b1⟩ := kl_pt_bounds _ _ hp hq
  have hc : (pdens j v h σ y - pdens j v' h σ y) ^ 2 / pdens j v' h σ y = chiInt j σ v' h y := by
    unfold chiInt; rw [diff_sq j σ h y hvv]
  rw [Real.norm_eq_abs]
  unfold klInt
  rw [abs_le]
  constructor
  · have := neg_abs_le (pdens j v h σ y - pdens j v' h σ y)
    have : 0 ≤ chiInt j σ v' h y := by rw [← hc]; positivity
    linarith
  · have := le_abs_self (pdens j v h σ y - pdens j v' h σ y)
    linarith

/-- KL is the integral of its centred integrand. -/
theorem parKL_centred (j : ℕ) (hj : 0 < j) (σ v v' h : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hvv : MaskPair v v') :
    parKL j σ v v' h = ∫ y, (klInt j σ v v' h y - (pdens j v h σ y - pdens j v' h σ y)) := by
  have hD : Integrable (fun y => pdens j v h σ y - pdens j v' h σ y) :=
    (pdens_integrable j σ v h hσ).sub (pdens_integrable j σ v' h hσ)
  rw [integral_sub (klInt_integrable j hj σ v v' h hσ hh hh1 hvv) hD, integral_sub
    (pdens_integrable j σ v h hσ) (pdens_integrable j σ v' h hσ), pdens_integral j σ v h hσ,
    pdens_integral j σ v' h hσ, sub_self, sub_zero]
  rfl

/-- **KL is nonnegative**, at every level `h`. -/
theorem parKL_nonneg (j : ℕ) (σ v v' h : ℝ) (hσ : 0 < σ) : 0 ≤ parKL j σ v v' h := by
  unfold parKL
  by_cases hi : Integrable (fun y => klInt j σ v v' h y)
  · have hD : Integrable (fun y => pdens j v h σ y - pdens j v' h σ y) :=
      (pdens_integrable j σ v h hσ).sub (pdens_integrable j σ v' h hσ)
    have h1 : ∫ y, (pdens j v h σ y - pdens j v' h σ y) ≤ ∫ y, klInt j σ v v' h y := by
      refine integral_mono hD hi fun y => ?_
      have := (kl_pt_bounds _ _ (pdens_pos' j σ v h y hσ) (pdens_pos' j σ v' h y hσ)).1
      unfold klInt; linarith
    rw [integral_sub (pdens_integrable j σ v h hσ) (pdens_integrable j σ v' h hσ),
      pdens_integral j σ v h hσ, pdens_integral j σ v' h hσ, sub_self] at h1
    exact h1
  · rw [integral_undef hi]

/-- **The pointwise KL limit.** -/
theorem kl_pointwise (j : ℕ) (hj : 0 < j) (σ v v' y : ℝ) (hσ : 0 < σ) (hvv : MaskPair v v') :
    Tendsto (fun h => (klInt j σ v v' h y - (pdens j v h σ y - pdens j v' h σ y)) / h ^ (2 * j))
      (𝓝[>] 0) (𝓝 (aj j σ y ^ 2 / p0 σ y / 2)) := by
  have hv' := maskPair_v' hvv
  have hv : v = 1 ∨ v = -1 := by
    rcases hvv with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  set q : ℝ → ℝ := fun h => pdens j v' h σ y with hqdef
  set D : ℝ → ℝ := fun h => pdens j v h σ y - pdens j v' h σ y with hDdef
  set C : ℝ → ℝ := fun h => D h ^ 2 / q h / h ^ (2 * j) with hCdef
  have hC : Tendsto C (𝓝[>] 0) (𝓝 (aj j σ y ^ 2 / p0 σ y)) := by
    refine (chi_pointwise j hj σ v' y hσ hv').congr fun h => ?_
    simp only [hCdef, hDdef, hqdef]
    rw [diff_sq j σ h y hvv, ← chi_rescale]
    rfl
  have hq : Tendsto q (𝓝[>] 0) (𝓝 (p0 σ y)) := pdens_tendsto j hj σ v' y hv'
  have hD : Tendsto D (𝓝[>] 0) (𝓝 0) := by
    have := (pdens_tendsto j hj σ v y hv).sub hq
    rwa [sub_self] at this
  have hr : Tendsto (fun h => D h / q h) (𝓝[>] 0) (𝓝 0) := by
    have := hD.div hq (p0_pos σ y hσ).ne'
    rwa [zero_div] at this
  set Er : ℝ → ℝ := fun h => q h * ((1 + D h / q h) * Real.log (1 + D h / q h) - D h / q h
      - (D h / q h) ^ 2 / 2) / h ^ (2 * j) with hEr
  have hsmall : ∀ᶠ h in 𝓝[>] 0, |D h / q h| ≤ 1 / 2 := by
    have := hr.abs
    rw [abs_zero] at this
    exact this.eventually (ge_mem_nhds (by norm_num))
  have hEr0 : Tendsto Er (𝓝[>] 0) (𝓝 0) := by
    have hbound : Tendsto (fun h => 4 * (C h * |D h / q h|)) (𝓝[>] 0) (𝓝 0) := by
      have := (hC.mul hr.abs).const_mul 4
      simpa using this
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hsmall, self_mem_nhdsWithin] with h hs hpos
    have hh : 0 < h := hpos
    have hqp : 0 < q h := pdens_pos' j σ v' h y hσ
    have hhj : 0 < h ^ (2 * j) := pow_pos hh _
    have hlc := log_cubic (D h / q h) hs
    simp only [hEr, hCdef, Real.norm_eq_abs]
    rw [abs_div, abs_of_pos hhj, abs_mul, abs_of_pos hqp, div_le_iff₀ hhj]
    have e : 4 * (D h ^ 2 / q h / h ^ (2 * j) * |D h / q h|) * h ^ (2 * j)
        = q h * (4 * |D h / q h| ^ 3) := by
      rw [abs_div, abs_of_pos hqp]
      field_simp
      rw [← sq_abs (D h)]
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hlc hqp.le
  have hlim := (hC.div_const 2).add hEr0
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hpos
  have hh : 0 < h := hpos
  have hqp : 0 < q h := pdens_pos' j σ v' h y hσ
  have hpp : 0 < pdens j v h σ y := pdens_pos' j σ v h y hσ
  have hhj : 0 < h ^ (2 * j) := pow_pos hh _
  have hq0 : pdens j v' h σ y ≠ 0 := (pdens_pos' j σ v' h y hσ).ne'
  have hratio : 1 + D h / q h = pdens j v h σ y / q h := by
    simp only [hDdef, hqdef]; field_simp; ring
  simp only [hCdef, hEr]
  rw [hratio]
  unfold klInt
  simp only [hDdef, hqdef]
  field_simp
  ring

/-- **The rescaled KL converges to `c_j`.** -/
theorem kl_limit (j : ℕ) (hj : 0 < j) (σ v v' : ℝ) (hσ : 0 < σ) (hvv : MaskPair v v') :
    Tendsto (fun h => parKL j σ v v' h / h ^ (2 * j)) (𝓝[>] 0) (𝓝 (cj j σ)) := by
  have hv' := maskPair_v' hvv
  have hc : cj j σ = ∫ y, aj j σ y ^ 2 / p0 σ y / 2 := by
    unfold cj; rw [integral_div]; ring
  rw [hc]
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), parKL j σ v v' h / h ^ (2 * j)
      = ∫ y, (klInt j σ v v' h y - (pdens j v h σ y - pdens j v' h σ y)) / h ^ (2 * j) := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
    rw [parKL_centred j hj σ v v' h hσ hh.1 hh.2 hvv, integral_div]
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun y => KE j σ * envR j σ y) ?_ ?_
    ((envR_integrable j σ hσ).const_mul _) ?_
  · refine Filter.Eventually.of_forall fun h => ?_
    refine (((((continuous_pdens j v h σ).measurable.mul
      (((continuous_pdens j v h σ).measurable.div
        (continuous_pdens j v' h σ).measurable).log)).sub
      ((continuous_pdens j v h σ).sub (continuous_pdens j v' h σ)).measurable).div_const
        _)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
    refine Filter.Eventually.of_forall fun y => ?_
    have hp := pdens_pos' j σ v h y hσ
    have hq := pdens_pos' j σ v' h y hσ
    obtain ⟨b0, b1⟩ := kl_pt_bounds _ _ hp hq
    have hhj : 0 < h ^ (2 * j) := pow_pos hh.1 _
    have hle := chi_integrand_le j hj σ h y v' hσ hh.1 hh.2 hv'
    rw [← chi_rescale] at hle
    unfold chiInt at hle
    rw [← diff_sq j σ h y hvv] at hle
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by unfold klInt; exact b0) hhj.le)]
    refine le_trans ?_ hle
    exact div_le_div_of_nonneg_right (by unfold klInt; exact b1) hhj.le
  · exact Filter.Eventually.of_forall fun y => kl_pointwise j hj σ v v' y hσ hvv

/-! ## 8. The constant is positive -/

/-- The `χ²` of the two masks at query `j`, through the channel of `LeanPaperBParityWorldV1`. -/
theorem chi_lower_world (j : ℕ) (hj : 0 < j) (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1) :
    Gc j σ ^ 2 / 4 * h ^ (2 * j) ≤ ∫ y, chiInt j σ 1 h y := by
  set m := j + 1 with hm
  have hm0 : 0 < m := by omega
  set w : Fin m := ⟨j - 1, by omega⟩ with hw
  set w' : Fin m := ⟨j, by omega⟩ with hw'
  set q : Fin m := ⟨j, by omega⟩ with hq
  have hww : w ≠ w' := by
    intro e
    have hv : j - 1 = j := congrArg Fin.val e
    omega
  have hv : parVis m q w w' := by
    refine ⟨by simp [hq]; omega, Or.inl ?_⟩
    simp [hq, hw]; omega
  have hlow := par_chi_visible σ h hσ hh hh1 hm0 w w' q hww hv
  have hdens : ∀ y, (parChan m σ h hσ hh.le hm0).dens w q y = pdens j (-1) h σ y := by
    intro y
    show parDens m σ h w q y = _
    unfold parDens
    rw [if_neg (by simp [hq]; omega)]
    have : maskR (q : ℕ) ((w : ℕ) + 1) = -1 := by
      unfold maskR; rw [if_pos (by simp [hq, hw]; omega)]
    simp only [hq] at this ⊢
    rw [this]
  have hdens' : ∀ y, (parChan m σ h hσ hh.le hm0).dens w' q y = pdens j 1 h σ y := by
    intro y
    show parDens m σ h w' q y = _
    unfold parDens
    rw [if_neg (by simp [hq]; omega)]
    have : maskR (q : ℕ) ((w' : ℕ) + 1) = 1 := by
      unfold maskR; rw [if_neg (by simp [hq, hw'] <;> omega)]
    simp only [hq] at this ⊢
    rw [this]
  have hchi : chi (parChan m σ h hσ hh.le hm0) w w' q
      = ∫⁻ y, ENNReal.ofReal (chiInt j σ 1 h y) := by
    unfold chi
    refine lintegral_congr fun y => ?_
    rw [hdens, hdens']
    unfold chiInt
    rw [← diff_sq j σ h y (Or.inr ⟨rfl, rfl⟩)]
  rw [hchi, ← ofReal_integral_eq_lintegral_ofReal
    (chiInt_integrable j hj σ 1 h hσ hh hh1 (Or.inl rfl))
    (Filter.Eventually.of_forall fun y => div_nonneg (sq_nonneg _)
      (pdens_pos' j σ 1 h y hσ).le)] at hlow
  have hq' : (q : ℕ) = j := rfl
  rw [hq'] at hlow
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun y => div_nonneg (sq_nonneg _)
    (pdens_pos' j σ 1 h y hσ).le)).mp hlow

/-- **`c_j ≥ Gc_j² / 8 > 0`.** -/
theorem cj_ge (j : ℕ) (hj : 0 < j) (σ : ℝ) (hσ : 0 < σ) : Gc j σ ^ 2 / 8 ≤ cj j σ := by
  have hlim := chi_limit j hj σ 1 hσ (Or.inl rfl)
  have hge : ∀ᶠ h in 𝓝[>] (0 : ℝ), Gc j σ ^ 2 / 4 ≤ (∫ y, chiInt j σ 1 h y) / h ^ (2 * j) := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
    rw [le_div_iff₀ (pow_pos hh.1 _)]
    exact chi_lower_world j hj σ h hσ hh.1 hh.2
  have := ge_of_tendsto hlim hge
  linarith

theorem cj_pos (j : ℕ) (hj : 0 < j) (σ : ℝ) (hσ : 0 < σ) : 0 < cj j σ := by
  have := Gc_pos j hj σ
  have := cj_ge j hj σ hσ
  have : 0 < Gc j σ ^ 2 / 8 := by positivity
  linarith

end CIGAMF.P13.PaperBParityCritical
