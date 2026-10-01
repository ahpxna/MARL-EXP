import «LeanPaperBWorldsV1»
import «LeanPaperBStoppedParityV1»
import «LeanPaperBHellingerParityV1»

/-!
# Paper B: three assemblies (tasks T5, T7, T8)

Each result below is one declaration that composes theorems already proved elsewhere, with
every constant explicit, together with a witness that its hypotheses can be met in a
non-trivial instance.

* **T5, `chi2_worlds_le`** (Theorem `thm:unif`). On the two worlds built from a Gaussian
  mixture, the chi-square divergence `∫ (P - Q)^2 / Q` is at most
  `h^{2r} r^{-2r} klConst σ R h₀ r`, uniformly over every probe in the box. The flat world `Q`
  is above the envelope `envLo` (`worldQ_floor`, `mixDens_floor`), so the envelope bound of
  `hellinger_rate_bound` applies with the floor `ℓ = Q` itself: this is the monotonicity in the
  floor that turns `chi2_uniform` into a statement about `χ²(P, Q)`. `chi2_worlds_normalized`
  states it for the normalised pair `P/Z, Q/Z`, `Z = σ √(2π)`, which are probability
  densities (`worldQ_mass`, `worldP_mass`). `t5_satisfiable`: the box is non-empty with
  `h > 0`.
* **T7, `endpoint_stopped`** (Theorem `thm:endpoint`, stopped class). For `m ≥ 2`, `σ > 0`,
  `0 < h ≤ 1` and `0 < δ ≤ δ₀ = min(δS, δI)/2`: every safe-correct almost-surely stopping
  policy has, at some world, expected informative cost at least
  `cS log(1/δ)/h²` with `cS = 1/(8 (m-1) aS)`, and one safe-correct stopping policy costs at
  most `CS log(1/δ)/h²` at every world; the same for identification with `h^{2(m-1)}`,
  `cI = 1/(8 aI)` and `CI`. The level-`2δ` bounds of `stopped_safe_lower`/`stopped_id_lower`
  are converted by `log(1/(2δ)) ≥ log(1/δ)/2` (`log_half_le`, `δ ≤ 1/4`) and by dividing by
  `a h^{2s}` inside `ℝ≥0∞`. `endpoint_constants_pos`: `δ₀ > 0`, `cS, cI > 0`, and
  `log(1/δ₀) > 0`, so the statement is not vacuous.
* **T8, `order_theta`** (Theorem `thm:order`, general `Θ`). On any channel whose per-query
  chi-square is at most the graded information `κ = C h^{2 sep}`, with `κ ≤ K κ_H` on distinct
  worlds (`κ_H` the Hellinger information), and `s*` the least safe order:
  - every finite-horizon policy that is safe with probability `1 - δ` has a world with
    `E[#queries] ≥ (((1-δ)/(|W|-1)) log(1/δ) - log 2) / (C h^{2 s*})` (`graded_lower_chi`);
  - the Hellinger tournament at the obstruction value `t_H ≥ C h^{2 s*}/K`
    (`hellinger_upper_star`, `resolved_le_scale`) with
    `n = ⌈K log(|W|/δ)/(C h^{2 s*})⌉` rounds per pair is safe with probability `1 - δ` at every
    world and costs at most `|W|² n ≤ |W|² (K log(|W|/δ)/(C h^{2 s*}) + 1)`.
  So for fixed `|W|` the minimax cost is `Θ(log(1/δ)/h^{2 s*})`. The comparison `κ ≤ K κ_H` is
  asked only on DISTINCT worlds: on the diagonal `κ_H = 0` while `κ > 0`, so the
  all-pairs form would be unsatisfiable. `order_theta_parity`: the parity channel meets every
  hypothesis, with `C = aS`, `K = aS / C_H`, for identification (`s* = m - 1`).
-/

namespace CIGAMF.P13.PaperBAssembly

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

/-! ## T5. The chi-square divergence of the two worlds -/

section T5

open CIGAMF.P13.PaperBRates CIGAMF.P13.PaperBKL CIGAMF.P13.PaperBWorlds

variable {r : ℕ}

/-- **T5: `χ²(P, Q) = O(h^{2r})` uniformly over the linear class**, with the constant of
`chi2_uniform`. -/
theorem chi2_worlds_le (σ R h₀ h : ℝ) (r n : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hh₀ : 0 ≤ h₀) (hh : 0 ≤ h) (a : Fin r → ℝ) (ha : ∑ i, |a i| ≤ 1)
    (hscale : ∑ i, |h * a i| ≤ h₀)
    (w cs : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hcs : ∀ j, |cs j| ≤ R) :
    ∫ y, (worldP (mixDens σ n w cs) (fun i => h * a i) y
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y) ^ 2
          / worldQ (mixDens σ n w cs) (fun i => h * a i) y
      ≤ h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2 * klConst σ R h₀ r := by
  have hRh : 0 ≤ R + h₀ := by linarith
  have hfloor : ∀ y, envLo σ (R + h₀) y
      ≤ worldQ (mixDens σ n w cs) (fun i => h * a i) y := fun y =>
    worldQ_floor _ _ _ h₀ hscale
      (fun v y' hv => mixDens_floor σ R h₀ hσ hR hh₀ n w cs hw hw1 hcs v y' hv) y
  refine hellinger_rate_bound σ (R + h₀) h r hr hσ hRh hh a ha _ _ (fun y => ?_) hfloor
  rw [worlds_diff]
  exact iterDiff_mixture_envelope σ R h₀ hσ hR hh₀ r n w hw (le_of_eq hw1) cs hcs
    (fun i => h * a i) hscale y

theorem gkern_eq (σ : ℝ) : gkern σ = fun y => Real.exp (-(1 / (2 * σ ^ 2)) * y ^ 2) := by
  funext y; unfold gkern; ring_nf

theorem integrable_gkern (σ : ℝ) (hσ : 0 < σ) : Integrable (gkern σ) := by
  rw [gkern_eq]; exact integrable_exp_neg_mul_sq (by positivity)

theorem integral_gkern (σ : ℝ) (hσ : 0 < σ) : ∫ y, gkern σ y = σ * √(2 * π) := by
  rw [gkern_eq, integral_gaussian]
  have e : π / (1 / (2 * σ ^ 2)) = σ ^ 2 * (2 * π) := by field_simp
  rw [e, Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσ.le]

theorem integrable_mixDens (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (w cs : Fin n → ℝ) :
    Integrable (mixDens σ n w cs) := by
  unfold mixDens
  exact integrable_finset_sum _ fun j _ => ((integrable_gkern σ hσ).comp_sub_right (cs j)).const_mul _

theorem integral_mixDens (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (w cs : Fin n → ℝ) (hw1 : ∑ j, w j = 1) :
    ∫ y, mixDens σ n w cs y = σ * √(2 * π) := by
  unfold mixDens
  rw [integral_finset_sum _ fun j _ =>
    ((integrable_gkern σ hσ).comp_sub_right (cs j)).const_mul _]
  have : ∀ j ∈ (Finset.univ : Finset (Fin n)),
      ∫ y, w j * gkern σ (y - cs j) = w j * (σ * √(2 * π)) := by
    intro j _
    rw [integral_const_mul, integral_sub_right_eq_self (gkern σ) (cs j), integral_gkern σ hσ]
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, hw1, one_mul]

theorem integrable_worldQ (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (w cs : Fin n → ℝ) (b : Fin r → ℝ) :
    Integrable (worldQ (mixDens σ n w cs) b) := by
  unfold worldQ
  exact (integrable_finset_sum _ fun z _ =>
    (integrable_mixDens σ hσ n w cs).comp_sub_right (shiftOf b z)).const_mul _

/-- **The flat world has mass `σ √(2π)`.** -/
theorem worldQ_mass (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (w cs : Fin n → ℝ) (hw1 : ∑ j, w j = 1)
    (b : Fin r → ℝ) : ∫ y, worldQ (mixDens σ n w cs) b y = σ * √(2 * π) := by
  unfold worldQ
  rw [integral_const_mul, integral_finset_sum _ fun z _ =>
    (integrable_mixDens σ hσ n w cs).comp_sub_right (shiftOf b z)]
  have : ∀ z ∈ (Finset.univ : Finset (Fin r → Bool)),
      ∫ y, mixDens σ n w cs (y - shiftOf b z) = σ * √(2 * π) := by
    intro z _
    rw [integral_sub_right_eq_self (mixDens σ n w cs) (shiftOf b z),
      integral_mixDens σ hσ n w cs hw1]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : ((Fintype.card (Fin r → Bool) : ℕ) : ℝ) = 2 ^ r := by simp
  rw [hcard, ← mul_assoc, ← mul_pow]
  norm_num

/-- **The tilted world has the same mass** (for `r ≥ 1`). -/
theorem worldP_mass (σ : ℝ) (hσ : 0 < σ) (hr : 0 < r) (n : ℕ) (w cs : Fin n → ℝ)
    (hw1 : ∑ j, w j = 1) (b : Fin r → ℝ) :
    ∫ y, worldP (mixDens σ n w cs) b y = σ * √(2 * π) := by
  have hd : ∀ y, worldP (mixDens σ n w cs) b y
      = worldQ (mixDens σ n w cs) b y + iterDiff (mixDens σ n w cs) (List.ofFn b) y := by
    intro y; rw [← worlds_diff]; ring
  have hM := integrable_mixDens σ hσ n w cs
  have hI := iterDiff_integrable _ hM (List.ofFn b)
  simp_rw [hd]
  rw [integral_add (integrable_worldQ σ hσ n w cs b) hI, worldQ_mass σ hσ n w cs hw1 b]
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hr)
  rw [List.ofFn_succ, integral_iterDiff_zero _ hM, add_zero]

/-- **T5, normalised.** `P/Z` and `Q/Z`, `Z = σ √(2π)`, are probability densities
(`worldP_mass`, `worldQ_mass`), and their chi-square divergence is at most
`h^{2r} r^{-2r} klConst / (σ √(2π))`. -/
theorem chi2_worlds_normalized (σ R h₀ h : ℝ) (r n : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hh₀ : 0 ≤ h₀) (hh : 0 ≤ h) (a : Fin r → ℝ) (ha : ∑ i, |a i| ≤ 1)
    (hscale : ∑ i, |h * a i| ≤ h₀)
    (w cs : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hcs : ∀ j, |cs j| ≤ R) :
    ∫ y, (worldP (mixDens σ n w cs) (fun i => h * a i) y / (σ * √(2 * π))
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y / (σ * √(2 * π))) ^ 2
          / (worldQ (mixDens σ n w cs) (fun i => h * a i) y / (σ * √(2 * π)))
      ≤ h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2 * klConst σ R h₀ r / (σ * √(2 * π)) := by
  have hZ : 0 < σ * √(2 * π) := mul_pos hσ (Real.sqrt_pos.mpr (by positivity))
  have hfloor : ∀ y, envLo σ (R + h₀) y
      ≤ worldQ (mixDens σ n w cs) (fun i => h * a i) y := fun y =>
    worldQ_floor _ _ _ h₀ hscale
      (fun v y' hv => mixDens_floor σ R h₀ hσ hR hh₀ n w cs hw hw1 hcs v y' hv) y
  have hpt : ∀ y, (worldP (mixDens σ n w cs) (fun i => h * a i) y / (σ * √(2 * π))
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y / (σ * √(2 * π))) ^ 2
          / (worldQ (mixDens σ n w cs) (fun i => h * a i) y / (σ * √(2 * π)))
        = (worldP (mixDens σ n w cs) (fun i => h * a i) y
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y) ^ 2
          / worldQ (mixDens σ n w cs) (fun i => h * a i) y / (σ * √(2 * π)) := by
    intro y
    have hQ : 0 < worldQ (mixDens σ n w cs) (fun i => h * a i) y :=
      lt_of_lt_of_le (envLo_pos σ (R + h₀) y) (hfloor y)
    field_simp
  simp_rw [hpt]
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (chi2_worlds_le σ R h₀ h r n hr hσ hR hh₀ hh a ha hscale w cs hw hw1 hcs) hZ.le

/-- **T5's hypotheses are met with `h > 0`**: one centre at `0`, one shift of size `h = 1/2`. -/
theorem t5_satisfiable :
    ∃ (σ R h₀ h : ℝ) (a : Fin 1 → ℝ) (w cs : Fin 1 → ℝ),
      0 < σ ∧ 0 ≤ R ∧ 0 ≤ h₀ ∧ 0 < h ∧ ∑ i, |a i| ≤ 1 ∧ ∑ i, |h * a i| ≤ h₀
        ∧ (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, |cs j| ≤ R) :=
  ⟨1, 0, 1, 1 / 2, fun _ => 1, fun _ => 1, fun _ => 0, by norm_num, le_rfl, by norm_num,
    by norm_num, by norm_num, by norm_num, fun _ => by norm_num, by norm_num,
    fun _ => by norm_num⟩

end T5

/-! ## T7. The endpoint over almost-surely stopping policies, in `log(1/δ)` form -/

section T7

open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBParityExperiment CIGAMF.P13.PaperBEndgame
open CIGAMF.P13.PaperBRateClosure CIGAMF.P13.PaperBParityFinish CIGAMF.P13.PaperBStoppedParity
open CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBParityDecoder

variable {m : ℕ}

/-- The confidence threshold of the endpoint. -/
noncomputable def δ₀ (m : ℕ) : ℝ := min (δS m) (δI m) / 2

/-- The safe lower constant `1/(8 (m-1) aS)`. -/
noncomputable def cSafe (m : ℕ) (σ : ℝ) : ℝ := 1 / (8 * ((m : ℝ) - 1) * aS m σ)

/-- The identification lower constant `1/(8 aI)`. -/
noncomputable def cId (m : ℕ) (σ : ℝ) : ℝ := 1 / (8 * aI m σ)

/-- Dividing a lower bound `ofReal (A) ≤ ofReal (a) * X` by `a > 0` inside `ℝ≥0∞`. -/
theorem ofReal_div_le (A a : ℝ) (ha : 0 < a) (X : ℝ≥0∞)
    (h : ENNReal.ofReal A ≤ ENNReal.ofReal a * X) : ENNReal.ofReal (A / a) ≤ X := by
  by_cases hA : A ≤ 0
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonpos_of_nonneg hA ha.le)]; exact bot_le
  push_neg at hA
  have hne : ENNReal.ofReal a ≠ 0 := by simpa using ha
  have e : ENNReal.ofReal A = ENNReal.ofReal a * ENNReal.ofReal (A / a) := by
    rw [← ENNReal.ofReal_mul ha.le, mul_div_cancel₀ _ ha.ne']
  rw [e] at h
  exact (ENNReal.mul_le_mul_iff_right hne ENNReal.ofReal_ne_top).mp h

/-- **T7: Theorem `thm:endpoint`, the stopped class, with explicit constants.** -/
theorem endpoint_stopped (σ : ℝ) (hσ : 0 < σ) (hm : 0 < m) (hm2 : 2 ≤ m) (h δ : ℝ)
    (hh : 0 < h) (hh1 : h ≤ 1) (hδ : 0 < δ) (hδ0 : δ ≤ δ₀ m) :
    (∀ S : SPol m, CorrectS σ hσ hm .safe h δ S → ∃ w,
      ENNReal.ofReal (cSafe m σ * (Real.log (1 / δ) / h ^ 2)) ≤ costS σ hσ hm h S w) ∧
    (∃ S : SPol m, CorrectS σ hσ hm .safe h δ S ∧ ∀ w,
      costS σ hσ hm h S w
        ≤ ENNReal.ofReal ((safeCert σ hσ hm hm2).C * (Real.log (1 / δ) / h ^ 2))) ∧
    (∀ S : SPol m, CorrectS σ hσ hm .identify h δ S → ∃ w,
      ENNReal.ofReal (cId m σ * (Real.log (1 / δ) / h ^ (2 * (m - 1)))) ≤ costS σ hσ hm h S w) ∧
    (∃ S : SPol m, CorrectS σ hσ hm .identify h δ S ∧ ∀ w,
      costS σ hσ hm h S w
        ≤ ENNReal.ofReal ((idCert σ hσ hm hm2).C * (Real.log (1 / δ) / h ^ (2 * (m - 1))))) := by
  have h2δ : 2 * δ ≤ min (δS m) (δI m) := by unfold δ₀ at hδ0; linarith
  obtain ⟨-, hSup, -, hIup⟩ := stopped_parity_rates σ hσ hm hm2 h δ hh hh1 hδ h2δ
  obtain ⟨hSlo, hIlo⟩ := stopped_lower_log σ hσ hm hm2 h δ hh hh1 hδ h2δ
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    linarith
  have haS := aS_pos (m := m) σ hσ
  have haI := aI_pos (m := m) σ hσ
  have hsc1 : scale h δ 1 = Real.log (1 / δ) / h ^ 2 := by unfold scale; norm_num
  have hscI : scale h δ (m - 1) = Real.log (1 / δ) / h ^ (2 * (m - 1)) := rfl
  refine ⟨fun S hS => ?_, ?_, fun S hS => ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hSlo S hS
    refine ⟨w, le_trans (le_of_eq ?_) (ofReal_div_le _ _ (by positivity) _ hw)⟩
    congr 1; unfold cSafe; field_simp
  · obtain ⟨S, hS, hc⟩ := hSup
    exact ⟨S, hS, fun w => by rw [← hsc1]; exact hc w⟩
  · obtain ⟨w, hw⟩ := hIlo S hS
    refine ⟨w, le_trans (le_of_eq ?_) (ofReal_div_le _ _ (by positivity) _ hw)⟩
    congr 1; unfold cId; field_simp
  · obtain ⟨S, hS, hc⟩ := hIup
    exact ⟨S, hS, fun w => by rw [← hscI]; exact hc w⟩

/-- **The endpoint is not vacuous**: the threshold and both lower constants are positive, and
`log(1/δ₀) > 0`. -/
theorem endpoint_constants_pos (σ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) :
    0 < δ₀ m ∧ 0 < cSafe m σ ∧ 0 < cId m σ ∧ 0 < Real.log (1 / δ₀ m) := by
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    linarith
  have hKm : (0 : ℝ) < Km m := by
    unfold Km
    have : 1 ≤ m - 1 := by omega
    exact_mod_cast this
  have hδS : 0 < δS m := by
    unfold δS; exact lt_min (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  have hδI : 0 < δI m := by
    unfold δI; exact lt_min (by norm_num) (by positivity)
  have hδ0 : 0 < δ₀ m := by unfold δ₀; exact half_pos (lt_min hδS hδI)
  have hδ0le : δ₀ m ≤ 1 / 8 := by
    unfold δ₀
    have : min (δS m) (δI m) ≤ 1 / 4 := (min_le_left _ _).trans (by unfold δS; exact min_le_left _ _)
    linarith
  refine ⟨hδ0, ?_, ?_, ?_⟩
  · unfold cSafe; have := aS_pos (m := m) σ hσ; positivity
  · unfold cId; have := aI_pos (m := m) σ hσ; positivity
  · apply Real.log_pos
    rw [lt_div_iff₀ hδ0]; linarith

end T7

/-! ## T8. The order law with `Θ`, on a general channel -/

section T8

open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBObstructionLaw
open CIGAMF.P13.PaperBObstructionParity CIGAMF.P13.PaperBHellingerTest
open CIGAMF.P13.PaperBSchedule CIGAMF.P13.PaperBParityExperiment
open CIGAMF.P13.PaperBHellingerParity CIGAMF.P13.PaperBParityChannel

variable {W Q A : Type*} [Fintype W] [DecidableEq W] [Fintype A] [DecidableEq A]
  [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] [Fintype Q]

/-- The graded information with the diagonal set to zero. -/
noncomputable def gradedOff (sep : W → W → ℕ) (Cc h : ℝ≥0) : W → W → ℝ≥0 :=
  fun u v => if u = v then 0 else graded sep Cc h u v

/-- **T8: Theorem `thm:order` with `Θ`, for fixed `|W|`.** -/
theorem order_theta [Nonempty A] (C : Channel W Q) (safe : W → Finset A)
    (hsafe : ∀ w, (safe w).Nonempty) (hex : ∃ H : Finset W, Unsafe safe H)
    (sep : W → W → ℕ) (Cc h K : ℝ≥0) (hC : 0 < Cc) (h0 : 0 < h) (h1 : h < 1)
    (hchi : ∀ w v, w ≠ v → ∀ q, q ≠ C.dummy →
      chi C w v q ≤ ((graded sep Cc h w v : ℝ≥0) : ℝ≥0∞))
    (hdom : ∀ u v, u ≠ v → graded sep Cc h u v ≤ K * kH C u v)
    (sStar : ℕ) (hS : SafeAt sep safe sStar) (hmin : ∀ s, SafeAt sep safe s → sStar ≤ s)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (a0 : A) :
    -- the lower side, for every finite-horizon policy
    (∀ (pol : Policy Q) (n : ℕ) (out : Hist Q n → A),
      (∀ w, MeasurableSet {ω | out ω ∈ safe w}) →
      (∀ w, 1 - δ ≤ (hist C pol w n).real {ω | out ω ∈ safe w}) →
      ∃ w0 : W, ENNReal.ofReal
          (((1 - δ) / ((Fintype.card W : ℝ) - 1) * Real.log (1 / δ) - Real.log 2)
            / ((Cc : ℝ) * (h : ℝ) ^ (2 * sStar)))
        ≤ costN C pol w0 n) ∧
    -- the upper side, by the Hellinger tournament
    (∃ tH : ℝ≥0, Cc * h ^ (2 * sStar) ≤ K * tH ∧ 0 < tH ∧
      let n := ⌈(K : ℝ) * Real.log ((Fintype.card W : ℝ) / δ) / ((Cc : ℝ) * (h : ℝ) ^ (2 * sStar))⌉₊
      (n : ℝ) ≤ (K : ℝ) * Real.log ((Fintype.card W : ℝ) / δ) / ((Cc : ℝ) * (h : ℝ) ^ (2 * sStar)) + 1
      ∧ (∀ w, hist C (schedPolicy (tSched C tH n)) w (Fintype.card (W × W) * n)
            {ω | decode safe (pairSet (kH C) tH) (beatH C tH n) a0 ω ∉ safe w}
            ≤ ENNReal.ofReal δ)
      ∧ ∀ w, costN C (schedPolicy (tSched C tH n)) w (Fintype.card (W × W) * n)
            ≤ ((Fintype.card W ^ 2 * n : ℕ) : ℝ≥0∞)) := by
  have ht0 : (0 : ℝ) < (Cc : ℝ) * (h : ℝ) ^ (2 * sStar) := by
    have : (0 : ℝ) < Cc := by exact_mod_cast hC
    have : (0 : ℝ) < h := by exact_mod_cast h0
    positivity
  refine ⟨fun pol n out hmeas hcorr => ?_, ?_⟩
  · obtain ⟨w0, hw0⟩ := graded_lower_chi C pol n out safe hsafe hmeas δ hδ hδ1 hcorr sep Cc h hC
      h0 h1 hchi hex sStar hS hmin
    refine ⟨w0, ofReal_div_le _ _ ht0 _ ?_⟩
    have e : ((Cc * h ^ (2 * sStar) : ℝ≥0) : ℝ≥0∞)
        = ENNReal.ofReal ((Cc : ℝ) * (h : ℝ) ^ (2 * sStar)) := by
      rw [← NNReal.coe_pow, ← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal]
    rwa [e] at hw0
  · obtain ⟨tH, hres, ⟨H, hH, htight⟩, hup⟩ := hellinger_upper_star C safe hsafe hex a0 δ hδ
    have hgres : Resolves (graded sep Cc h) safe (Cc * h ^ (2 * sStar)) :=
      (graded_resolves_iff sep safe Cc h hC h0 h1 sStar).mpr hS
    have hres1 : Resolves (gradedOff sep Cc h) safe (Cc * h ^ (2 * sStar)) := by
      intro H' hH'
      obtain ⟨u, hu, v, hv, hne, hle⟩ := hgres H' hH'
      exact ⟨u, hu, v, hv, hne, by unfold gradedOff; rwa [if_neg hne]⟩
    have hcmp : ∀ u v, gradedOff sep Cc h u v ≤ K * kH C u v := by
      intro u v
      unfold gradedOff
      split_ifs with huv
      · exact bot_le
      · exact hdom u v huv
    have hle : Cc * h ^ (2 * sStar) ≤ K * tH :=
      resolved_le_scale (gradedOff sep Cc h) (kH C) K hcmp safe _ tH hres1 H hH htight
    have hpos : (0 : ℝ≥0) < Cc * h ^ (2 * sStar) := by
      have := pow_pos h0 (2 * sStar); exact mul_pos hC this
    have hKt : 0 < K * tH := lt_of_lt_of_le hpos hle
    have htH : 0 < tH := pos_of_mul_pos_right hKt (by positivity)
    have hK : 0 < K := pos_of_mul_pos_left hKt (by positivity)
    refine ⟨tH, hle, htH, ?_⟩
    intro n
    have hW : (1 : ℝ) ≤ Fintype.card W := by
      obtain ⟨H0, hH0⟩ := hex
      have := two_le_card_of_unsafe safe hsafe H0 hH0
      have : 2 ≤ Fintype.card W := this.trans (Finset.card_le_univ H0)
      exact_mod_cast (by omega : 1 ≤ Fintype.card W)
    have hlog : 0 ≤ Real.log ((Fintype.card W : ℝ) / δ) :=
      Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    have htHr : (0 : ℝ) < tH := by exact_mod_cast htH
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK
    have hleR : (Cc : ℝ) * (h : ℝ) ^ (2 * sStar) ≤ (K : ℝ) * tH := by exact_mod_cast hle
    have hnge : Real.log ((Fintype.card W : ℝ) / δ) / tH ≤ n := by
      refine le_trans ?_ (Nat.le_ceil _)
      rw [div_le_div_iff₀ htHr ht0]
      nlinarith [mul_le_mul_of_nonneg_left hleR hlog]
    obtain ⟨hsafeU, hcost⟩ := hup htH n hnge
    refine ⟨?_, hsafeU, hcost⟩
    exact (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hKr.le hlog) ht0.le)).le

/-- **T8 is not vacuous: the parity channel meets every hypothesis** (identification,
`s* = m - 1`, `C = aS`, `K = aS / C_H`). -/
theorem order_theta_parity {m : ℕ} (σ : ℝ) (hσ : 0 < σ) (hm2 : 2 ≤ m) (h : ℝ≥0) (hh : 0 < h)
    (hh1 : h < 1) :
    let C := chanAt σ hσ (by omega : 0 < m) (h : ℝ)
    (∀ w v : Fin m, w ≠ v → ∀ q, q ≠ C.dummy →
      chi C w v q ≤ ((graded sepP (aSN m σ hσ) h w v : ℝ≥0) : ℝ≥0∞))
    ∧ (∀ u v : Fin m, u ≠ v → graded sepP (aSN m σ hσ) h u v ≤ (aSN m σ hσ / CH m σ) * kH C u v)
    ∧ SafeAt (sepP (m := m)) (fun w : Fin m => ({w} : Finset (Fin m))) (m - 1)
    ∧ (∀ s, SafeAt (sepP (m := m)) (fun w : Fin m => ({w} : Finset (Fin m))) s → m - 1 ≤ s) := by
  have hm : 0 < m := by omega
  intro C
  obtain ⟨hS, hmin⟩ := parity_id_order (m := m) hm2
  refine ⟨fun w v hwv q hq => parity_graded σ hσ hm h hh hh1.le w v hwv q hq, fun u v huv => ?_,
    hS, hmin⟩
  have hCH : 0 < CH m σ := CH_pos σ hm2
  have hg := parity_kH_graded σ hσ hm2 h hh hh1.le u v huv
  have e : graded sepP (aSN m σ hσ) h u v
      = (aSN m σ hσ / CH m σ) * graded sepP (CH m σ) h u v := by
    unfold graded
    rw [← mul_assoc, div_mul_cancel₀ _ hCH.ne']
  rw [e]
  exact mul_le_mul_of_nonneg_left hg (by positivity)

end T8

#print axioms chi2_worlds_le
#print axioms worldQ_mass
#print axioms worldP_mass
#print axioms chi2_worlds_normalized
#print axioms t5_satisfiable
#print axioms endpoint_stopped
#print axioms endpoint_constants_pos
#print axioms order_theta
#print axioms order_theta_parity

end CIGAMF.P13.PaperBAssembly
