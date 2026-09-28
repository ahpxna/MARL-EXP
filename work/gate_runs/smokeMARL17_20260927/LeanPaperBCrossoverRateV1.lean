import «LeanPaperBParityCriticalV1»

/-!
# Paper B: the query-class crossover as a RATE (B1 / P-7), on the actual mixture density

The crossover channel has three hidden tail bits `w`, the hidden character
`χ(w) = s₁ s₂ s₃`, and the widened probe

    g_η(w) = (s₁ + s₂ + s₃ + η s₁ s₂) / (3 + η),   η ≥ 0.

The two worlds `v = ±1` have densities `p_v(y) = (1/8) Σ_w φ_σ(y − v χ(w) − h g_η(w))`
(`xdens`).  At `η = 0` this is the parity channel with `j = 3`.

## WHAT IS PROVED (this file, part 1: the ingredients)

* `phi_eq_gkern`, `iter_gkern`, `iter_phi`: `φ_σ^{(k)} = Zc⁻¹ · gaussDeriv σ k`.
* `iter_gfun`, `gfun_deriv_bound`: `|G_y^{(k)}(u)| ≤ 2 Zc⁻¹ envUp σ 2 k y` for `|u| ≤ 1`, where
  `G_y(u) = φ(y−1−u) − φ(y+1−u)`.
* `xdens_sub`: `p_+ − p_− = XF`, the cube average `(1/8) Σ χ(w) G_y(g_η(w) h)`.
* `mom0` … `mom3`: `E χ = 0`, `E χ g = 0`, `E χ g² = 2η/(3+η)²`, `E χ g³ = 6/(3+η)³`.
* `iter_XF`: `XF^{(k)}(t) = (1/8) Σ χ g^k G^{(k)}(g t)`, at every `t`.
-/

namespace CIGAMF.P13.PaperBCrossoverRate

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBParityCritical CIGAMF.P13.PaperBRates

/-! ## 1. Gaussian derivatives -/

theorem phi_eq_gkern (σ x : ℝ) : phi σ x = (Zc σ)⁻¹ * gkern σ x := by
  unfold phi gkern Zc gaussianPDFReal var2
  simp only [NNReal.coe_mk, sub_zero]
  congr 2

theorem iter_gkern (σ : ℝ) (hσ : σ ≠ 0) (n : ℕ) : iteratedDeriv n (gkern σ) = gaussDeriv σ n := by
  induction n with
  | zero => funext y; rw [iteratedDeriv_zero, gaussDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext y
      exact (gaussDeriv_hasDerivAt σ hσ n y).deriv

theorem iter_phi (σ : ℝ) (hσ : σ ≠ 0) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (phi σ) x = (Zc σ)⁻¹ * gaussDeriv σ n x := by
  have hf : phi σ = fun x => (Zc σ)⁻¹ * gkern σ x := funext (phi_eq_gkern σ)
  rw [hf, iteratedDeriv_const_mul_field, iter_gkern σ hσ n]

theorem contDiff_phi (σ : ℝ) (n : ℕ) : ContDiff ℝ n (phi σ) := by
  unfold phi gaussianPDFReal; fun_prop

/-- The `k`-th derivative of `G_y` at any point. -/
theorem iter_gfun (σ y : ℝ) (hσ : σ ≠ 0) (k : ℕ) (u : ℝ) :
    iteratedDeriv k (gfun σ y) u
      = (-1) ^ k * (Zc σ)⁻¹ * (gaussDeriv σ k (y - 1 - u) - gaussDeriv σ k (y + 1 - u)) := by
  have hp := contDiff_phi σ k
  have hA : ContDiffAt ℝ k (fun u => phi σ (y - 1 - u)) u :=
    (hp.comp (contDiff_const.sub contDiff_id)).contDiffAt
  have hB : ContDiffAt ℝ k (fun u => phi σ (y + 1 - u)) u :=
    (hp.comp (contDiff_const.sub contDiff_id)).contDiffAt
  have hg : gfun σ y = fun u => phi σ (y - 1 - u) - phi σ (y + 1 - u) := rfl
  rw [hg, iteratedDeriv_fun_sub hA hB]
  have e1 := congrFun (iteratedDeriv_comp_const_sub (n := k) (f := phi σ) (s := y - 1)) u
  have e2 := congrFun (iteratedDeriv_comp_const_sub (n := k) (f := phi σ) (s := y + 1)) u
  simp only [smul_eq_mul] at e1 e2
  rw [e1, e2, iter_phi σ hσ, iter_phi σ hσ]
  ring

/-- **Uniform bound on `G_y^{(k)}` for `|u| ≤ 1`.** -/
theorem gfun_deriv_bound (σ y : ℝ) (hσ : 0 < σ) (k : ℕ) (u : ℝ) (hu : |u| ≤ 1) :
    |iteratedDeriv k (gfun σ y) u| ≤ 2 * ((Zc σ)⁻¹ * envUp σ 2 k y) := by
  rw [iter_gfun σ y hσ.ne' k u]
  have hZ : 0 < (Zc σ)⁻¹ := inv_pos.mpr (Zc_pos σ hσ)
  have h1 : |gaussDeriv σ k (y - (1 + u))| ≤ envUp σ 2 k y :=
    gaussDeriv_shift_envelope σ 2 hσ (by norm_num) k (1 + u) y
      (by rw [abs_le] at hu ⊢; constructor <;> linarith)
  have h2 : |gaussDeriv σ k (y - (-1 + u))| ≤ envUp σ 2 k y :=
    gaussDeriv_shift_envelope σ 2 hσ (by norm_num) k (-1 + u) y
      (by rw [abs_le] at hu ⊢; constructor <;> linarith)
  have e1 : y - 1 - u = y - (1 + u) := by ring
  have e2 : y + 1 - u = y - (-1 + u) := by ring
  rw [e1, e2, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hZ]
  have := abs_sub (gaussDeriv σ k (y - (1 + u))) (gaussDeriv σ k (y - (-1 + u)))
  nlinarith

/-! ## 2. The crossover channel -/

/-- Rademacher value. -/
def sb (b : Bool) : ℝ := if b then 1 else -1

abbrev Cube := Bool × Bool × Bool

/-- The hidden character. -/
def chiB (w : Cube) : ℝ := sb w.1 * sb w.2.1 * sb w.2.2

/-- The widened probe. -/
noncomputable def gE (η : ℝ) (w : Cube) : ℝ :=
  (sb w.1 + sb w.2.1 + sb w.2.2 + η * (sb w.1 * sb w.2.1)) / (3 + η)

/-- The observation density of world `v`. -/
noncomputable def xdens (η v h σ y : ℝ) : ℝ :=
  (1 / 8) * ∑ w : Cube, phi σ (y - (v * chiB w + h * gE η w))

/-- The density difference as a cube average. -/
noncomputable def XF (η σ y h : ℝ) : ℝ := (1 / 8) * ∑ w : Cube, chiB w * gfun σ y (gE η w * h)

theorem sb_pm (b : Bool) : sb b = 1 ∨ sb b = -1 := by cases b <;> simp [sb]

theorem chiB_pm (w : Cube) : chiB w = 1 ∨ chiB w = -1 := by
  unfold chiB
  rcases sb_pm w.1 with h1 | h1 <;> rcases sb_pm w.2.1 with h2 | h2 <;>
    rcases sb_pm w.2.2 with h3 | h3 <;> simp [h1, h2, h3]

theorem xdens_sub (η h σ y : ℝ) : xdens η 1 h σ y - xdens η (-1) h σ y = XF η σ y h := by
  unfold xdens XF
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold gfun
  rcases chiB_pm w with hc | hc <;> rw [hc] <;> ring_nf

theorem sum_cube (f : Cube → ℝ) :
    ∑ w : Cube, f w = f (true, true, true) + f (true, true, false) + f (true, false, true)
      + f (true, false, false) + f (false, true, true) + f (false, true, false)
      + f (false, false, true) + f (false, false, false) := by
  simp [Fintype.sum_prod_type, Fintype.sum_bool]; ring

/-! ## 3. The moments against the character -/

theorem mom0 : (1 / 8 : ℝ) * ∑ w : Cube, chiB w = 0 := by
  rw [sum_cube]; simp [chiB, sb]

theorem mom1 (η : ℝ) (hη : 0 ≤ η) : (1 / 8 : ℝ) * ∑ w : Cube, chiB w * gE η w = 0 := by
  have h3 : (3 + η) ≠ 0 := by linarith
  rw [sum_cube]; simp only [chiB, gE, sb]; norm_num; field_simp; ring

theorem mom2 (η : ℝ) (hη : 0 ≤ η) :
    (1 / 8 : ℝ) * ∑ w : Cube, chiB w * gE η w ^ 2 = 2 * η / (3 + η) ^ 2 := by
  have h3 : (3 + η) ≠ 0 := by linarith
  rw [sum_cube]; simp only [chiB, gE, sb]; norm_num; field_simp; ring

theorem mom3 (η : ℝ) (hη : 0 ≤ η) :
    (1 / 8 : ℝ) * ∑ w : Cube, chiB w * gE η w ^ 3 = 6 / (3 + η) ^ 3 := by
  have h3 : (3 + η) ≠ 0 := by linarith
  rw [sum_cube]; simp only [chiB, gE, sb]; norm_num; field_simp; ring

theorem gE_abs_le (η : ℝ) (hη : 0 ≤ η) (w : Cube) : |gE η w| ≤ 1 := by
  unfold gE
  have h3 : 0 < 3 + η := by linarith
  rw [abs_div, abs_of_pos h3, div_le_one h3]
  rcases sb_pm w.1 with h1 | h1 <;> rcases sb_pm w.2.1 with h2 | h2 <;>
    rcases sb_pm w.2.2 with h4 | h4 <;> rw [h1, h2, h4] <;> rw [abs_le] <;> constructor <;> linarith

/-! ## 4. Derivatives of `XF` at every point -/

theorem contDiff_XF (η σ y : ℝ) (n : ℕ) : ContDiff ℝ n (XF η σ y) := by
  unfold XF gfun phi gaussianPDFReal
  fun_prop

theorem iter_XF (η σ y : ℝ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (XF η σ y) t
      = (1 / 8) * ∑ w : Cube, chiB w * gE η w ^ k * iteratedDeriv k (gfun σ y) (gE η w * t) := by
  have hg := contDiff_gfun σ y k
  have hF : XF η σ y = fun h => (1 / 8 : ℝ) * ∑ w : Cube, chiB w * gfun σ y (gE η w * h) := rfl
  rw [hF, iteratedDeriv_const_mul_field]
  congr 1
  rw [iteratedDeriv_fun_sum (f := fun w h => chiB w * gfun σ y (gE η w * h))
    (fun w _ => (contDiff_const.mul (hg.comp (contDiff_const.mul contDiff_id))).contDiffAt)]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul hg]
  simp only [smul_eq_mul]
  ring

/-! ## 5. The Taylor remainder of order four, uniform in `η ≥ 0` -/

/-- Second and third derivatives of `G_y` at `0`. -/
noncomputable def G2 (σ y : ℝ) : ℝ := iteratedDeriv 2 (gfun σ y) 0
noncomputable def G3 (σ y : ℝ) : ℝ := iteratedDeriv 3 (gfun σ y) 0

noncomputable def M2 (η : ℝ) : ℝ := 2 * η / (3 + η) ^ 2
noncomputable def M3 (η : ℝ) : ℝ := 6 / (3 + η) ^ 3

/-- The Taylor polynomial of order three. -/
noncomputable def T3 (η σ y h : ℝ) : ℝ := M2 η * G2 σ y * h ^ 2 / 2 + M3 η * G3 σ y * h ^ 3 / 6

/-- The fourth-derivative envelope. -/
noncomputable def E4 (σ y : ℝ) : ℝ := 2 * ((Zc σ)⁻¹ * envUp σ 2 4 y)

theorem deriv0 (η σ y : ℝ) (k : ℕ) :
    iteratedDeriv k (XF η σ y) 0
      = iteratedDeriv k (gfun σ y) 0 * ((1 / 8) * ∑ w : Cube, chiB w * gE η w ^ k) := by
  rw [iter_XF]
  simp_rw [mul_zero]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

theorem taylor3_eq (η σ y h : ℝ) (hη : 0 ≤ η) (hh : 0 < h) :
    taylorWithinEval (XF η σ y) 3 (Set.Icc 0 h) 0 h = T3 η σ y h := by
  rw [taylor_within_apply]
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) h) := uniqueDiffOn_Icc hh
  have h0 : (0 : ℝ) ∈ Set.Icc 0 h := ⟨le_rfl, hh.le⟩
  have hW : ∀ k, iteratedDerivWithin k (XF η σ y) (Set.Icc 0 h) 0 = iteratedDeriv k (XF η σ y) 0 :=
    fun k => iteratedDerivWithin_eq_iteratedDeriv hU ((contDiff_XF η σ y k).contDiffAt) h0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hW, deriv0, smul_eq_mul]
  have m0 := mom0
  have m1 := mom1 η hη
  have m2 := mom2 η hη
  have m3 := mom3 η hη
  have e0 : (1 / 8 : ℝ) * ∑ w : Cube, chiB w * gE η w ^ 0 = 0 := by simpa using m0
  have e1 : (1 / 8 : ℝ) * ∑ w : Cube, chiB w * gE η w ^ 1 = 0 := by simpa using m1
  rw [e0, e1, m2, m3]
  unfold T3 M2 M3 G2 G3
  simp only [Nat.factorial, Nat.cast_ofNat]
  push_cast
  ring

/-- **The order-four Taylor remainder, uniform in `η ≥ 0` and `0 < h ≤ 1`.** -/
theorem XF_taylor (η σ y h : ℝ) (hη : 0 ≤ η) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1) :
    |XF η σ y h - T3 η σ y h| ≤ E4 σ y * h ^ 4 / 6 := by
  have hU : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) h) := uniqueDiffOn_Icc hh
  have hcd : ContDiffOn ℝ ((3 : ℕ) + 1) (XF η σ y) (Set.Icc 0 h) := by
    have := (contDiff_XF η σ y 4).contDiffOn (s := Set.Icc 0 h)
    exact_mod_cast this
  have hx : h ∈ Set.Icc (0 : ℝ) h := ⟨hh.le, le_rfl⟩
  have hC : ∀ t ∈ Set.Icc (0 : ℝ) h,
      ‖iteratedDerivWithin (3 + 1) (XF η σ y) (Set.Icc 0 h) t‖ ≤ E4 σ y := by
    intro t ht
    rw [iteratedDerivWithin_eq_iteratedDeriv hU ((contDiff_XF η σ y (3 + 1)).contDiffAt) ht,
      iter_XF, Real.norm_eq_abs]
    have hbound : ∀ w : Cube,
        |chiB w * gE η w ^ (3 + 1) * iteratedDeriv (3 + 1) (gfun σ y) (gE η w * t)| ≤ E4 σ y := by
      intro w
      have hg := gE_abs_le η hη w
      have hgt : |gE η w * t| ≤ 1 := by
        rw [abs_mul]
        have : |t| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
        nlinarith [abs_nonneg (gE η w), abs_nonneg t]
      have hd := gfun_deriv_bound σ y hσ (3 + 1) (gE η w * t) hgt
      have hc : |chiB w| = 1 := by rcases chiB_pm w with h | h <;> rw [h] <;> norm_num
      have hp : |gE η w ^ (3 + 1)| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hg
      rw [abs_mul, abs_mul, hc, one_mul]
      unfold E4
      calc |gE η w ^ (3 + 1)| * |iteratedDeriv (3 + 1) (gfun σ y) (gE η w * t)|
          ≤ 1 * (2 * ((Zc σ)⁻¹ * envUp σ 2 (3 + 1) y)) :=
            mul_le_mul hp hd (abs_nonneg _) zero_le_one
        _ = 2 * ((Zc σ)⁻¹ * envUp σ 2 4 y) := by norm_num
    calc |(1 / 8) * ∑ w : Cube, chiB w * gE η w ^ (3 + 1) * iteratedDeriv (3 + 1) (gfun σ y) (gE η w * t)|
        ≤ (1 / 8) * ∑ w : Cube, |chiB w * gE η w ^ (3 + 1) * iteratedDeriv (3 + 1) (gfun σ y) (gE η w * t)| := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
          exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
      _ ≤ (1 / 8) * ∑ _w : Cube, E4 σ y :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => hbound w) (by norm_num)
      _ = E4 σ y := by simp [Finset.card_univ]
  have hT := taylor_mean_remainder_bound (n := 3) hh.le hcd hx hC
  rw [taylor3_eq η σ y h hη hh, Real.norm_eq_abs, sub_zero] at hT
  simpa [Nat.factorial] using hT

/-! ## 6. The pointwise envelope and the density floor -/

theorem G2_bound (σ y : ℝ) (hσ : 0 < σ) : |G2 σ y| ≤ 2 * ((Zc σ)⁻¹ * envUp σ 2 2 y) :=
  gfun_deriv_bound σ y hσ 2 0 (by simp)

theorem G3_bound (σ y : ℝ) (hσ : 0 < σ) : |G3 σ y| ≤ 2 * ((Zc σ)⁻¹ * envUp σ 2 3 y) :=
  gfun_deriv_bound σ y hσ 3 0 (by simp)

theorem M2_le (η : ℝ) (hη : 0 ≤ η) : 0 ≤ M2 η ∧ M2 η ≤ η := by
  unfold M2
  have h3 : 0 < (3 + η) ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ h3]
  have : (0 : ℝ) ≤ (3 + η) ^ 2 - 2 := by nlinarith
  nlinarith [mul_nonneg hη this]

theorem M3_le (η : ℝ) (hη : 0 ≤ η) : 0 ≤ M3 η ∧ M3 η ≤ 1 := by
  unfold M3
  have h3 : 0 < (3 + η) ^ 3 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ h3]; nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) (by linarith : (3 : ℝ) ≤ 3 + η) 3]

/-- The envelope sums used below. -/
noncomputable def U2 (σ y : ℝ) : ℝ := envUp σ 2 2 y
noncomputable def U34 (σ y : ℝ) : ℝ := envUp σ 2 3 y + envUp σ 2 4 y

theorem U2_nonneg (σ y : ℝ) : 0 ≤ U2 σ y := envUp_nonneg σ 2 2 y (by norm_num)
theorem U34_nonneg (σ y : ℝ) : 0 ≤ U34 σ y :=
  add_nonneg (envUp_nonneg σ 2 3 y (by norm_num)) (envUp_nonneg σ 2 4 y (by norm_num))

/-- **Pointwise envelope, uniform in `η ≥ 0`, `0 < h ≤ 1`**:
`|p_+ − p_−| ≤ Zc⁻¹ (η h² U2 + h³ U34)`. -/
theorem XF_abs_le (η σ y h : ℝ) (hη : 0 ≤ η) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1) :
    |XF η σ y h| ≤ (Zc σ)⁻¹ * (η * h ^ 2 * U2 σ y + h ^ 3 * U34 σ y) := by
  have hZ : 0 < (Zc σ)⁻¹ := inv_pos.mpr (Zc_pos σ hσ)
  have hT := XF_taylor η σ y h hη hσ hh hh1
  have hG2 := G2_bound σ y hσ
  have hG3 := G3_bound σ y hσ
  obtain ⟨m20, m2le⟩ := M2_le η hη
  obtain ⟨m30, m3le⟩ := M3_le η hη
  have e2 := envUp_nonneg σ 2 2 y (by norm_num)
  have e3 := envUp_nonneg σ 2 3 y (by norm_num)
  have e4 := envUp_nonneg σ 2 4 y (by norm_num)
  have hh2 : 0 ≤ h ^ 2 := by positivity
  have hh3 : 0 ≤ h ^ 3 := by positivity
  have h43 : h ^ 4 ≤ h ^ 3 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
  have hT3 : |T3 η σ y h| ≤ M2 η * |G2 σ y| * h ^ 2 / 2 + M3 η * |G3 σ y| * h ^ 3 / 6 := by
    unfold T3
    have := abs_add_le (M2 η * G2 σ y * h ^ 2 / 2) (M3 η * G3 σ y * h ^ 3 / 6)
    refine this.trans (le_of_eq ?_)
    rw [abs_div, abs_div, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg m20, abs_of_nonneg m30,
      abs_of_nonneg hh2, abs_of_nonneg hh3]
    norm_num
  have htri : |XF η σ y h| ≤ |T3 η σ y h| + E4 σ y * h ^ 4 / 6 := by
    have := abs_sub_abs_le_abs_sub (XF η σ y h) (T3 η σ y h)
    linarith
  unfold E4 at htri
  unfold U2 U34
  have a1 : M2 η * |G2 σ y| * h ^ 2 / 2 ≤ (Zc σ)⁻¹ * (η * h ^ 2 * envUp σ 2 2 y) := by
    have : M2 η * |G2 σ y| ≤ η * (2 * ((Zc σ)⁻¹ * envUp σ 2 2 y)) :=
      mul_le_mul m2le hG2 (abs_nonneg _) hη
    nlinarith
  have a2 : M3 η * |G3 σ y| * h ^ 3 / 6 ≤ (Zc σ)⁻¹ * (h ^ 3 * envUp σ 2 3 y) := by
    have : M3 η * |G3 σ y| ≤ 1 * (2 * ((Zc σ)⁻¹ * envUp σ 2 3 y)) :=
      mul_le_mul m3le hG3 (abs_nonneg _) zero_le_one
    nlinarith [mul_nonneg hZ.le e3]
  have a3 : 2 * ((Zc σ)⁻¹ * envUp σ 2 4 y) * h ^ 4 / 6 ≤ (Zc σ)⁻¹ * (h ^ 3 * envUp σ 2 4 y) := by
    nlinarith [mul_nonneg hZ.le e4]
  nlinarith

/-- **The density floor**: `p_v ≥ Zc⁻¹ envLo σ 2` for `v = ±1`, `|h| ≤ 1`, `η ≥ 0`. -/
theorem xdens_floor (η v h σ y : ℝ) (hη : 0 ≤ η) (hσ : 0 < σ) (hv : v = 1 ∨ v = -1)
    (hh : |h| ≤ 1) : (Zc σ)⁻¹ * envLo σ 2 y ≤ xdens η v h σ y := by
  unfold xdens
  have hZ : 0 ≤ (Zc σ)⁻¹ := (inv_pos.mpr (Zc_pos σ hσ)).le
  have hterm : ∀ w : Cube, (Zc σ)⁻¹ * envLo σ 2 y ≤ phi σ (y - (v * chiB w + h * gE η w)) := by
    intro w
    rw [phi_eq_gkern]
    refine mul_le_mul_of_nonneg_left ?_ hZ
    have hc : |v * chiB w + h * gE η w| ≤ 2 := by
      have hvc : |v * chiB w| = 1 := by
        rcases hv with rfl | rfl <;> rcases chiB_pm w with h' | h' <;> rw [h'] <;> norm_num
      have hhg : |h * gE η w| ≤ 1 := by
        rw [abs_mul]; nlinarith [gE_abs_le η hη w, abs_nonneg h, abs_nonneg (gE η w)]
      calc |v * chiB w + h * gE η w| ≤ |v * chiB w| + |h * gE η w| := abs_add_le _ _
        _ ≤ 2 := by linarith
    exact gaussian_lower_envelope σ 2 y _ hσ hc
  calc (Zc σ)⁻¹ * envLo σ 2 y = (1 / 8) * ∑ _w : Cube, (Zc σ)⁻¹ * envLo σ 2 y := by
        simp [Finset.card_univ]
    _ ≤ (1 / 8) * ∑ w : Cube, phi σ (y - (v * chiB w + h * gE η w)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => hterm w) (by norm_num)

theorem xdens_pos (η v h σ y : ℝ) (hσ : 0 < σ) : 0 < xdens η v h σ y := by
  unfold xdens
  exact mul_pos (by norm_num) (Finset.sum_pos (fun w _ => phi_pos σ _ hσ) Finset.univ_nonempty)

theorem continuous_xdens_y (η v h σ : ℝ) : Continuous fun y => xdens η v h σ y := by
  unfold xdens phi gaussianPDFReal; fun_prop

theorem continuous_xdens_h (η v σ y : ℝ) : Continuous fun h => xdens η v h σ y := by
  unfold xdens phi gaussianPDFReal; fun_prop

theorem continuous_XF_y (η σ h : ℝ) : Continuous fun y => XF η σ y h := by
  unfold XF gfun phi gaussianPDFReal; fun_prop

/-- Both worlds have density `p₀` at `h = 0`. -/
theorem xdens_zero (η v σ y : ℝ) (hv : v = 1 ∨ v = -1) : xdens η v 0 σ y = p0 σ y := by
  unfold xdens p0
  rw [sum_cube]
  simp only [zero_mul, add_zero, chiB, sb]
  rcases hv with rfl | rfl <;> norm_num <;> ring_nf

theorem xdens_tendsto (η v σ y : ℝ) (hv : v = 1 ∨ v = -1) :
    Tendsto (fun h => xdens η v h σ y) (𝓝[>] 0) (𝓝 (p0 σ y)) := by
  have := (continuous_xdens_h η v σ y).tendsto 0
  rw [xdens_zero η v σ y hv] at this
  exact this.mono_left nhdsWithin_le_nhds

/-! ## 7. The crossover law, upper half, uniform in `(h, η)` -/

/-- The `χ²` of the two worlds, reference world `v'`. -/
noncomputable def xchi (η σ v' h : ℝ) : ℝ := ∫ y, XF η σ y h ^ 2 / xdens η v' h σ y

noncomputable def IU (σ : ℝ) (k : ℕ) : ℝ := ∫ y, envUp σ 2 k y ^ 2 / envLo σ 2 y

/-- The uniform constant. -/
noncomputable def Kx (σ : ℝ) : ℝ := 2 * (Zc σ)⁻¹ * (IU σ 2 + 2 * (IU σ 3 + IU σ 4))

theorem chi_integrand_bound (η σ v' h y : ℝ) (hη : 0 ≤ η) (hσ : 0 < σ) (hv : v' = 1 ∨ v' = -1)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    XF η σ y h ^ 2 / xdens η v' h σ y
      ≤ 2 * (Zc σ)⁻¹ * (η ^ 2 * h ^ 4 * (envUp σ 2 2 y ^ 2 / envLo σ 2 y)
          + h ^ 6 * (2 * (envUp σ 2 3 y ^ 2 / envLo σ 2 y + envUp σ 2 4 y ^ 2 / envLo σ 2 y))) := by
  have hZc := Zc_pos σ hσ
  have hZ : 0 < (Zc σ)⁻¹ := inv_pos.mpr hZc
  have hlo := envLo_pos σ 2 y
  have hfl := xdens_floor η v' h σ y hη hσ hv (by rw [abs_of_pos hh]; exact hh1)
  have hflpos : 0 < (Zc σ)⁻¹ * envLo σ 2 y := mul_pos hZ hlo
  have hA := XF_abs_le η σ y h hη hσ hh hh1
  have hsq : XF η σ y h ^ 2 ≤ ((Zc σ)⁻¹ * (η * h ^ 2 * U2 σ y + h ^ 3 * U34 σ y)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have step1 : XF η σ y h ^ 2 / xdens η v' h σ y
      ≤ ((Zc σ)⁻¹ * (η * h ^ 2 * U2 σ y + h ^ 3 * U34 σ y)) ^ 2 / ((Zc σ)⁻¹ * envLo σ 2 y) :=
    div_le_div₀ (sq_nonneg _) hsq hflpos hfl
  refine step1.trans ?_
  unfold U2 U34
  set a := envUp σ 2 2 y
  set b := envUp σ 2 3 y
  set c := envUp σ 2 4 y
  set L := envLo σ 2 y
  have hx : (η * h ^ 2 * a + h ^ 3 * (b + c)) ^ 2
      ≤ 2 * ((η * h ^ 2 * a) ^ 2 + (h ^ 3 * (b + c)) ^ 2) := by
    nlinarith [sq_nonneg (η * h ^ 2 * a - h ^ 3 * (b + c))]
  have hbc : (b + c) ^ 2 ≤ 2 * (b ^ 2 + c ^ 2) := by nlinarith [sq_nonneg (b - c)]
  have hab : (η * h ^ 2 * a + h ^ 3 * (b + c)) ^ 2
      ≤ 2 * (η ^ 2 * h ^ 4 * a ^ 2 + h ^ 6 * (2 * (b ^ 2 + c ^ 2))) := by
    have h6 : 0 ≤ h ^ 6 := by positivity
    have : (h ^ 3 * (b + c)) ^ 2 ≤ h ^ 6 * (2 * (b ^ 2 + c ^ 2)) := by
      rw [mul_pow, ← pow_mul]; exact mul_le_mul_of_nonneg_left hbc h6
    have e : (η * h ^ 2 * a) ^ 2 = η ^ 2 * h ^ 4 * a ^ 2 := by ring
    nlinarith [hx, this, e]
  have lhs : ((Zc σ)⁻¹ * (η * h ^ 2 * a + h ^ 3 * (b + c))) ^ 2 / ((Zc σ)⁻¹ * L)
      = (Zc σ)⁻¹ * ((η * h ^ 2 * a + h ^ 3 * (b + c)) ^ 2 / L) := by
    field_simp
  have rhs : 2 * (Zc σ)⁻¹ * (η ^ 2 * h ^ 4 * (a ^ 2 / L) + h ^ 6 * (2 * (b ^ 2 / L + c ^ 2 / L)))
      = (Zc σ)⁻¹ * (2 * (η ^ 2 * h ^ 4 * a ^ 2 + h ^ 6 * (2 * (b ^ 2 + c ^ 2))) / L) := by
    field_simp
  rw [lhs, rhs]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hab hlo.le) hZ.le

/-- **The crossover law, upper half**: `χ²(h, η) ≤ Kx (η² h⁴ + h⁶)`, uniformly in `η ≥ 0` and
`0 < h ≤ 1`, with `Kx` independent of both. -/
theorem crossover_upper (η σ v' h : ℝ) (hη : 0 ≤ η) (hσ : 0 < σ) (hv : v' = 1 ∨ v' = -1)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    xchi η σ v' h ≤ Kx σ * (η ^ 2 * h ^ 4 + h ^ 6) := by
  have i2 := envRatio_integrable σ 2 hσ (by norm_num) 2
  have i3 := envRatio_integrable σ 2 hσ (by norm_num) 3
  have i4 := envRatio_integrable σ 2 hσ (by norm_num) 4
  have hbnd : Integrable (fun y => 2 * (Zc σ)⁻¹ * (η ^ 2 * h ^ 4 * (envUp σ 2 2 y ^ 2 / envLo σ 2 y)
      + h ^ 6 * (2 * (envUp σ 2 3 y ^ 2 / envLo σ 2 y + envUp σ 2 4 y ^ 2 / envLo σ 2 y)))) :=
    ((i2.const_mul _).add (((i3.add i4).const_mul 2).const_mul _)).const_mul _
  have hmeas : AEStronglyMeasurable (fun y => XF η σ y h ^ 2 / xdens η v' h σ y) :=
    (((continuous_XF_y η σ h).pow 2).div (continuous_xdens_y η v' h σ)
      (fun y => (xdens_pos η v' h σ y hσ).ne')).aestronglyMeasurable
  have hint : Integrable (fun y => XF η σ y h ^ 2 / xdens η v' h σ y) := by
    refine hbnd.mono' hmeas (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (xdens_pos η v' h σ y hσ).le)]
    exact chi_integrand_bound η σ v' h y hη hσ hv hh hh1
  unfold xchi
  refine (integral_mono hint hbnd fun y => chi_integrand_bound η σ v' h y hη hσ hv hh hh1).trans ?_
  have j34 : ∫ y, (envUp σ 2 3 y ^ 2 / envLo σ 2 y + envUp σ 2 4 y ^ 2 / envLo σ 2 y)
      = IU σ 3 + IU σ 4 := integral_add i3 i4
  have jA : Integrable (fun y => η ^ 2 * h ^ 4 * (envUp σ 2 2 y ^ 2 / envLo σ 2 y)) := i2.const_mul _
  have jB : Integrable (fun y => h ^ 6 * (2 * (envUp σ 2 3 y ^ 2 / envLo σ 2 y
      + envUp σ 2 4 y ^ 2 / envLo σ 2 y))) := ((i3.add i4).const_mul 2).const_mul _
  have jsum : ∫ y, (η ^ 2 * h ^ 4 * (envUp σ 2 2 y ^ 2 / envLo σ 2 y)
      + h ^ 6 * (2 * (envUp σ 2 3 y ^ 2 / envLo σ 2 y + envUp σ 2 4 y ^ 2 / envLo σ 2 y)))
      = η ^ 2 * h ^ 4 * IU σ 2 + h ^ 6 * (2 * (IU σ 3 + IU σ 4)) := by
    rw [integral_add jA jB, integral_const_mul, integral_const_mul, integral_const_mul, j34]
    rfl
  rw [integral_const_mul, jsum]
  have In : ∀ k : ℕ, 0 ≤ IU σ k := fun k =>
    integral_nonneg fun y => div_nonneg (sq_nonneg _) (envLo_pos σ 2 y).le
  have hZ : 0 ≤ (Zc σ)⁻¹ := (inv_pos.mpr (Zc_pos σ hσ)).le
  have hA : 0 ≤ η ^ 2 * h ^ 4 := by positivity
  have hB : 0 ≤ h ^ 6 := by positivity
  unfold Kx
  have i2 := In 2; have i3 := In 3; have i4 := In 4
  have key : η ^ 2 * h ^ 4 * IU σ 2 + h ^ 6 * (2 * (IU σ 3 + IU σ 4))
      ≤ (IU σ 2 + 2 * (IU σ 3 + IU σ 4)) * (η ^ 2 * h ^ 4 + h ^ 6) := by
    nlinarith [mul_nonneg hA (add_nonneg i3 i4), mul_nonneg hB i2]
  have := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ 2 * (Zc σ)⁻¹)
  linarith

/-- **At `η ≍ h` the exponent does NOT change**: along `η = c h`, `χ² ≤ Kx (c² + 1) h⁶`, the
order of the linear probe.  A nonlinear capability of order `h` does not erase the separation;
it takes `η ≫ h` (for instance a fixed `η > 0`, see `crossover_fixed_eta`). -/
theorem crossover_eta_of_order_h (c σ v' h : ℝ) (hc : 0 ≤ c) (hσ : 0 < σ) (hv : v' = 1 ∨ v' = -1)
    (hh : 0 < h) (hh1 : h ≤ 1) :
    xchi (c * h) σ v' h ≤ Kx σ * (c ^ 2 + 1) * h ^ 6 := by
  have := crossover_upper (c * h) σ v' h (mul_nonneg hc hh.le) hσ hv hh hh1
  calc xchi (c * h) σ v' h ≤ Kx σ * ((c * h) ^ 2 * h ^ 4 + h ^ 6) := this
    _ = Kx σ * (c ^ 2 + 1) * h ^ 6 := by ring

/-! ## 8. The two regimes at fixed `η`: exact limits (the lower halves) -/

theorem aj2_eq (σ y : ℝ) : G2 σ y = 4 * aj 2 σ y := by unfold aj G2; norm_num; ring
theorem aj3_eq (σ y : ℝ) : G3 σ y = 27 * aj 3 σ y := by unfold aj G3; norm_num; ring

/-- Pointwise leading term, `η > 0`: `XF/h² → M₂ G₂ / 2`. -/
theorem lead2 (η σ y : ℝ) (hη : 0 ≤ η) (hσ : 0 < σ) :
    Tendsto (fun h => XF η σ y h / h ^ 2) (𝓝[>] 0) (𝓝 (M2 η * G2 σ y / 2)) := by
  have hbound : Tendsto (fun h => |M3 η * G3 σ y| * h / 6 + E4 σ y * h ^ 2 / 6) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun h : ℝ => |M3 η * G3 σ y| * h / 6 + E4 σ y * h ^ 2 / 6) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun h : ℝ => |M3 η * G3 σ y| * h / 6 + E4 σ y * h ^ 2 / 6) := by
        fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
  have hT := XF_taylor η σ y h hη hσ hh.1 hh.2
  have hh2 : 0 < h ^ 2 := by have := hh.1; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  have hh0 : h ≠ 0 := hh.1.ne'
  have e : XF η σ y h / h ^ 2 - M2 η * G2 σ y / 2
      = (XF η σ y h - T3 η σ y h) / h ^ 2 + M3 η * G3 σ y * h / 6 := by
    unfold T3; field_simp; ring
  rw [e]
  have h1 : |(XF η σ y h - T3 η σ y h) / h ^ 2| ≤ E4 σ y * h ^ 2 / 6 := by
    rw [abs_div, abs_of_pos hh2, div_le_iff₀ hh2]
    calc |XF η σ y h - T3 η σ y h| ≤ E4 σ y * h ^ 4 / 6 := hT
      _ = E4 σ y * h ^ 2 / 6 * h ^ 2 := by ring
  have h2 : |M3 η * G3 σ y * h / 6| = |M3 η * G3 σ y| * h / 6 := by
    rw [abs_div, abs_mul, abs_of_pos hh.1]; norm_num
  calc |(XF η σ y h - T3 η σ y h) / h ^ 2 + M3 η * G3 σ y * h / 6|
      ≤ |(XF η σ y h - T3 η σ y h) / h ^ 2| + |M3 η * G3 σ y * h / 6| := abs_add_le _ _
    _ ≤ |M3 η * G3 σ y| * h / 6 + E4 σ y * h ^ 2 / 6 := by rw [h2]; linarith

/-- Pointwise leading term, `η = 0`: `XF/h³ → M₃ G₃ / 6`. -/
theorem lead3 (σ y : ℝ) (hσ : 0 < σ) :
    Tendsto (fun h => XF 0 σ y h / h ^ 3) (𝓝[>] 0) (𝓝 (M3 0 * G3 σ y / 6)) := by
  have hbound : Tendsto (fun h => E4 σ y * h / 6) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun h : ℝ => E4 σ y * h / 6) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun h : ℝ => E4 σ y * h / 6) := by fun_prop
      simpa using hc.tendsto 0
    exact this.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
  have hT := XF_taylor 0 σ y h le_rfl hσ hh.1 hh.2
  have hh3 : 0 < h ^ 3 := by have := hh.1; positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
  have hh0 : h ≠ 0 := hh.1.ne'
  have e : XF 0 σ y h / h ^ 3 - M3 0 * G3 σ y / 6 = (XF 0 σ y h - T3 0 σ y h) / h ^ 3 := by
    unfold T3 M2; field_simp; ring
  rw [e, abs_div, abs_of_pos hh3, div_le_iff₀ hh3]
  calc |XF 0 σ y h - T3 0 σ y h| ≤ E4 σ y * h ^ 4 / 6 := hT
    _ = E4 σ y * h / 6 * h ^ 3 := by ring

/-- **Regime `η > 0`: the rate is `h⁴`, with an explicit positive constant.**
`χ²(h, η)/h⁴ → 32 η² / (3+η)⁴ · c₂` as `h → 0⁺`, where `c₂ = cj 2 σ > 0`. -/
theorem crossover_fixed_eta (η σ v' : ℝ) (hη : 0 ≤ η) (hσ : 0 < σ) (hv : v' = 1 ∨ v' = -1) :
    Tendsto (fun h => xchi η σ v' h / h ^ 4) (𝓝[>] 0)
      (𝓝 (32 * η ^ 2 / (3 + η) ^ 4 * cj 2 σ)) := by
  have hZc := Zc_pos σ hσ
  have hZ : 0 < (Zc σ)⁻¹ := inv_pos.mpr hZc
  have hval : 32 * η ^ 2 / (3 + η) ^ 4 * cj 2 σ = ∫ y, (M2 η * G2 σ y / 2) ^ 2 / p0 σ y := by
    have e : ∀ y, (M2 η * G2 σ y / 2) ^ 2 / p0 σ y = (4 * M2 η ^ 2) * (aj 2 σ y ^ 2 / p0 σ y) := by
      intro y; rw [aj2_eq]; ring
    simp_rw [e]
    rw [integral_const_mul]
    unfold cj M2
    have h3 : (3 + η) ≠ 0 := by linarith
    field_simp
    ring
  rw [hval]
  have heq : (fun h => xchi η σ v' h / h ^ 4)
      = fun h => ∫ y, (XF η σ y h / h ^ 2) ^ 2 / xdens η v' h σ y := by
    funext h
    unfold xchi
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [div_pow, ← pow_mul]
    ring
  rw [heq]
  set B : ℝ → ℝ := fun y => 2 * (Zc σ)⁻¹ * (η ^ 2 * (envUp σ 2 2 y ^ 2 / envLo σ 2 y)
      + 2 * (envUp σ 2 3 y ^ 2 / envLo σ 2 y + envUp σ 2 4 y ^ 2 / envLo σ 2 y)) with hB
  have i2 := envRatio_integrable σ 2 hσ (by norm_num) 2
  have i3 := envRatio_integrable σ 2 hσ (by norm_num) 3
  have i4 := envRatio_integrable σ 2 hσ (by norm_num) 4
  have hBint : Integrable B := ((i2.const_mul _).add ((i3.add i4).const_mul 2)).const_mul _
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hBint ?_
  · refine Filter.Eventually.of_forall fun h => ?_
    exact ((((continuous_XF_y η σ h).div_const _).pow 2).div (continuous_xdens_y η v' h σ)
      (fun y => (xdens_pos η v' h σ y hσ).ne')).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
    refine Filter.Eventually.of_forall fun y => ?_
    have hpos := xdens_pos η v' h σ y hσ
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le)]
    have hh2 : 0 < h ^ 2 := by have := hh.1; positivity
    have hA := XF_abs_le η σ y h hη hσ hh.1 hh.2
    have hU2 := U2_nonneg σ y
    have hU34 := U34_nonneg σ y
    have habs : |XF η σ y h / h ^ 2| ≤ (Zc σ)⁻¹ * (η * U2 σ y + U34 σ y) := by
      rw [abs_div, abs_of_pos hh2, div_le_iff₀ hh2]
      refine hA.trans ?_
      have : h ^ 3 ≤ h ^ 2 := pow_le_pow_of_le_one hh.1.le hh.2 (by norm_num)
      nlinarith [mul_nonneg hZ.le hU34, mul_nonneg hZ.le (mul_nonneg hη hU2)]
    have hfl := xdens_floor η v' h σ y hη hσ hv (by rw [abs_of_pos hh.1]; exact hh.2)
    have hlo := envLo_pos σ 2 y
    have hflpos : 0 < (Zc σ)⁻¹ * envLo σ 2 y := mul_pos hZ hlo
    have hsq : (XF η σ y h / h ^ 2) ^ 2 ≤ ((Zc σ)⁻¹ * (η * U2 σ y + U34 σ y)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    refine (div_le_div₀ (sq_nonneg _) hsq hflpos hfl).trans ?_
    simp only [hB]
    unfold U2 U34
    set a := envUp σ 2 2 y
    set b := envUp σ 2 3 y
    set c := envUp σ 2 4 y
    set L := envLo σ 2 y
    have hab : (η * a + (b + c)) ^ 2 ≤ 2 * (η ^ 2 * a ^ 2 + 2 * (b ^ 2 + c ^ 2)) := by
      nlinarith [sq_nonneg (η * a - (b + c)), sq_nonneg (b - c)]
    have lhs : ((Zc σ)⁻¹ * (η * a + (b + c))) ^ 2 / ((Zc σ)⁻¹ * L)
        = (Zc σ)⁻¹ * ((η * a + (b + c)) ^ 2 / L) := by field_simp
    have rhs : 2 * (Zc σ)⁻¹ * (η ^ 2 * (a ^ 2 / L) + 2 * (b ^ 2 / L + c ^ 2 / L))
        = (Zc σ)⁻¹ * (2 * (η ^ 2 * a ^ 2 + 2 * (b ^ 2 + c ^ 2)) / L) := by field_simp
    rw [lhs, rhs]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hab hlo.le) hZ.le
  · exact Filter.Eventually.of_forall fun y =>
      ((lead2 η σ y hη hσ).pow 2).div (xdens_tendsto η v' σ y hv) (p0_pos σ y hσ).ne'

/-- **Regime `η = 0`: the rate is `h⁶`.**  `χ²(h, 0)/h⁶ → 2 c₃`, `c₃ = cj 3 σ > 0`: the linear
probe's parity order, recovered from the same mixture. -/
theorem crossover_zero_eta (σ v' : ℝ) (hσ : 0 < σ) (hv : v' = 1 ∨ v' = -1) :
    Tendsto (fun h => xchi 0 σ v' h / h ^ 6) (𝓝[>] 0) (𝓝 (2 * cj 3 σ)) := by
  have hZc := Zc_pos σ hσ
  have hZ : 0 < (Zc σ)⁻¹ := inv_pos.mpr hZc
  have hval : 2 * cj 3 σ = ∫ y, (M3 0 * G3 σ y / 6) ^ 2 / p0 σ y := by
    have e : ∀ y, (M3 0 * G3 σ y / 6) ^ 2 / p0 σ y = aj 3 σ y ^ 2 / p0 σ y := by
      intro y; rw [aj3_eq]; unfold M3; norm_num; ring
    simp_rw [e]
    unfold cj; ring
  rw [hval]
  have heq : (fun h => xchi 0 σ v' h / h ^ 6)
      = fun h => ∫ y, (XF 0 σ y h / h ^ 3) ^ 2 / xdens 0 v' h σ y := by
    funext h
    unfold xchi
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [div_pow, ← pow_mul]
    ring
  rw [heq]
  set B : ℝ → ℝ := fun y => 2 * (Zc σ)⁻¹ * (envUp σ 2 3 y ^ 2 / envLo σ 2 y
      + envUp σ 2 4 y ^ 2 / envLo σ 2 y) with hB
  have i3 := envRatio_integrable σ 2 hσ (by norm_num) 3
  have i4 := envRatio_integrable σ 2 hσ (by norm_num) 4
  have hBint : Integrable B := (i3.add i4).const_mul _
  refine tendsto_integral_filter_of_dominated_convergence B ?_ ?_ hBint ?_
  · refine Filter.Eventually.of_forall fun h => ?_
    exact ((((continuous_XF_y 0 σ h).div_const _).pow 2).div (continuous_xdens_y 0 v' h σ)
      (fun y => (xdens_pos 0 v' h σ y hσ).ne')).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with h hh
    refine Filter.Eventually.of_forall fun y => ?_
    have hpos := xdens_pos 0 v' h σ y hσ
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le)]
    have hh3 : 0 < h ^ 3 := by have := hh.1; positivity
    have hA := XF_abs_le 0 σ y h le_rfl hσ hh.1 hh.2
    have hU34 := U34_nonneg σ y
    have habs : |XF 0 σ y h / h ^ 3| ≤ (Zc σ)⁻¹ * U34 σ y := by
      rw [abs_div, abs_of_pos hh3, div_le_iff₀ hh3]
      refine hA.trans (le_of_eq ?_)
      ring
    have hfl := xdens_floor 0 v' h σ y le_rfl hσ hv (by rw [abs_of_pos hh.1]; exact hh.2)
    have hlo := envLo_pos σ 2 y
    have hflpos : 0 < (Zc σ)⁻¹ * envLo σ 2 y := mul_pos hZ hlo
    have hsq : (XF 0 σ y h / h ^ 3) ^ 2 ≤ ((Zc σ)⁻¹ * U34 σ y) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    refine (div_le_div₀ (sq_nonneg _) hsq hflpos hfl).trans ?_
    simp only [hB]
    unfold U34
    set b := envUp σ 2 3 y
    set c := envUp σ 2 4 y
    set L := envLo σ 2 y
    have hbc : (b + c) ^ 2 ≤ 2 * (b ^ 2 + c ^ 2) := by nlinarith [sq_nonneg (b - c)]
    have lhs : ((Zc σ)⁻¹ * (b + c)) ^ 2 / ((Zc σ)⁻¹ * L) = (Zc σ)⁻¹ * ((b + c) ^ 2 / L) := by
      field_simp
    have rhs : 2 * (Zc σ)⁻¹ * (b ^ 2 / L + c ^ 2 / L) = (Zc σ)⁻¹ * (2 * (b ^ 2 + c ^ 2) / L) := by
      field_simp
    rw [lhs, rhs]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hbc hlo.le) hZ.le
  · exact Filter.Eventually.of_forall fun y =>
      ((lead3 σ y hσ).pow 2).div (xdens_tendsto 0 v' σ y hv) (p0_pos σ y hσ).ne'

/-- The two limit constants are strictly positive (for `η > 0` in the first regime). -/
theorem crossover_constants_pos (η σ : ℝ) (hη : 0 < η) (hσ : 0 < σ) :
    0 < 32 * η ^ 2 / (3 + η) ^ 4 * cj 2 σ ∧ 0 < 2 * cj 3 σ := by
  have c2 := cj_pos 2 (by norm_num) σ hσ
  have c3 := cj_pos 3 (by norm_num) σ hσ
  constructor
  · have : 0 < 32 * η ^ 2 / (3 + η) ^ 4 := by positivity
    positivity
  · positivity

end CIGAMF.P13.PaperBCrossoverRate

#print axioms CIGAMF.P13.PaperBCrossoverRate.XF_taylor
#print axioms CIGAMF.P13.PaperBCrossoverRate.XF_abs_le
#print axioms CIGAMF.P13.PaperBCrossoverRate.xdens_floor
#print axioms CIGAMF.P13.PaperBCrossoverRate.crossover_upper
#print axioms CIGAMF.P13.PaperBCrossoverRate.crossover_eta_of_order_h
#print axioms CIGAMF.P13.PaperBCrossoverRate.crossover_fixed_eta
#print axioms CIGAMF.P13.PaperBCrossoverRate.crossover_zero_eta
#print axioms CIGAMF.P13.PaperBCrossoverRate.crossover_constants_pos
