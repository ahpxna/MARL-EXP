import «LeanPaperBChannelPairV1»

/-!
# Paper B: the rate bound at the decoder's own pair, and the normalisation

`channel_pair_diff` showed the decoder's two densities differ by the iterated symmetric
difference of `pairBase φ = φ(.-1) - φ(.+1)`, not of `φ`.  That left two things owed, both
named in `PROOFS.md` §9: applying the envelope to each component and adding, and carrying
the UNNORMALISED kernel `gkern` over to probability laws.  Both are here.

**Componentwise.**  `pair_iterDiff_split` writes the pair's difference as a difference of
two iterated differences, each of a TRANSLATE of the mixture.  A translate of a mixture is
the mixture with its centres shifted (`mixDens_translate`), so each component is covered by
`iterDiff_mixture_envelope` at radius `R+1` instead of `R`.  The triangle inequality then
gives the pair a factor of two, and squaring gives the chi-square bound a factor of four --
`pair_chi2_bound`.  Nothing about the pair is assumed; the factor is paid, not hidden.

**Normalisation.**  `gkern sigma y = exp(-y^2/(2 sigma^2))` is the unnormalised Gaussian, so
a bound proved for it is a bound about a measure of total mass `sigma sqrt(2 pi)`, not about
a probability law.  `gkern_integral` computes that mass and `kl_scale`, `chi2_scale` say how
the two functionals transform: the divergence of the normalised pair is the unnormalised one
divided by the mass.  So the bounds transfer with an explicit constant rather than by
assertion.
-/

namespace CIGAMF.P13.PaperBPairRate

open MeasureTheory
open CIGAMF.P13.PaperBRates
open CIGAMF.P13.PaperBWorlds
open CIGAMF.P13.PaperBChannelPair

/-! ## A translate of a mixture is a mixture -/

theorem mixDens_translate (σ : ℝ) (n : ℕ) (w cs : Fin n → ℝ) (t : ℝ) :
    (fun u => mixDens σ n w cs (u - t)) = fun z => ∑ j, w j * gkern σ (z - (cs j + t)) := by
  funext u
  unfold mixDens
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 2
  ring

/-- **Each component of the pair carries the mixture envelope**, at radius `R+1`: the
translate moves every centre by at most one. -/
theorem pair_component_envelope (σ R h₀ : ℝ) (hσ : 0 < σ) (hR : 0 ≤ R) (hh₀ : 0 ≤ h₀)
    (r n : ℕ) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j ≤ 1)
    (cs : Fin n → ℝ) (hcs : ∀ j, |cs j| ≤ R) (t : ℝ) (ht : |t| ≤ 1)
    (b : Fin r → ℝ) (hb : ∑ i, |b i| ≤ h₀) (y : ℝ) :
    |iterDiff (fun u => mixDens σ n w cs (u - t)) (List.ofFn b) y|
      ≤ (∏ i, |b i|) * envUp σ (R + 1 + h₀) r y := by
  rw [mixDens_translate σ n w cs t]
  have hcs' : ∀ j, |cs j + t| ≤ R + 1 := by
    intro j
    calc |cs j + t| ≤ |cs j| + |t| := abs_add_le _ _
      _ ≤ R + 1 := by linarith [hcs j, ht]
  have h := iterDiff_mixture_envelope σ (R + 1) h₀ hσ (by linarith) hh₀ r n w hw hw1
    (fun j => cs j + t) hcs' b hb y
  exact h

/-- **The pair's difference, with the factor of two the split costs.** -/
theorem pair_envelope (σ R h₀ : ℝ) (hσ : 0 < σ) (hR : 0 ≤ R) (hh₀ : 0 ≤ h₀)
    (r n : ℕ) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j ≤ 1)
    (cs : Fin n → ℝ) (hcs : ∀ j, |cs j| ≤ R)
    (b : Fin r → ℝ) (hb : ∑ i, |b i| ≤ h₀) (y : ℝ) :
    |iterDiff (pairBase (mixDens σ n w cs)) (List.ofFn b) y|
      ≤ 2 * ((∏ i, |b i|) * envUp σ (R + 1 + h₀) r y) := by
  have hsplit := pair_iterDiff_split (r := r) (mixDens σ n w cs) b y
  have hminus : (fun u => mixDens σ n w cs (u - 1))
      = fun u => mixDens σ n w cs (u - 1) := rfl
  have hplus : (fun u : ℝ => mixDens σ n w cs (u + 1))
      = fun u => mixDens σ n w cs (u - (-1)) := by
    funext u; congr 1; ring
  have h1 := pair_component_envelope σ R h₀ hσ hR hh₀ r n w hw hw1 cs hcs 1
    (by norm_num) b hb y
  have h2 := pair_component_envelope σ R h₀ hσ hR hh₀ r n w hw hw1 cs hcs (-1)
    (by norm_num) b hb y
  rw [← hplus] at h2
  rw [hsplit]
  calc |iterDiff (fun u => mixDens σ n w cs (u - 1)) (List.ofFn b) y
          - iterDiff (fun u => mixDens σ n w cs (u + 1)) (List.ofFn b) y|
      ≤ |iterDiff (fun u => mixDens σ n w cs (u - 1)) (List.ofFn b) y|
        + |iterDiff (fun u => mixDens σ n w cs (u + 1)) (List.ofFn b) y| := abs_sub _ _
    _ ≤ 2 * ((∏ i, |b i|) * envUp σ (R + 1 + h₀) r y) := by linarith [h1, h2]

/-- **The chi-square bound at the decoder's pair.**  The same `h^{2r}` rate as the
constructed pair, with the factor `4` the componentwise split costs, and with the radius
enlarged by the translate. -/
theorem pair_chi2_bound (σ R h₀ h : ℝ) (r n : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hh₀ : 0 ≤ h₀) (hh : 0 ≤ h) (a : Fin r → ℝ) (ha : ∑ i, |a i| ≤ 1)
    (hscale : ∑ i, |h * a i| ≤ h₀)
    (w cs : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j ≤ 1) (hcs : ∀ j, |cs j| ≤ R) :
    ∫ y, (iterDiff (pairBase (mixDens σ n w cs)) (List.ofFn (fun i => h * a i)) y) ^ 2
          / envLo σ (R + 1 + h₀) y
      ≤ 4 * (h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2 * klConst σ (R + 1) h₀ r) := by
  have hhalf := hellinger_rate_bound σ (R + 1 + h₀) h r hr hσ (by linarith) hh a ha
    (fun y => iterDiff (pairBase (mixDens σ n w cs)) (List.ofFn (fun i => h * a i)) y / 2)
    (envLo σ (R + 1 + h₀)) (fun y => ?_) (fun y => le_rfl)
  · have hpull : ∫ y, (iterDiff (pairBase (mixDens σ n w cs))
          (List.ofFn (fun i => h * a i)) y / 2) ^ 2 / envLo σ (R + 1 + h₀) y
        = (1 / 4) * ∫ y, (iterDiff (pairBase (mixDens σ n w cs))
            (List.ofFn (fun i => h * a i)) y) ^ 2 / envLo σ (R + 1 + h₀) y := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      field_simp
      ring
    rw [hpull] at hhalf
    unfold klConst
    linarith [hhalf]
  · have hpe := pair_envelope σ R h₀ hσ hR hh₀ r n w hw hw1 cs hcs (fun i => h * a i)
      hscale y
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    linarith [hpe]

/-! ## The unnormalised kernel, and what normalising costs -/

/-- **The kernel's total mass.**  `gkern` is the unnormalised Gaussian; dividing by this is
what turns the pair into probability laws. -/
theorem gkern_integral (σ : ℝ) (hσ : 0 < σ) :
    ∫ y, gkern σ y = σ * Real.sqrt (2 * Real.pi) := by
  have hb : (0 : ℝ) < 1 / (2 * σ ^ 2) := by positivity
  have hrw : (fun y : ℝ => gkern σ y) = fun y : ℝ => Real.exp (-(1 / (2 * σ ^ 2)) * y ^ 2) := by
    funext y
    unfold gkern
    congr 1
    field_simp
  rw [hrw, integral_gaussian]
  have harg : Real.pi / (1 / (2 * σ ^ 2)) = 2 * Real.pi * σ ^ 2 := by
    field_simp
  rw [harg, show 2 * Real.pi * σ ^ 2 = σ ^ 2 * (2 * Real.pi) from by ring,
    Real.sqrt_mul (by positivity)]
  rw [Real.sqrt_sq hσ.le]

/-- **The divergence of the normalised pair.**  Dividing both densities by the same mass
leaves the log-ratio alone and scales the integral, so the bound transfers with the explicit
constant `1/Z`. -/
theorem kl_scale (Z : ℝ) (hZ : 0 < Z) (P Q : ℝ → ℝ) :
    ∫ y, (P y / Z) * Real.log ((P y / Z) / (Q y / Z))
      = (1 / Z) * ∫ y, P y * Real.log (P y / Q y) := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  have hZ0 : Z ≠ 0 := ne_of_gt hZ
  show P y / Z * Real.log (P y / Z / (Q y / Z)) = 1 / Z * (P y * Real.log (P y / Q y))
  have hratio : P y / Z / (Q y / Z) = P y / Q y := by
    field_simp
  rw [hratio]
  ring

/-- **And of the chi-square.**  Here the envelope is scaled too, so the net factor is again
`1/Z`. -/
theorem chi2_scale (Z : ℝ) (hZ : 0 < Z) (Δ L : ℝ → ℝ) :
    ∫ y, (Δ y / Z) ^ 2 / (L y / Z) = (1 / Z) * ∫ y, (Δ y) ^ 2 / L y := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  have hZ0 : Z ≠ 0 := ne_of_gt hZ
  show (Δ y / Z) ^ 2 / (L y / Z) = 1 / Z * ((Δ y) ^ 2 / L y)
  by_cases hL : L y = 0
  · simp [hL]
  · field_simp

/-! ## Audit -/

#print axioms mixDens_translate
#print axioms pair_component_envelope
#print axioms pair_envelope
#print axioms pair_chi2_bound
#print axioms gkern_integral
#print axioms kl_scale
#print axioms chi2_scale

end CIGAMF.P13.PaperBPairRate
