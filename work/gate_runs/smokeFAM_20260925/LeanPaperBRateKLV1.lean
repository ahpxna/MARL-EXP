import «LeanPaperBRatesV1»
import «LeanPaperBKLV1»

/-!
# Paper B: the divergence rate, composed from the envelope already proved

`LeanPaperBRatesV1.mixture_hellinger_rate` bounds

    integral ( iterDiff (mixture) shifts y )^2 / ( sum_j w_j gkern sigma (y - c_j) )
      <=  h^(2r) * (1/r)^(2r) * integral envUp^2 / envLo,

and the denominator there is the mixture density itself.  `LeanPaperBKLV1.kl_le_envelope`
turns exactly that quantity into a bound on the Kullback-Leibler divergence.  So the two
compose, and what is left of "KL uniform over the query class" is a single identification:
that the two worlds' density DIFFERENCE is the iterated difference the envelope bounds.

That identification is carried here as a hypothesis, named `hdiff`, rather than assumed away
--- it is the one modelling step still owed, and stating it explicitly is what keeps the
composition honest.  Everything else in the chain is proved.

WHAT REMAINS AFTER THIS FILE.  `hdiff` at the actual observation model, **uniformly over the
admissible query class**: the shifts must be those the query induces, for every query in the
class, with the constant independent of the query.  Nothing here establishes that.
-/

namespace CIGAMF.P13.PaperBRate

open MeasureTheory
open CIGAMF.P13.PaperBRates
open CIGAMF.P13.PaperBKL

/-- **A finite mixture of Gaussian kernels is strictly positive.**  Needed because the
divergence divides by it. -/
theorem mixture_pos {n : ℕ} (σ : ℝ) (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) (cs : Fin n → ℝ) (y : ℝ) :
    0 < ∑ j, w j * gkern σ (y - cs j) := by
  classical
  rcases Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw1]; exact one_ne_zero) with ⟨j, -, hj⟩
  have hpos : 0 < w j * gkern σ (y - cs j) :=
    mul_pos (lt_of_le_of_ne (hw j) (Ne.symm hj)) (gkern_pos σ (y - cs j))
  refine Finset.sum_pos' (fun i _ => mul_nonneg (hw i) (gkern_pos σ (y - cs i)).le)
    ⟨j, Finset.mem_univ j, hpos⟩

/-- **The divergence rate, composed.**  Given the density-difference identification, the
Kullback-Leibler divergence inherits the envelope's `h^{2r}` rate --- with the floor taken
to be the density itself, which is the tightest case. -/
theorem kl_rate_of_mixture {n : ℕ}
    (σ R h₀ h : ℝ) (r : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hR : 0 ≤ R) (hh₀ : 0 ≤ h₀)
    (hh : 0 ≤ h) (a : Fin r → ℝ) (ha : ∑ i, |a i| ≤ 1) (hscale : ∑ i, |h * a i| ≤ h₀)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (cs : Fin n → ℝ) (hcs : ∀ j, |cs j| ≤ R)
    (p q : ℝ → ℝ) (hp : ∀ y, 0 ≤ p y)
    (hq : ∀ y, q y = ∑ j, w j * gkern σ (y - cs j))
    (hdiff : ∀ y, p y - q y
      = iterDiff (fun z => ∑ j, w j * gkern σ (z - cs j))
          (List.ofFn (fun i => h * a i)) y)
    (hkl : Integrable (fun y => p y * Real.log (p y / q y)) volume)
    (henv : Integrable (fun y => (p y - q y) ^ 2 / q y) volume)
    (hdiffint : Integrable (fun y => p y - q y) volume)
    (hmass : ∫ y, (p y - q y) = 0) :
    ∫ y, p y * Real.log (p y / q y)
      ≤ h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2
        * ∫ y, envUp σ (R + h₀) r y ^ 2 / envLo σ (R + h₀) y := by
  have hqpos : ∀ y, 0 < q y := fun y => by
    rw [hq y]; exact mixture_pos σ w hw hw1 cs y
  -- the KL inequality, with the floor taken to be the density itself
  have hkle : ∫ y, p y * Real.log (p y / q y) ≤ ∫ y, (p y - q y) ^ 2 / q y :=
    kl_le_envelope volume p q q hp hqpos hqpos (fun y => le_rfl) hkl henv hdiffint hmass
  -- the envelope bound, at the same integrand
  have hrw : (fun y : ℝ => (p y - q y) ^ 2 / q y)
      = fun y : ℝ => (iterDiff (fun z => ∑ j, w j * gkern σ (z - cs j))
          (List.ofFn (fun i => h * a i)) y) ^ 2 / (∑ j, w j * gkern σ (y - cs j)) := by
    funext y
    rw [hdiff y, hq y]
  rw [hrw] at hkle
  exact le_trans hkle
    (mixture_hellinger_rate σ R h₀ h r n hr hσ hR hh₀ hh a ha hscale w hw hw1 cs hcs)

/-! ## Audit -/

#print axioms mixture_pos
#print axioms kl_rate_of_mixture

end CIGAMF.P13.PaperBRate
