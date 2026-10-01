import «LeanQueryGaussianLevelV1»

/-! # Query Q3: the mixture's `h`-expansion, assembled from the per-component law.

`LeanQueryGaussianLevelV1` proves everything about ONE mixture component
(`iteratedDeriv_shift`) and everything about the level sum once the coefficients are in
hand (`levelSum_eq_zero_of_levels_agree`, `levelSum_ne_zero`).  What was missing between
them is bookkeeping: the observation density is a finite SUM

    p_{W,h}(y) = ∑_x π_x φ_σ(y - f_W(x) - h g(x)),

and `iteratedDeriv` must be pushed through that sum.  Mathlib has
`iteratedFDeriv_fun_sum_apply` for the multilinear iterated derivative but no
scalar-variable counterpart, so `iteratedDeriv_fun_sum` below supplies it, and
`iteratedDeriv_mixture` is the assembly.

## WHAT IS PROVED

* `iteratedDeriv_fun_sum` — `iteratedDeriv` commutes with `Finset.sum` for functions that
  are `ContDiffAt` at the point.  This is the lemma Mathlib lacks.
* `contDiff_component` — each mixture component is smooth in `h`; the hypothesis of the
  previous lemma is therefore discharged, never assumed.
* `iteratedDeriv_mixture` — the `j`-th derivative in `h` at `h = 0` of the WHOLE mixture
  is exactly `levelSum σ j (image f univ) (levelMoment π f g j)`.  This is the step the
  Q3 audit recorded as the one remaining piece.
* `mixture_coeff_diff_eq_zero` — order-`j` cancellation for two worlds whose level
  moments agree: the easy half, now stated on the mixture rather than on the level sum.
* `mixture_coeff_ne_zero` — the top level with a nonzero moment forces the order-`r`
  coefficient of the mixture to be somewhere nonzero: the hard half, likewise transported
  to the mixture.

## WHAT THIS DOES NOT ESTABLISH

- The normalising constant `1/(σ√(2π))` and the factor `1/j!` are positive constants and
  are dropped throughout, exactly as in `LeanQueryGaussianLevelV1`; they change no
  vanishing statement but the manuscript must not quote these as densities.
- Nothing here bounds `H²`; the Hellinger assembly lives in the 3b/3c modules.
- `mixture_coeff_diff_eq_zero` assumes the two worlds share a level set.  Worlds with
  different level sets are not covered by that statement.
-/

namespace CIGAMF.P13.QueryMixtureDerivative

open Polynomial Finset
open CIGAMF.P13.QueryGaussianLevel

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Each mixture component is smooth in the perturbation parameter `h`. -/
theorem contDiff_component (σ : ℝ) (v g y : ℝ) (n : ℕ) :
    ContDiff ℝ n (fun h : ℝ => gauss σ (y - v - h * g)) := by
  have hin : ContDiff ℝ n (fun h : ℝ => -((y - v - h * g) ^ 2) / (2 * σ ^ 2)) :=
    (((contDiff_const.sub (contDiff_id.mul contDiff_const)).pow 2).neg).div_const _
  exact Real.contDiff_exp.comp hin

/-- **`iteratedDeriv` commutes with a finite sum.**  Mathlib has the multilinear version
`iteratedFDeriv_fun_sum_apply`; this is the scalar-variable counterpart it lacks. -/
theorem iteratedDeriv_fun_sum {ι : Type*} {u : Finset ι} {n : ℕ} {F : ι → ℝ → ℝ} {x : ℝ}
    (h : ∀ i ∈ u, ContDiffAt ℝ n (F i) x) :
    iteratedDeriv n (fun z => ∑ i ∈ u, F i z) x = ∑ i ∈ u, iteratedDeriv n (F i) x := by
  simp only [iteratedDeriv]
  rw [iteratedFDeriv_fun_sum_apply h]
  simp

/-- The order-`j` level moment `M_j(v) = ∑_{x : f x = v} π_x (-g x)^j`. -/
def levelMoment (pi f g : X → ℝ) (j : ℕ) (v : ℝ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x => f x = v), pi x * (-g x) ^ j

/-- **The assembly.**  The `j`-th derivative in `h` at `h = 0` of the whole mixture is the
order-`j` level sum.  Nothing is assumed about smoothness: `contDiff_component` supplies
it, and `iteratedDeriv_shift` supplies each component's value. -/
theorem iteratedDeriv_mixture (σ : ℝ) (hσ : σ ≠ 0) (pi f g : X → ℝ) (y : ℝ) (j : ℕ) :
    iteratedDeriv j (fun h : ℝ => ∑ x : X, pi x * gauss σ (y - f x - h * g x)) 0
      = levelSum σ j (Finset.image f Finset.univ) (levelMoment pi f g j) y := by
  classical
  have hsmooth : ∀ x ∈ (Finset.univ : Finset X),
      ContDiffAt ℝ j (fun h : ℝ => pi x * gauss σ (y - f x - h * g x)) 0 := fun x _ =>
    contDiffAt_const.mul (contDiff_component σ (f x) (g x) y j).contDiffAt
  rw [iteratedDeriv_fun_sum hsmooth]
  have hterm : ∀ x : X,
      iteratedDeriv j (fun h : ℝ => pi x * gauss σ (y - f x - h * g x)) 0
        = pi x * (-g x) ^ j * ((hpoly σ j).eval (y - f x) * gauss σ (y - f x)) := by
    intro x
    rw [iteratedDeriv_const_mul_field (pi x) (fun h : ℝ => gauss σ (y - f x - h * g x)),
        iteratedDeriv_shift σ hσ (g x) (f x) y j 0]
    simp [mul_assoc]
  simp only [hterm]
  rw [sum_by_level pi f (fun x => (-g x) ^ j)
        (fun v => (hpoly σ j).eval (y - v) * gauss σ (y - v))]
  rfl

/-- **The easy half on the mixture.**  Two worlds sharing a level set, whose order-`j`
level moments agree, have the same order-`j` coefficient. -/
theorem mixture_coeff_diff_eq_zero (σ : ℝ) (hσ : σ ≠ 0)
    (piA fA gA piB fB gB : X → ℝ) (j : ℕ) (y : ℝ)
    (hS : Finset.image fB Finset.univ = Finset.image fA Finset.univ)
    (hagree : ∀ v ∈ Finset.image fA Finset.univ,
        levelMoment piA fA gA j v = levelMoment piB fB gB j v) :
    iteratedDeriv j (fun h : ℝ => ∑ x : X, piA x * gauss σ (y - fA x - h * gA x)) 0
      - iteratedDeriv j (fun h : ℝ => ∑ x : X, piB x * gauss σ (y - fB x - h * gB x)) 0
        = 0 := by
  rw [iteratedDeriv_mixture σ hσ piA fA gA y j, iteratedDeriv_mixture σ hσ piB fB gB y j,
      hS]
  exact levelSum_eq_zero_of_levels_agree σ j _ _ _ hagree y

/-- **The hard half on the mixture.**  If the largest level carries a nonzero order-`r`
moment, the order-`r` coefficient of the mixture is somewhere nonzero: the shifted
Gaussian derivatives cannot conspire to cancel. -/
theorem mixture_coeff_ne_zero (σ : ℝ) (hσ : σ ≠ 0) (pi f g : X → ℝ) (r : ℕ)
    (vstar : ℝ) (hvs : vstar ∈ Finset.image f Finset.univ)
    (htop : ∀ v ∈ Finset.image f Finset.univ, v ≠ vstar → v < vstar)
    (hc : levelMoment pi f g r vstar ≠ 0) :
    ∃ y, iteratedDeriv r (fun h : ℝ => ∑ x : X, pi x * gauss σ (y - f x - h * g x)) 0
      ≠ 0 := by
  obtain ⟨y, hy⟩ := levelSum_ne_zero σ hσ r (Finset.image f Finset.univ)
    (levelMoment pi f g r) vstar hvs htop hc
  exact ⟨y, by rw [iteratedDeriv_mixture σ hσ pi f g y r]; exact hy⟩

#print axioms contDiff_component
#print axioms iteratedDeriv_fun_sum
#print axioms iteratedDeriv_mixture
#print axioms mixture_coeff_diff_eq_zero
#print axioms mixture_coeff_ne_zero

end

end CIGAMF.P13.QueryMixtureDerivative
