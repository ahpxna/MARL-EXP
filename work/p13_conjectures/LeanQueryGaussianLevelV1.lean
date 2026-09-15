import Mathlib

/-! # Query step 3a: Gaussian derivatives, level moments, and NON-VANISHING of the
order-`r` coefficient -- formalised directly, not assumed.

The observation density of world `W` is the finite Gaussian mixture
`p_{W,h}(y) = ∑_x π_x φ_σ(y - f_W(x) - h g(x))`.  Expanding in `h` produces

    Δ_j(y) = ((-1)^j/j!) ∑_v (M_{A,j}(v) - M_{B,j}(v)) φ_σ^{(j)}(y - v),
    M_{W,j}(v) = ∑_{x : f_W(x)=v} π_x g(x)^j.

Two things must be proved separately, and the second is the one that is usually
skipped: (i) the coefficients below order `r` cancel, and (ii) `Δ_r ≢ 0`.  "One
coefficient is nonzero" is NOT enough -- the shifted Gaussian derivatives could in
principle cancel each other.  This file proves both, with the Gaussian derivatives
built explicitly.

## THE GAUSSIAN DERIVATIVES

`hpoly σ n` is the Hermite-type sequence `H_0 = 1`, `H_{n+1} = H_n' - (y/σ²) H_n`, and
`iteratedDeriv_gauss` proves `dⁿ/dyⁿ e^{-y²/2σ²} = H_n(y) e^{-y²/2σ²}`.
`hpoly_coeff` computes `H_n`'s degree-`n` coefficient as `(-1/σ²)^n`, which is nonzero,
so `H_n ≠ 0` -- the fact the non-vanishing argument needs.

## THE NON-VANISHING ARGUMENT

Factor `φ_σ(y-v) = φ_σ(y) e^{vy/σ² - v²/2σ²}` (`gauss_shift`).  Dividing the whole sum
by the largest level's factor leaves

    T(y) = c_{v*} H_r(y - v*)  +  ∑_{v < v*} c_v H_r(y - v) e^{-(v*-v)y/σ² + const}.

Each term of the second sum is a polynomial against a DECAYING exponential, so it
tends to `0` (`poly_exp_decay`, via `Polynomial.tendsto_div_exp_atTop`).  If `T ≡ 0`
then the polynomial `c_{v*}·H_r(· - v*)` would tend to `0` at `+∞`; by
`Polynomial.tendsto_nhds_iff` its leading coefficient would be `0`, so it would be the
zero polynomial -- contradicting `c_{v*} ≠ 0` and `H_r ≠ 0`.  Hence `T ≢ 0`, hence
`Δ_r ≢ 0`.

## WHAT IS PROVED

* `hasDerivAt_gauss`, `hasDerivAt_hgauss`, `iteratedDeriv_gauss` — the Gaussian's
  iterated derivatives, in closed form.
* `hpoly_natDegree_le`, `hpoly_coeff`, `hpoly_ne_zero`.
* `iteratedDeriv_shift` — the `h`-expansion of one mixture component: the `j`-th
  derivative at `h = 0` is `(-g)^j` times the `j`-th Gaussian derivative.  This is
  exactly where `g(x)^j` -- and therefore the level moment -- comes from.
* `sum_by_level` — grouping the per-point sum into LEVEL moments.
* `levelSum_eq_zero_of_levels_agree` — order-`j` cancellation when all level moments
  agree: the easy half.
* `poly_exp_decay` — polynomial against decaying exponential.
* `levelSum_ne_zero` — **the hard half: the top level with a nonzero coefficient forces
  `Δ_r ≢ 0`.**

## WHAT THIS DOES NOT ESTABLISH

- The Taylor REMAINDER control (step 3c, the integrable Gaussian envelope) and the
  Hellinger integral itself are not here; this file is the coefficient analysis only.
- The normalising constant `1/(σ√(2π))` and the factor `1/j!` are positive constants
  and are dropped: they change no vanishing statement.
- Nothing here bounds `H²`; that assembly is `LeanQueryRateAssemblyV2`.
-/

namespace CIGAMF.P13.QueryGaussianLevel

open Polynomial Filter Finset
open scoped Topology

noncomputable section

/-- The unnormalised Gaussian. -/
def gauss (σ y : ℝ) : ℝ := Real.exp (-(y ^ 2) / (2 * σ ^ 2))

theorem gauss_pos (σ y : ℝ) : 0 < gauss σ y := Real.exp_pos _

theorem hasDerivAt_gauss (σ : ℝ) (hσ : σ ≠ 0) (y : ℝ) :
    HasDerivAt (gauss σ) (-(y / σ ^ 2) * gauss σ y) y := by
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2)) (-(2 * y ^ 1)) y := (hasDerivAt_pow 2 y).neg
  have h3 : HasDerivAt (fun x : ℝ => -(x ^ 2) / (2 * σ ^ 2)) (-(y / σ ^ 2)) y := by
    have h2 := h1.div_const (2 * σ ^ 2)
    have he : -(2 * y ^ 1) / (2 * σ ^ 2) = -(y / σ ^ 2) := by
      rw [pow_one]
      field_simp
    rwa [he] at h2
  have h4 : HasDerivAt (gauss σ) (Real.exp (-(y ^ 2) / (2 * σ ^ 2)) * -(y / σ ^ 2)) y := h3.exp
  convert h4 using 1
  unfold gauss
  ring

/-- The Hermite-type sequence of the Gaussian's derivatives. -/
def hpoly (σ : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => derivative (hpoly σ n) - C (1 / σ ^ 2) * X * hpoly σ n

theorem hasDerivAt_hgauss (σ : ℝ) (hσ : σ ≠ 0) (j : ℕ) (z : ℝ) :
    HasDerivAt (fun w => (hpoly σ j).eval w * gauss σ w)
      ((hpoly σ (j + 1)).eval z * gauss σ z) z := by
  have h := (Polynomial.hasDerivAt (hpoly σ j) z).mul (hasDerivAt_gauss σ hσ z)
  have hunfold : hpoly σ (j + 1)
      = derivative (hpoly σ j) - C (1 / σ ^ 2) * X * hpoly σ j := rfl
  have heq : (hpoly σ (j + 1)).eval z * gauss σ z
      = (derivative (hpoly σ j)).eval z * gauss σ z
        + (hpoly σ j).eval z * (-(z / σ ^ 2) * gauss σ z) := by
    rw [hunfold]
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    ring
  rw [heq]
  exact h

theorem iteratedDeriv_gauss (σ : ℝ) (hσ : σ ≠ 0) :
    ∀ (n : ℕ) (y : ℝ), iteratedDeriv n (gauss σ) y = (hpoly σ n).eval y * gauss σ y := by
  intro n
  induction n with
  | zero => intro y; simp [hpoly, iteratedDeriv_zero]
  | succ n ih =>
      intro y
      have hfun : iteratedDeriv n (gauss σ) = fun z => (hpoly σ n).eval z * gauss σ z :=
        funext ih
      rw [iteratedDeriv_succ, hfun, (hasDerivAt_hgauss σ hσ n y).deriv]

theorem hpoly_natDegree_le (σ : ℝ) : ∀ n : ℕ, (hpoly σ n).natDegree ≤ n := by
  intro n
  induction n with
  | zero => simp [hpoly]
  | succ n ih =>
      have h1 : (derivative (hpoly σ n)).natDegree ≤ n + 1 :=
        le_trans (Polynomial.natDegree_derivative_le _) (by omega)
      have h2 : (C (1 / σ ^ 2) * X * hpoly σ n).natDegree ≤ n + 1 := by
        refine le_trans (Polynomial.natDegree_mul_le) ?_
        have hcx : (C (1 / σ ^ 2) * X).natDegree ≤ 1 :=
          le_trans Polynomial.natDegree_mul_le (by simp)
        omega
      exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le h1 h2)

theorem hpoly_coeff (σ : ℝ) : ∀ n : ℕ, (hpoly σ n).coeff n = (-(1 / σ ^ 2)) ^ n := by
  intro n
  induction n with
  | zero => simp [hpoly]
  | succ n ih =>
      have hd : (derivative (hpoly σ n)).coeff (n + 1) = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        have := Polynomial.natDegree_derivative_le (hpoly σ n)
        have := hpoly_natDegree_le σ n
        omega
      have hx : (C (1 / σ ^ 2) * X * hpoly σ n).coeff (n + 1)
          = (1 / σ ^ 2) * (hpoly σ n).coeff n := by
        have hassoc : C (1 / σ ^ 2) * X * hpoly σ n
            = C (1 / σ ^ 2) * (X * hpoly σ n) := by ring
        rw [hassoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
      simp only [hpoly, Polynomial.coeff_sub, hd, hx, ih]
      ring

theorem hpoly_ne_zero (σ : ℝ) (hσ : σ ≠ 0) (n : ℕ) : hpoly σ n ≠ 0 := by
  intro h
  have := hpoly_coeff σ n
  rw [h] at this
  simp only [Polynomial.coeff_zero] at this
  have hσ2 : (0:ℝ) < σ ^ 2 := lt_of_le_of_ne (sq_nonneg σ) (Ne.symm (pow_ne_zero 2 hσ))
  have hne : (-(1 / σ ^ 2) : ℝ) ≠ 0 := by
    have h1 : (0:ℝ) < 1 / σ ^ 2 := by positivity
    intro hEq
    linarith
  exact (pow_ne_zero n hne) this.symm

/-- The `h`-expansion of one mixture component.  The factor `(-g)^j` is exactly what
turns the sum over points into the level moment `∑ π_x g(x)^j`. -/
theorem iteratedDeriv_shift (σ : ℝ) (hσ : σ ≠ 0) (g v y : ℝ) :
    ∀ (j : ℕ) (h₀ : ℝ), iteratedDeriv j (fun h : ℝ => gauss σ (y - v - h * g)) h₀
      = (-g) ^ j * ((hpoly σ j).eval (y - v - h₀ * g) * gauss σ (y - v - h₀ * g)) := by
  intro j
  induction j with
  | zero => intro h₀; simp [hpoly, iteratedDeriv_zero]
  | succ j ih =>
      intro h₀
      have hfun : iteratedDeriv j (fun h : ℝ => gauss σ (y - v - h * g))
          = fun h => (-g) ^ j * ((hpoly σ j).eval (y - v - h * g) * gauss σ (y - v - h * g)) :=
        funext ih
      rw [iteratedDeriv_succ, hfun]
      have hu : HasDerivAt (fun h : ℝ => y - v - h * g) (-g) h₀ := by
        simpa using ((hasDerivAt_id h₀).mul_const g).const_sub (y - v)
      have hF0 := HasDerivAt.comp h₀ (hasDerivAt_hgauss σ hσ j (y - v - h₀ * g)) hu
      have hF : HasDerivAt
          (fun h : ℝ => (hpoly σ j).eval (y - v - h * g) * gauss σ (y - v - h * g))
          (((hpoly σ (j + 1)).eval (y - v - h₀ * g) * gauss σ (y - v - h₀ * g)) * (-g)) h₀ :=
        hF0
      have hG := hF.const_mul ((-g) ^ j)
      rw [hG.deriv]
      ring

/-- Grouping the per-point sum into LEVEL moments. -/
theorem sum_by_level {X : Type*} [Fintype X] [DecidableEq X]
    (pi f w : X → ℝ) (Q : ℝ → ℝ) :
    ∑ x : X, pi x * w x * Q (f x)
      = ∑ v ∈ Finset.image f Finset.univ,
          (∑ x ∈ Finset.univ.filter (fun x => f x = v), pi x * w x) * Q v := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
        (fun x (_ : x ∈ (Finset.univ : Finset X)) =>
          Finset.mem_image_of_mem f (Finset.mem_univ x))
        (fun x => pi x * w x * Q (f x))]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.1 hx).2]

/-- The order-`r` coefficient function `Δ_r`, up to positive constants. -/
def levelSum (σ : ℝ) (r : ℕ) (S : Finset ℝ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∑ v ∈ S, c v * ((hpoly σ r).eval (y - v) * gauss σ (y - v))

/-- The easy half: if the two worlds' level moments agree at order `j`, the order-`j`
coefficient vanishes identically. -/
theorem levelSum_eq_zero_of_levels_agree (σ : ℝ) (r : ℕ) (S : Finset ℝ) (cA cB : ℝ → ℝ)
    (hagree : ∀ v ∈ S, cA v = cB v) (y : ℝ) :
    levelSum σ r S cA y - levelSum σ r S cB y = 0 := by
  unfold levelSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun v hv => ?_
  rw [hagree v hv]
  ring

/-- A shifted Gaussian is the Gaussian times an exponential in `y`: this identity is
what makes the LARGEST level dominate. -/
theorem gauss_shift (σ : ℝ) (hσ : σ ≠ 0) (v y : ℝ) :
    gauss σ (y - v) = gauss σ y * Real.exp (v * y / σ ^ 2 - v ^ 2 / (2 * σ ^ 2)) := by
  unfold gauss
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

/-- A polynomial against a decaying exponential tends to `0`. -/
theorem poly_exp_decay (p : ℝ[X]) (v δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun y : ℝ => p.eval (y - v) * Real.exp (-(δ * y))) atTop (𝓝 0) := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hq := Polynomial.tendsto_div_exp_atTop (p.comp (C δ⁻¹ * X - C v))
  have hmul : Tendsto (fun y : ℝ => δ * y) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hδ tendsto_id
  have hcomp := hq.comp hmul
  have hfun : (fun x : ℝ => (p.comp (C δ⁻¹ * X - C v)).eval x / Real.exp x) ∘ (fun y : ℝ => δ * y)
      = fun y : ℝ => p.eval (y - v) * Real.exp (-(δ * y)) := by
    funext y
    simp only [Function.comp_apply, Polynomial.eval_comp, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Real.exp_neg,
      div_eq_mul_inv]
    congr 2
    field_simp
  rwa [hfun] at hcomp

/-- **The hard half.**  If the largest level carries a nonzero coefficient, the
order-`r` coefficient function is not identically zero: the shifted Gaussian
derivatives cannot cancel. -/
theorem levelSum_ne_zero (σ : ℝ) (hσ : σ ≠ 0) (r : ℕ) (S : Finset ℝ) (c : ℝ → ℝ)
    (vstar : ℝ) (hvs : vstar ∈ S) (htop : ∀ v ∈ S, v ≠ vstar → v < vstar)
    (hc : c vstar ≠ 0) : ∃ y, levelSum σ r S c y ≠ 0 := by
  classical
  set P := hpoly σ r with hP
  have hPne : P ≠ 0 := hpoly_ne_zero σ hσ r
  -- the polynomial carried by the top level
  set A : ℝ[X] := C (c vstar) * P.comp (X - C vstar) with hA
  have hAeval : ∀ y : ℝ, A.eval y = c vstar * P.eval (y - vstar) := by
    intro y
    simp [hA, Polynomial.eval_comp]
  have hAne : A ≠ 0 := by
    intro hzero
    have hall : ∀ z : ℝ, P.eval z = 0 := by
      intro z
      have := hAeval (z + vstar)
      rw [hzero] at this
      simp only [Polynomial.eval_zero] at this
      have hz : z + vstar - vstar = z := by ring
      rw [hz] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hc
    exact hPne (Polynomial.funext (fun z => by simpa using hall z))
  -- the remainder, one term per strictly smaller level
  set B : ℝ → ℝ := fun y => ∑ v ∈ S.erase vstar,
      c v * P.eval (y - v) * Real.exp ((v - vstar) * y / σ ^ 2
        - (v ^ 2 - vstar ^ 2) / (2 * σ ^ 2)) with hB
  have hBzero : Tendsto B atTop (𝓝 0) := by
    rw [hB]
    have : Tendsto (fun y : ℝ => ∑ v ∈ S.erase vstar,
        c v * P.eval (y - v) * Real.exp ((v - vstar) * y / σ ^ 2
          - (v ^ 2 - vstar ^ 2) / (2 * σ ^ 2))) atTop (𝓝 (∑ _v ∈ S.erase vstar, (0:ℝ))) := by
      refine tendsto_finset_sum _ fun v hv => ?_
      have hvlt : v < vstar := htop v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv)
      set δ : ℝ := (vstar - v) / σ ^ 2 with hδdef
      have hσ2 : (0:ℝ) < σ ^ 2 := by positivity
      have hδ : 0 < δ := by rw [hδdef]; exact div_pos (by linarith) hσ2
      have hdecay := poly_exp_decay P v δ hδ
      have hconst := hdecay.const_mul
        (c v * Real.exp (-((v ^ 2 - vstar ^ 2) / (2 * σ ^ 2))))
      have hfun : (fun y : ℝ => (c v * Real.exp (-((v ^ 2 - vstar ^ 2) / (2 * σ ^ 2))))
            * (P.eval (y - v) * Real.exp (-(δ * y))))
          = fun y : ℝ => c v * P.eval (y - v) * Real.exp ((v - vstar) * y / σ ^ 2
              - (v ^ 2 - vstar ^ 2) / (2 * σ ^ 2)) := by
        funext y
        have hexp : Real.exp (-(δ * y)) * Real.exp (-((v ^ 2 - vstar ^ 2) / (2 * σ ^ 2)))
            = Real.exp ((v - vstar) * y / σ ^ 2 - (v ^ 2 - vstar ^ 2) / (2 * σ ^ 2)) := by
          rw [← Real.exp_add]
          congr 1
          rw [hδdef]
          field_simp
          ring
        calc (c v * Real.exp (-((v ^ 2 - vstar ^ 2) / (2 * σ ^ 2))))
              * (P.eval (y - v) * Real.exp (-(δ * y)))
            = c v * P.eval (y - v)
              * (Real.exp (-(δ * y)) * Real.exp (-((v ^ 2 - vstar ^ 2) / (2 * σ ^ 2)))) := by
              ring
          _ = c v * P.eval (y - v) * Real.exp ((v - vstar) * y / σ ^ 2
              - (v ^ 2 - vstar ^ 2) / (2 * σ ^ 2)) := by rw [hexp]
      rw [hfun] at hconst
      simpa using hconst
    simpa using this
  -- the factorisation
  have hBy : ∀ y : ℝ, B y = ∑ v ∈ S.erase vstar,
      c v * P.eval (y - v) * Real.exp ((v - vstar) * y / σ ^ 2
        - (v ^ 2 - vstar ^ 2) / (2 * σ ^ 2)) := fun _ => rfl
  have hfact : ∀ y : ℝ, levelSum σ r S c y
      = gauss σ y * Real.exp (vstar * y / σ ^ 2 - vstar ^ 2 / (2 * σ ^ 2))
        * (A.eval y + B y) := by
    intro y
    have hsplit : ∀ v : ℝ, c v * ((hpoly σ r).eval (y - v) * gauss σ (y - v))
        = gauss σ y * Real.exp (vstar * y / σ ^ 2 - vstar ^ 2 / (2 * σ ^ 2))
          * (c v * P.eval (y - v) * Real.exp ((v - vstar) * y / σ ^ 2
              - (v ^ 2 - vstar ^ 2) / (2 * σ ^ 2))) := by
      intro v
      rw [gauss_shift σ hσ v y, ← hP]
      have hexp : Real.exp (v * y / σ ^ 2 - v ^ 2 / (2 * σ ^ 2))
          = Real.exp (vstar * y / σ ^ 2 - vstar ^ 2 / (2 * σ ^ 2))
            * Real.exp ((v - vstar) * y / σ ^ 2 - (v ^ 2 - vstar ^ 2) / (2 * σ ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    have htop0 : c vstar * ((hpoly σ r).eval (y - vstar) * gauss σ (y - vstar))
        = gauss σ y * Real.exp (vstar * y / σ ^ 2 - vstar ^ 2 / (2 * σ ^ 2)) * A.eval y := by
      rw [hsplit vstar, hAeval y]
      have hz : (vstar - vstar) * y / σ ^ 2 - (vstar ^ 2 - vstar ^ 2) / (2 * σ ^ 2) = 0 := by
        ring
      rw [hz, Real.exp_zero]
      ring
    have hrest : (∑ v ∈ S.erase vstar, c v * ((hpoly σ r).eval (y - v) * gauss σ (y - v)))
        = gauss σ y * Real.exp (vstar * y / σ ^ 2 - vstar ^ 2 / (2 * σ ^ 2)) * B y := by
      rw [hBy y, Finset.mul_sum]
      exact Finset.sum_congr rfl fun v _ => hsplit v
    unfold levelSum
    rw [← Finset.add_sum_erase _ _ hvs, htop0, hrest, mul_add]
  -- conclude
  by_contra hnone
  push_neg at hnone
  have hTzero : ∀ y : ℝ, A.eval y + B y = 0 := by
    intro y
    have h1 := hfact y
    rw [hnone y] at h1
    have hpos : (0:ℝ) < gauss σ y * Real.exp (vstar * y / σ ^ 2 - vstar ^ 2 / (2 * σ ^ 2)) :=
      mul_pos (gauss_pos σ y) (Real.exp_pos _)
    rcases mul_eq_zero.1 h1.symm with h | h
    · exact absurd h (ne_of_gt hpos)
    · exact h
  have hAtend : Tendsto (fun y => A.eval y) atTop (𝓝 0) := by
    have heq : (fun y : ℝ => A.eval y) = fun y : ℝ => -(B y) := by
      funext y; linarith [hTzero y]
    rw [heq]
    simpa using hBzero.neg
  have := (Polynomial.tendsto_nhds_iff (P := A)).1 hAtend
  exact hAne (Polynomial.leadingCoeff_eq_zero.1 this.1)

#print axioms gauss_pos
#print axioms hasDerivAt_gauss
#print axioms hasDerivAt_hgauss
#print axioms iteratedDeriv_gauss
#print axioms hpoly_natDegree_le
#print axioms hpoly_coeff
#print axioms hpoly_ne_zero
#print axioms iteratedDeriv_shift
#print axioms sum_by_level
#print axioms levelSum_eq_zero_of_levels_agree
#print axioms gauss_shift
#print axioms poly_exp_decay
#print axioms levelSum_ne_zero

end
end CIGAMF.P13.QueryGaussianLevel
