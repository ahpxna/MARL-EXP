import «LeanPaperA7OracleSelectV1»

/-!
# Paper A7: stability of the information game with UNBOUNDED alternatives

`LeanPaperA7OracleSelectV1.J_lipschitz_in_world` needs every alternative in a box
(`hbox : ∀ nu ∈ Alt, InBox B nu`).  The alternative set of the paper's family
(`TrueAltStrict r`, over which `actualKLGame` is defined) is not bounded, and the learner's
code boxes it only as an implementation choice.  This module removes the box.

The observation: `sqrt(2 pen(w, mu, lambda))` is a weighted Euclidean distance between `mu` and
`lambda`, so by Minkowski's inequality (`sqrt_wsum_add_le`) it moves by at most the weighted
distance between two worlds, whatever `lambda` is (`sqrt_pen_le`).  Taking the infimum:

* `Jval_ge_of_close` -- `J(w, mu') >= J(w, mu) - rho sqrt(2U)` for every upper bound
  `U >= J(w, mu)`, where `rho^2 >= sum_e w_e (mu'_e - mu_e)^2`;
* for an allocation and `|mu' - mu| <= r` coordinatewise, `rho = r` (`rho_le_of_alloc`);
* `Gamma_ge_of_close` -- the same for the game value;
* `oracle_perturbation_free` -- the design the oracle returns at the estimate has TRUE
  information at least `Gamma(theta) - eps - 2 r sqrt(2U)`.

No box, no bound on the alternatives, and the constants involve only an upper bound `U` on the
game values -- which is finite for estimates in a bounded region.
-/

namespace CIGAMF.P13.PaperA7SqrtLip

open Finset
open CIGAMF.P13.PaperA7OracleSelect

variable {E : Type*} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
/-- **Weighted Minkowski.** -/
theorem sqrt_wsum_add_le (w a b : E → ℝ) (hw : ∀ e, 0 ≤ w e) :
    Real.sqrt (∑ e, w e * (a e + b e) ^ 2)
      ≤ Real.sqrt (∑ e, w e * a e ^ 2) + Real.sqrt (∑ e, w e * b e ^ 2) := by
  set A := ∑ e, w e * a e ^ 2 with hA
  set Bs := ∑ e, w e * b e ^ 2 with hB
  have hA0 : 0 ≤ A := sum_nonneg fun e _ => mul_nonneg (hw e) (sq_nonneg _)
  have hB0 : 0 ≤ Bs := sum_nonneg fun e _ => mul_nonneg (hw e) (sq_nonneg _)
  -- Cauchy-Schwarz for the cross term
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun e => Real.sqrt (w e) * a e)
    (fun e => Real.sqrt (w e) * b e)
  have hsq : ∀ e, (Real.sqrt (w e) * a e) ^ 2 = w e * a e ^ 2 := by
    intro e; rw [mul_pow, Real.sq_sqrt (hw e)]
  have hsq' : ∀ e, (Real.sqrt (w e) * b e) ^ 2 = w e * b e ^ 2 := by
    intro e; rw [mul_pow, Real.sq_sqrt (hw e)]
  have hprod : ∀ e, Real.sqrt (w e) * a e * (Real.sqrt (w e) * b e) = w e * a e * b e := by
    intro e
    have := Real.mul_self_sqrt (hw e)
    calc Real.sqrt (w e) * a e * (Real.sqrt (w e) * b e)
        = (Real.sqrt (w e) * Real.sqrt (w e)) * a e * b e := by ring
      _ = w e * a e * b e := by rw [this]
  simp only [hsq, hsq', hprod] at hcs
  set X := ∑ e, w e * a e * b e with hX
  have hXle : X ≤ Real.sqrt A * Real.sqrt Bs := by
    have h1 : X ^ 2 ≤ (Real.sqrt A * Real.sqrt Bs) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0]; exact hcs
    have h2 : 0 ≤ Real.sqrt A * Real.sqrt Bs := by positivity
    nlinarith [abs_le_of_sq_le_sq' h1 h2]
  have hexp : ∑ e, w e * (a e + b e) ^ 2 = A + 2 * X + Bs := by
    rw [hA, hB, hX, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun e _ => ?_
    ring
  rw [hexp]
  have hrhs : A + 2 * X + Bs ≤ (Real.sqrt A + Real.sqrt Bs) ^ 2 := by
    have := Real.sq_sqrt hA0
    have := Real.sq_sqrt hB0
    nlinarith
  calc Real.sqrt (A + 2 * X + Bs) ≤ Real.sqrt ((Real.sqrt A + Real.sqrt Bs) ^ 2) :=
        Real.sqrt_le_sqrt hrhs
    _ = Real.sqrt A + Real.sqrt Bs := Real.sqrt_sq (by positivity)

omit [DecidableEq E] in
/-- **The weighted distance to an alternative moves by at most the distance between the
worlds.** -/
theorem sqrt_pen_le (w mu mu' nu : E → ℝ) (hw : ∀ e, 0 ≤ w e) :
    Real.sqrt (2 * pen w mu' nu)
      ≤ Real.sqrt (2 * pen w mu nu) + Real.sqrt (∑ e, w e * (mu' e - mu e) ^ 2) := by
  have h2 : ∀ x y z : E → ℝ, 2 * pen w x z = ∑ e, w e * (x e - z e) ^ 2 := by
    intro x y z; unfold pen; ring
  rw [h2 mu' mu nu, h2 mu mu' nu]
  have := sqrt_wsum_add_le w (fun e => mu e - nu e) (fun e => mu' e - mu e) hw
  have heq : ∀ e, (mu e - nu e) + (mu' e - mu e) = mu' e - nu e := fun e => by ring
  simp only [heq] at this
  exact this

omit [DecidableEq E] in
/-- For an allocation, a coordinatewise radius `r` is a weighted radius `r`. -/
theorem rho_le_of_alloc (w mu mu' : E → ℝ) (hw : IsAlloc w) (r : ℝ) (hr : 0 ≤ r)
    (hclose : ∀ e, |mu' e - mu e| ≤ r) :
    Real.sqrt (∑ e, w e * (mu' e - mu e) ^ 2) ≤ r := by
  have h : ∑ e, w e * (mu' e - mu e) ^ 2 ≤ r ^ 2 := by
    calc ∑ e, w e * (mu' e - mu e) ^ 2 ≤ ∑ e, w e * r ^ 2 := by
          refine sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ?_ (hw.1 e)
          have := hclose e
          nlinarith [abs_nonneg (mu' e - mu e), sq_abs (mu' e - mu e)]
      _ = r ^ 2 := by rw [← sum_mul, hw.2, one_mul]
  calc Real.sqrt (∑ e, w e * (mu' e - mu e) ^ 2) ≤ Real.sqrt (r ^ 2) := Real.sqrt_le_sqrt h
    _ = r := Real.sqrt_sq hr

/-- **The information of a design at a nearby world, without a box on the alternatives.** -/
theorem Jval_ge_of_close (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (w mu mu' : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : Real.sqrt (∑ e, w e * (mu' e - mu e) ^ 2) ≤ ρ)
    (U : ℝ) (hU : Jval Alt w mu ≤ U) :
    Jval Alt w mu - ρ * Real.sqrt (2 * U) ≤ Jval Alt w mu' := by
  set j := Jval Alt w mu with hj
  have hj0 : 0 ≤ j := by
    refine le_csInf (hne.image _) ?_
    rintro _ ⟨nu, -, rfl⟩
    exact pen_nonneg w mu nu hw
  have hsU : Real.sqrt (2 * j) ≤ Real.sqrt (2 * U) := Real.sqrt_le_sqrt (by linarith)
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨nu, hnu, rfl⟩
  have hjle : j ≤ pen w mu nu := csInf_le (Jval_bddBelow Alt w mu hw) ⟨nu, hnu, rfl⟩
  have hpen0 : 0 ≤ pen w mu' nu := pen_nonneg w mu' nu hw
  -- the distance from mu to nu is at most the distance from mu' plus rho
  have hsym : Real.sqrt (∑ e, w e * (mu e - mu' e) ^ 2) ≤ ρ := by
    have : ∀ e, (mu e - mu' e) ^ 2 = (mu' e - mu e) ^ 2 := fun e => by ring
    simp only [this]; exact hρ
  have htri := sqrt_pen_le w mu' mu nu hw
  have hdist : Real.sqrt (2 * j) ≤ Real.sqrt (2 * pen w mu' nu) + ρ := by
    have : Real.sqrt (2 * j) ≤ Real.sqrt (2 * pen w mu nu) := Real.sqrt_le_sqrt (by linarith)
    linarith
  -- square it
  set s := Real.sqrt (2 * j) with hs
  set p := Real.sqrt (2 * pen w mu' nu) with hp
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hp0 : 0 ≤ p := Real.sqrt_nonneg _
  have hss : s ^ 2 = 2 * j := Real.sq_sqrt (by linarith)
  have hpp : p ^ 2 = 2 * pen w mu' nu := Real.sq_sqrt (by linarith)
  have hmain : j - ρ * s ≤ pen w mu' nu := by
    rcases le_or_gt ρ s with hρs | hρs
    · have h1 : s - ρ ≤ p := by linarith
      have h2 : (s - ρ) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      nlinarith
    · have : j - ρ * s ≤ 0 := by nlinarith
      linarith
  have : ρ * s ≤ ρ * Real.sqrt (2 * U) := mul_le_mul_of_nonneg_left hsU hρ0
  linarith

/-- **The game value at a nearby world.** -/
theorem Gamma_ge_of_close (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (mu mu' : E → ℝ)
    (r : ℝ) (hr : 0 ≤ r) (hclose : ∀ e, |mu' e - mu e| ≤ r) (Γ Γ' : ℝ)
    (hΓ : IsLUB {v : ℝ | ∃ w : E → ℝ, IsAlloc w ∧ v = Jval Alt w mu} Γ)
    (hΓ' : IsLUB {v : ℝ | ∃ w : E → ℝ, IsAlloc w ∧ v = Jval Alt w mu'} Γ')
    (hex : ∃ w : E → ℝ, IsAlloc w) :
    Γ - r * Real.sqrt (2 * Γ) ≤ Γ' := by
  have hpt : ∀ w, IsAlloc w → Jval Alt w mu - r * Real.sqrt (2 * Γ) ≤ Γ' := by
    intro w hw
    have hJ : Jval Alt w mu ≤ Γ := hΓ.1 ⟨w, hw, rfl⟩
    have := Jval_ge_of_close Alt hne w mu mu' hw.1 r hr (rho_le_of_alloc w mu mu' hw r hr hclose)
      Γ hJ
    exact le_trans this (hΓ'.1 ⟨w, hw, rfl⟩)
  -- Γ is the least upper bound of the J values at mu
  have hub : ∀ v ∈ {v : ℝ | ∃ w : E → ℝ, IsAlloc w ∧ v = Jval Alt w mu},
      v ≤ Γ' + r * Real.sqrt (2 * Γ) := by
    rintro _ ⟨w, hw, rfl⟩
    have := hpt w hw
    linarith
  have := hΓ.2 hub
  linarith

/-- **Oracle perturbation without a box.**  `lo` is a certified lower value of the returned
design at the estimate `theta_hat`, within `eps` of the estimated game value; `U` bounds both
game values.  Then the design's TRUE information is at least `Gamma(theta) - eps -
2 r sqrt(2U)`. -/
theorem oracle_perturbation_free (Alt : Set (E → ℝ)) (hne : Alt.Nonempty) (w θ θh : E → ℝ)
    (hw : IsAlloc w) (r : ℝ) (hr : 0 ≤ r) (hclose : ∀ e, |θh e - θ e| ≤ r) (Gt Gh : ℝ)
    (hGt : IsLUB {v : ℝ | ∃ w' : E → ℝ, IsAlloc w' ∧ v = Jval Alt w' θ} Gt)
    (hGh : IsLUB {v : ℝ | ∃ w' : E → ℝ, IsAlloc w' ∧ v = Jval Alt w' θh} Gh)
    (U : ℝ) (hUt : Gt ≤ U) (hUh : Gh ≤ U)
    (lo ε : ℝ) (hlo : lo ≤ Jval Alt w θh) (hbr : Gh - ε ≤ lo) :
    Gt - ε - 2 * r * Real.sqrt (2 * U) ≤ Jval Alt w θ := by
  have hclose' : ∀ e, |θ e - θh e| ≤ r := fun e => by rw [abs_sub_comm]; exact hclose e
  -- the estimated game is at least the true one, less the perturbation
  have hG := Gamma_ge_of_close Alt hne θ θh r hr hclose Gt Gh hGt hGh ⟨w, hw⟩
  have hsqGt : Real.sqrt (2 * Gt) ≤ Real.sqrt (2 * U) := Real.sqrt_le_sqrt (by linarith)
  -- the design's information moves back to the true world
  have hJh : Jval Alt w θh ≤ U := le_trans (hGh.1 ⟨w, hw, rfl⟩) hUh
  have hJ := Jval_ge_of_close Alt hne w θh θ hw.1 r hr
    (rho_le_of_alloc w θh θ hw r hr hclose') U hJh
  have h1 : r * Real.sqrt (2 * Gt) ≤ r * Real.sqrt (2 * U) := mul_le_mul_of_nonneg_left hsqGt hr
  linarith

#print axioms sqrt_wsum_add_le
#print axioms sqrt_pen_le
#print axioms rho_le_of_alloc
#print axioms Jval_ge_of_close
#print axioms Gamma_ge_of_close
#print axioms oracle_perturbation_free

end CIGAMF.P13.PaperA7SqrtLip
