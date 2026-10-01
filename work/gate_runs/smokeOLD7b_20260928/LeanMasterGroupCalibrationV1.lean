import Mathlib

/-! # MASTER: a group of calibration queries can beat every single one -- but only
if the nuisance has rank at least two.

`scripts/P6_master_group_calibration.py` extends the MASTER observation law to a
VECTOR nuisance, `Y e = m_theta e + v_e ⬝ b + Z e` with `b ∈ ℝ^p`, and shows that
moving a fraction `t` of the budget from ordinary queries to a mixture `rho` of
calibration controls changes the profiled information of alternative `u` at rate

  `dI_u/dt|_0 = ∑_l rho l * G u l - I_u`,   `G u l = (c_l ⬝ K⁻¹ M_u)^2 / (2 nu_l kappa_l)`,

so on the active set the value moves at rate `Lambda - V_0` with
`Lambda = max_rho min_u ∑_l rho l * G u l`.  The `- V_0` is the budget taken away
from the ordinary queries and must not be dropped.

THIS FILE PROVES THE STRUCTURAL DICHOTOMY THAT DECIDES WHEN THAT CAN BE POSITIVE
FOR A MIXTURE BUT NOT FOR ANY SINGLE CONTROL.

* `mixVal_pure` — a single control is the mixture concentrated on it, so the best
  single control is always available to the mixer.
* `rank_one_no_complementarity` — if `G u l = alpha u * beta l` (which is exactly
  what a SCALAR nuisance `p = 1` forces, since then `K`, `M_u` and `c_l` are
  scalars and `G u l = (M_u/K)^2 * c_l^2/(2 nu_l kappa_l)`), then NO mixture beats
  the best single control.  Buying a bundle can never be strictly better than
  buying the best single item, so the common-offset model cannot exhibit the
  effect at all.
* `rank_one_value` — combining the two: for a rank-one `G`, `Lambda` equals the
  best single control exactly.
* `rank_two_complementarity` — and a witness that rank two is enough: with
  `G = 3 • I₂` every single control leaves an alternative at gain `0`, while the
  even mixture gives `3/2` against every alternative.  So the dichotomy is sharp.

## WHAT THIS DOES NOT ESTABLISH

- The derivative formula itself is not formalised; it is derived and checked
  against finite differences in the script.  This file is about the object
  `max_rho min_u ⟨rho, G u ⬝⟩` once `G` is given.
- `rank_two_complementarity` is a statement about the matrix `3 • I₂`.  That this
  matrix ARISES from a real four-item / two-instrument query family with
  `G = 3 V_0 • I₂` is computed in the script from the query means and variances,
  and is not formalised here.
- Nothing here says the vector-nuisance model is the right model for MASTER.
-/

namespace CIGAMF.P13.MasterGroupCalibration

open Finset

noncomputable section

variable {U L : Type*} [Fintype U] [Fintype L] [Nonempty U] [Nonempty L]

/-- The gain a control mixture `rho` delivers against the WORST active alternative. -/
def mixVal (G : U → L → ℝ) (rho : L → ℝ) : ℝ :=
  (univ : Finset U).inf' univ_nonempty (fun u => ∑ l, rho l * G u l)

/-- The gain of the best SINGLE control, each judged against its own worst
alternative. -/
def bestSingle (G : U → L → ℝ) : ℝ :=
  (univ : Finset L).sup' univ_nonempty
    (fun l => (univ : Finset U).inf' univ_nonempty (fun u => G u l))

/-- A single control is the mixture concentrated on it. -/
theorem mixVal_pure (G : U → L → ℝ) [DecidableEq L] (l₀ : L) :
    mixVal G (fun l => if l = l₀ then 1 else 0)
      = (univ : Finset U).inf' univ_nonempty (fun u => G u l₀) := by
  unfold mixVal
  refine congrArg _ ?_
  funext u
  simp

/-- Hence the best single control is never better than the best mixture. -/
theorem bestSingle_le_mixVal_pure (G : U → L → ℝ) [DecidableEq L] :
    ∃ l₀ : L, bestSingle G = mixVal G (fun l => if l = l₀ then 1 else 0) := by
  obtain ⟨l₀, -, hl₀⟩ :=
    (univ : Finset L).exists_max_image
      (fun l => (univ : Finset U).inf' univ_nonempty (fun u => G u l)) univ_nonempty
  refine ⟨l₀, ?_⟩
  rw [mixVal_pure]
  unfold bestSingle
  exact le_antisymm (Finset.sup'_le _ _ (fun l _ => hl₀ l (mem_univ l)))
    (Finset.le_sup'
      (fun l => (univ : Finset U).inf' univ_nonempty (fun u => G u l)) (mem_univ l₀))

/-- THE NEGATIVE CONTROL.  A rank-one gain matrix -- which is what a scalar nuisance
forces -- admits no complementarity: every mixture is dominated by a single control. -/
theorem rank_one_no_complementarity
    (alpha : U → ℝ) (beta : L → ℝ) (rho : L → ℝ)
    (ha : ∀ u, 0 ≤ alpha u) (hb : ∀ l, 0 ≤ beta l)
    (hr0 : ∀ l, 0 ≤ rho l) (hr1 : ∑ l, rho l = 1) :
    mixVal (fun u l => alpha u * beta l) rho
      ≤ bestSingle (fun u l => alpha u * beta l) := by
  obtain ⟨u₀, -, hu₀⟩ := (univ : Finset U).exists_min_image alpha univ_nonempty
  obtain ⟨l₀, -, hl₀⟩ := (univ : Finset L).exists_max_image beta univ_nonempty
  have hc : ∑ l, rho l * beta l ≤ beta l₀ := by
    calc ∑ l, rho l * beta l
        ≤ ∑ l, rho l * beta l₀ :=
          Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left (hl₀ l (mem_univ l)) (hr0 l)
      _ = (∑ l, rho l) * beta l₀ := by rw [← Finset.sum_mul]
      _ = beta l₀ := by rw [hr1, one_mul]
  have h1 : mixVal (fun u l => alpha u * beta l) rho
      ≤ ∑ l, rho l * (alpha u₀ * beta l) :=
    Finset.inf'_le _ (mem_univ u₀)
  have h2 : ∑ l, rho l * (alpha u₀ * beta l) = alpha u₀ * ∑ l, rho l * beta l := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h3 : alpha u₀ * (∑ l, rho l * beta l) ≤ alpha u₀ * beta l₀ :=
    mul_le_mul_of_nonneg_left hc (ha u₀)
  have h4 : alpha u₀ * beta l₀
      ≤ (univ : Finset U).inf' univ_nonempty (fun u => alpha u * beta l₀) :=
    Finset.le_inf' _ _ fun u _ =>
      mul_le_mul_of_nonneg_right (hu₀ u (mem_univ u)) (hb l₀)
  have h5 : (univ : Finset U).inf' univ_nonempty (fun u => alpha u * beta l₀)
      ≤ bestSingle (fun u l => alpha u * beta l) := by
    unfold bestSingle
    exact Finset.le_sup'
      (fun l => (univ : Finset U).inf' univ_nonempty (fun u => alpha u * beta l))
      (mem_univ l₀)
  linarith [h1, h2 ▸ h1, h3, h4, h5]

/-- For a rank-one gain matrix the optimal mixture value IS the best single control:
`bestSingle` is an upper bound for every mixture and is itself attained by a pure
mixture. -/
theorem rank_one_value [DecidableEq L]
    (alpha : U → ℝ) (beta : L → ℝ)
    (ha : ∀ u, 0 ≤ alpha u) (hb : ∀ l, 0 ≤ beta l) :
    (∀ rho : L → ℝ, (∀ l, 0 ≤ rho l) → ∑ l, rho l = 1 →
        mixVal (fun u l => alpha u * beta l) rho
          ≤ bestSingle (fun u l => alpha u * beta l))
    ∧ ∃ l₀ : L, bestSingle (fun u l => alpha u * beta l)
        = mixVal (fun u l => alpha u * beta l) (fun l => if l = l₀ then 1 else 0) :=
  ⟨fun rho h0 h1 => rank_one_no_complementarity alpha beta rho ha hb h0 h1,
   bestSingle_le_mixVal_pure _⟩

/-- The rank-two witness: `G = 3 • I₂`. -/
def Gex : Fin 2 → Fin 2 → ℝ := fun u l => if u = l then 3 else 0

/-- Rank two is enough.  Every single control leaves an alternative with gain `0`,
while the even mixture gives `3/2` against EVERY alternative -- so
`bestSingle Gex = 0 < 3/2 = mixVal Gex (uniform)`. -/
theorem rank_two_complementarity :
    bestSingle Gex = 0 ∧ mixVal Gex (fun _ => (1 : ℝ) / 2) = 3 / 2 := by
  constructor
  · unfold bestSingle
    have hz : ∀ l : Fin 2,
        (univ : Finset (Fin 2)).inf' univ_nonempty (fun u => Gex u l) = 0 := by
      intro l
      refine le_antisymm ?_ ?_
      · have : Gex (l + 1) l = 0 := by
          unfold Gex
          have : l + 1 ≠ l := by fin_cases l <;> decide
          simp [this]
        calc (univ : Finset (Fin 2)).inf' univ_nonempty (fun u => Gex u l)
            ≤ Gex (l + 1) l := Finset.inf'_le _ (mem_univ _)
          _ = 0 := this
      · refine Finset.le_inf' _ _ fun u _ => ?_
        unfold Gex
        by_cases h : u = l <;> simp [h]
    simp only [hz]
    exact le_antisymm (Finset.sup'_le _ _ fun l _ => le_of_eq rfl)
      (Finset.le_sup' (fun _ : Fin 2 => (0 : ℝ)) (mem_univ (0 : Fin 2)))
  · unfold mixVal
    have hsum : ∀ u : Fin 2, ∑ l, (1 : ℝ) / 2 * Gex u l = 3 / 2 := by
      intro u
      fin_cases u <;> · unfold Gex; simp; norm_num
    simp only [hsum]
    exact le_antisymm (Finset.inf'_le _ (mem_univ (0 : Fin 2)))
      (Finset.le_inf' _ _ fun u _ => le_of_eq rfl)

#print axioms mixVal_pure
#print axioms bestSingle_le_mixVal_pure
#print axioms rank_one_no_complementarity
#print axioms rank_one_value
#print axioms rank_two_complementarity

end
end CIGAMF.P13.MasterGroupCalibration
