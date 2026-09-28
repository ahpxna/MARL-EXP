import Mathlib
import «LeanFunctionalCertificateLifetimeV1»
import «LeanFunctionalRankingV6»

/-! # Selective maintenance of functional Top-K certificates -/

namespace CIGAMF.P13.FunctionalSelectiveMaintenance

open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

def residualDrift (drift : I → ℝ) (refresh : Finset I) (j : I) : ℝ :=
  if j ∈ refresh then 0 else drift j

def SafeRefresh (lower upper drift : I → ℝ)
    (refresh selected : Finset I) : Prop :=
  ∀ j ∈ selected, ∀ l ∉ selected,
    residualDrift drift refresh j + residualDrift drift refresh l <
      lower j - upper l

theorem LIFE_B1_selective_refresh_safety
    (C Cfuture lower upper drift : I → ℝ)
    (refresh selected : Finset I) (k : ℕ)
    (hCard : selected.card = k)
    (hCoverage : ∀ j, lower j ≤ C j ∧ C j ≤ upper j)
    (hFuture : ∀ j,
      |Cfuture j - C j| ≤ residualDrift drift refresh j)
    (hSafe : SafeRefresh lower upper drift refresh selected) :
    CIGAMF.V6.FunctionalRanking.StrictTopK Cfuture selected k := by
  refine ⟨hCard, ?_⟩
  intro j hj l hl
  have hjLower := (abs_le.mp (hFuture j)).1
  have hlUpper := (abs_le.mp (hFuture l)).2
  have hMargin := hSafe j hj l hl
  have hjCover := (hCoverage j).1
  have hlCover := (hCoverage l).2
  linarith

theorem residualDrift_antitone
    (drift : I → ℝ) (refresh₁ refresh₂ : Finset I)
    (hSubset : refresh₁ ⊆ refresh₂) (hNonneg : ∀ j, 0 ≤ drift j) :
    ∀ j, residualDrift drift refresh₂ j ≤ residualDrift drift refresh₁ j := by
  intro j
  by_cases hj₁ : j ∈ refresh₁
  · have hj₂ := hSubset hj₁
    simp [residualDrift, hj₁, hj₂]
  · by_cases hj₂ : j ∈ refresh₂
    · simp [residualDrift, hj₁, hj₂, hNonneg j]
    · simp [residualDrift, hj₁, hj₂]

theorem LIFE_B2_refresh_set_monotonicity
    (lower upper drift : I → ℝ)
    (refresh₁ refresh₂ selected : Finset I)
    (hSubset : refresh₁ ⊆ refresh₂)
    (hNonneg : ∀ j, 0 ≤ drift j)
    (hSafe : SafeRefresh lower upper drift refresh₁ selected) :
    SafeRefresh lower upper drift refresh₂ selected := by
  intro j hj l hl
  have hjd := residualDrift_antitone drift refresh₁ refresh₂
    hSubset hNonneg j
  have hld := residualDrift_antitone drift refresh₁ refresh₂
    hSubset hNonneg l
  exact lt_of_le_of_lt (add_le_add hjd hld) (hSafe j hj l hl)

def RefreshCost (cost : I → ℝ) (refresh : Finset I) : ℝ :=
  ∑ j ∈ refresh, cost j

theorem LIFE_B3_minimum_cost_refresh_exists
    (lower upper drift cost : I → ℝ) (selected : Finset I)
    (hExists : ∃ refresh : Finset I,
      SafeRefresh lower upper drift refresh selected) :
    ∃ refresh : Finset I,
      SafeRefresh lower upper drift refresh selected ∧
      ∀ alternative : Finset I,
        SafeRefresh lower upper drift alternative selected →
          RefreshCost cost refresh ≤ RefreshCost cost alternative := by
  classical
  let feasible := Finset.univ.powerset.filter
    (fun refresh ↦ SafeRefresh lower upper drift refresh selected)
  have hFeasible : feasible.Nonempty := by
    rcases hExists with ⟨refresh, hRefresh⟩
    refine ⟨refresh, ?_⟩
    simp [feasible, hRefresh]
  rcases feasible.exists_min_image (RefreshCost cost) hFeasible with
    ⟨refresh, hRefresh, hMinimum⟩
  refine ⟨refresh, (Finset.mem_filter.1 hRefresh).2, ?_⟩
  intro alternative hAlternative
  exact hMinimum alternative (by simp [feasible, hAlternative])

theorem LIFE_B3_minimum_refresh_is_safe
    (C Cfuture lower upper drift : I → ℝ)
    (refresh selected : Finset I) (k : ℕ)
    (hCard : selected.card = k)
    (hCoverage : ∀ j, lower j ≤ C j ∧ C j ≤ upper j)
    (hFuture : ∀ j,
      |Cfuture j - C j| ≤ residualDrift drift refresh j)
    (hSafe : SafeRefresh lower upper drift refresh selected) :
    CIGAMF.V6.FunctionalRanking.StrictTopK Cfuture selected k :=
  LIFE_B1_selective_refresh_safety C Cfuture lower upper drift
    refresh selected k hCard hCoverage hFuture hSafe

def DependsOnlyOn {V R : Type*}
    (depends : Finset I) (evaluate : (I → V) → R) : Prop :=
  ∀ x y, (∀ j ∈ depends, x j = y j) → evaluate x = evaluate y

theorem LIFE_B4_dependency_locality
    {V R : Type*} (depends : Finset I) (evaluate : (I → V) → R)
    (hLocal : DependsOnlyOn depends evaluate)
    (old new : I → V)
    (hOutsideOnly : ∀ j ∈ depends, old j = new j) :
    evaluate old = evaluate new :=
  hLocal old new hOutsideOnly

end CIGAMF.P13.FunctionalSelectiveMaintenance
