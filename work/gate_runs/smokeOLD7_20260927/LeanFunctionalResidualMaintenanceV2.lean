import «LeanFunctionalSelectiveMaintenanceV1»


/-! Selective maintenance with nonzero post-refresh error bounds.
Safety is conditional on coverage and the stated future-error bound. -/
namespace CIGAMF.P13.FunctionalResidualMaintenance
open scoped BigOperators
open CIGAMF.P13.FunctionalSelectiveMaintenance
variable {I : Type*} [Fintype I] [DecidableEq I]

def residualBound (drift refreshed : I → ℝ) (refresh : Finset I) (j : I) : ℝ :=
  if j ∈ refresh then refreshed j else drift j

def SafeRefresh (lower upper drift refreshed : I → ℝ)
    (refresh selected : Finset I) : Prop :=
  ∀ j ∈ selected, ∀ l ∉ selected,
    residualBound drift refreshed refresh j + residualBound drift refreshed refresh l <
      lower j - upper l

theorem residualBound_zero (drift : I → ℝ) (refresh : Finset I) (j : I) :
    residualBound drift (fun _ => 0) refresh j = residualDrift drift refresh j := rfl

theorem selective_refresh_safety
    (C Cfuture lower upper drift refreshed : I → ℝ)
    (refresh selected : Finset I) (k : ℕ)
    (hCard : selected.card = k)
    (hCoverage : ∀ j, lower j ≤ C j ∧ C j ≤ upper j)
    (hFuture : ∀ j, |Cfuture j - C j| ≤ residualBound drift refreshed refresh j)
    (hSafe : SafeRefresh lower upper drift refreshed refresh selected) :
    CIGAMF.V6.FunctionalRanking.StrictTopK Cfuture selected k := by
  refine ⟨hCard, ?_⟩
  intro j hj l hl
  have hjLower := (abs_le.mp (hFuture j)).1
  have hlUpper := (abs_le.mp (hFuture l)).2
  have hMargin := hSafe j hj l hl
  have hjCover := (hCoverage j).1
  have hlCover := (hCoverage l).2
  linarith

theorem residualBound_antitone (drift refreshed : I → ℝ)
    (refresh₁ refresh₂ : Finset I) (hSubset : refresh₁ ⊆ refresh₂)
    (hImproves : ∀ j, refreshed j ≤ drift j) :
    ∀ j, residualBound drift refreshed refresh₂ j ≤ residualBound drift refreshed refresh₁ j := by
  intro j
  by_cases h₁ : j ∈ refresh₁
  · have h₂ := hSubset h₁
    simp [residualBound, h₁, h₂]
  · by_cases h₂ : j ∈ refresh₂
    · simp [residualBound, h₁, h₂, hImproves j]
    · simp [residualBound, h₁, h₂]

theorem refresh_set_monotonicity (lower upper drift refreshed : I → ℝ)
    (refresh₁ refresh₂ selected : Finset I) (hSubset : refresh₁ ⊆ refresh₂)
    (hImproves : ∀ j, refreshed j ≤ drift j)
    (hSafe : SafeRefresh lower upper drift refreshed refresh₁ selected) :
    SafeRefresh lower upper drift refreshed refresh₂ selected := by
  intro j hj l hl
  exact lt_of_le_of_lt (add_le_add
    (residualBound_antitone drift refreshed refresh₁ refresh₂ hSubset hImproves j)
    (residualBound_antitone drift refreshed refresh₁ refresh₂ hSubset hImproves l))
    (hSafe j hj l hl)

theorem feasible_iff_full_refresh_safe (lower upper drift refreshed : I → ℝ)
    (selected : Finset I) (hImproves : ∀ j, refreshed j ≤ drift j) :
    (∃ refresh, SafeRefresh lower upper drift refreshed refresh selected) ↔
      SafeRefresh lower upper drift refreshed Finset.univ selected := by
  constructor
  · rintro ⟨refresh, h⟩
    exact refresh_set_monotonicity lower upper drift refreshed refresh Finset.univ
      selected (Finset.subset_univ _) hImproves h
  · intro h; exact ⟨Finset.univ, h⟩

/-- Failure of full refresh rules out this sufficient certificate, not actual safety. -/
theorem no_feasible_refresh_of_full_failure (lower upper drift refreshed : I → ℝ)
    (selected : Finset I) (hImproves : ∀ j, refreshed j ≤ drift j)
    (hFail : ¬ SafeRefresh lower upper drift refreshed Finset.univ selected) :
    ¬ ∃ refresh, SafeRefresh lower upper drift refreshed refresh selected := by
  exact fun h => hFail ((feasible_iff_full_refresh_safe _ _ _ _ _ hImproves).mp h)

theorem minimum_cost_refresh_exists (lower upper drift refreshed cost : I → ℝ)
    (selected : Finset I)
    (hExists : ∃ refresh, SafeRefresh lower upper drift refreshed refresh selected) :
    ∃ refresh, SafeRefresh lower upper drift refreshed refresh selected ∧
      ∀ alternative, SafeRefresh lower upper drift refreshed alternative selected →
        RefreshCost cost refresh ≤ RefreshCost cost alternative := by
  classical
  let feasible := Finset.univ.powerset.filter
    (fun refresh ↦ SafeRefresh lower upper drift refreshed refresh selected)
  have hFeasible : feasible.Nonempty := by
    rcases hExists with ⟨refresh, hRefresh⟩
    exact ⟨refresh, by simp [feasible, hRefresh]⟩
  rcases feasible.exists_min_image (RefreshCost cost) hFeasible with
    ⟨refresh, hRefresh, hMinimum⟩
  refine ⟨refresh, (Finset.mem_filter.1 hRefresh).2, ?_⟩
  intro alternative hAlternative
  exact hMinimum alternative (by simp [feasible, hAlternative])
end CIGAMF.P13.FunctionalResidualMaintenance
