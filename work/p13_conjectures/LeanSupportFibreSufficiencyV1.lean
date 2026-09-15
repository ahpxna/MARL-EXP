import «LeanSupportCriticalIdentificationV1»


/-! Exact whole-fibre condition for a universally safe support controller.
Pairwise separation alone need not suffice for the abstract regret API. -/
namespace CIGAMF.P13.SupportFibreSufficiency
open CIGAMF.P13.SupportCriticalIdentification
variable {A D : Type*} [Fintype A] [DecidableEq A]

def FibreSafe (regret : Finset A → D → ℝ) (eps : ℝ) (queries : Finset A) : Prop :=
  ∀ signature : A → Bool, ∃ decision : D,
    ∀ omega, QueryObservation queries omega = signature → regret omega decision ≤ eps

theorem universal_controller_iff_fibreSafe
    (regret : Finset A → D → ℝ) (eps : ℝ) (queries : Finset A) :
    (∃ controller : (A → Bool) → D,
      ∀ omega, regret omega (controller (QueryObservation queries omega)) ≤ eps) ↔
      FibreSafe regret eps queries := by
  classical
  constructor
  · rintro ⟨controller, h⟩ signature
    refine ⟨controller signature, ?_⟩
    intro omega hSame
    simpa [hSame] using h omega
  · intro h
    choose controller hController using h
    exact ⟨controller, fun omega => hController _ omega rfl⟩

theorem fibreSafe_implies_separates
    (regret : Finset A → D → ℝ) (eps : ℝ) (queries : Finset A)
    (h : FibreSafe regret eps queries) : Separates regret eps queries :=
  SUP_B2_universal_query_set_must_separate regret eps queries
    ((universal_controller_iff_fibreSafe regret eps queries).mpr h)

theorem minimum_safe_query_set_exists
    (regret : Finset A → D → ℝ) (eps : ℝ)
    (hExists : ∃ queries, FibreSafe regret eps queries) :
    ∃ optimal, FibreSafe regret eps optimal ∧
      ∀ queries, FibreSafe regret eps queries → optimal.card ≤ queries.card := by
  classical
  let feasible := Finset.univ.powerset.filter (FibreSafe regret eps)
  have hFeasible : feasible.Nonempty := by
    rcases hExists with ⟨queries, hQueries⟩
    exact ⟨queries, by simp [feasible, hQueries]⟩
  rcases feasible.exists_min_image Finset.card hFeasible with ⟨optimal,hOptimal,hMin⟩
  refine ⟨optimal, (Finset.mem_filter.1 hOptimal).2, ?_⟩
  intro queries hQueries
  exact hMin queries (by simp [feasible, hQueries])

/-- Each support forbids exactly one of three decisions. -/
def bad (omega : Finset (Fin 2)) : Fin 3 :=
  if 0 ∈ omega then (if 1 ∈ omega then 2 else 0) else 1

def toyRegret (omega : Finset (Fin 2)) (d : Fin 3) : ℝ :=
  if d = bad omega then 1 else 0

theorem toy_good_iff (omega : Finset (Fin 2)) (d : Fin 3) :
    toyRegret omega d ≤ 0 ↔ d ≠ bad omega := by
  by_cases h : d = bad omega <;> simp [toyRegret, h]

theorem two_forbidden_have_alternative : ∀ i j : Fin 3,
    ∃ d : Fin 3, d ≠ i ∧ d ≠ j := by decide

theorem every_pair_has_common_good (omega₁ omega₂ : Finset (Fin 2)) :
    ∃ d, toyRegret omega₁ d ≤ 0 ∧ toyRegret omega₂ d ≤ 0 := by
  obtain ⟨d,h₁,h₂⟩ := two_forbidden_have_alternative (bad omega₁) (bad omega₂)
  exact ⟨d, (toy_good_iff _ _).mpr h₁, (toy_good_iff _ _).mpr h₂⟩

theorem empty_queries_separate : Separates toyRegret 0 ∅ := by
  intro omega₁ omega₂ hIncompatible
  obtain ⟨d,h₁,h₂⟩ := every_pair_has_common_good omega₁ omega₂
  exact False.elim (Set.disjoint_left.1 hIncompatible h₁ h₂)

theorem bad_surjective : ∀ d : Fin 3, ∃ omega, bad omega = d := by
  intro d
  fin_cases d
  · exact ⟨{0}, by decide⟩
  · exact ⟨∅, by decide⟩
  · exact ⟨{0,1}, by decide⟩

theorem empty_queries_not_fibreSafe : ¬ FibreSafe toyRegret 0 ∅ := by
  intro h
  obtain ⟨d, hd⟩ := h (fun _ => false)
  obtain ⟨omega, hBad⟩ := bad_surjective d
  have hGood := hd omega (by funext a; simp [QueryObservation])
  exact ((toy_good_iff _ _).mp hGood) hBad.symm

/-- A concrete separation/sufficiency gap in the existing abstract support API. -/
theorem pairwise_separation_not_sufficient :
    Separates toyRegret 0 ∅ ∧
      ¬ ∃ controller : (Fin 2 → Bool) → Fin 3,
        ∀ omega, toyRegret omega (controller (QueryObservation ∅ omega)) ≤ 0 := by
  refine ⟨empty_queries_separate, ?_⟩
  intro h
  exact empty_queries_not_fibreSafe ((universal_controller_iff_fibreSafe _ _ _).mp h)
end CIGAMF.P13.SupportFibreSufficiency
