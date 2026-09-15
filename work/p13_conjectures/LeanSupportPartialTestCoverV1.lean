import Mathlib
import «LeanSupportCriticalIdentificationV1»

/-!
# Support separation as an exact partial-test-cover instance

The reduction uses ordered support-world pairs only to avoid quotienting
unordered pairs in Lean.  Each pair occurs together with its reversal, which
does not change the feasible query sets or their minimum cardinality.

This is an exact finite mapping, not an NP-hardness claim.
-/

namespace CIGAMF.P13.SupportPartialTestCover

open CIGAMF.P13.SupportCriticalIdentification

variable {A D : Type*} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

abbrev SupportPair (A : Type*) := Finset A × Finset A

noncomputable def incompatibleSupportPairs
    (regret : Finset A → D → ℝ) (eps : ℝ) : Finset (SupportPair A) := by
  classical
  exact Finset.univ.filter fun pair ↦
    Incompatible regret eps pair.1 pair.2

noncomputable def supportCellTest
    (regret : Finset A → D → ℝ) (eps : ℝ) (a : A) :
    Finset (SupportPair A) := by
  classical
  exact (incompatibleSupportPairs regret eps).filter fun pair ↦
    Distinguishes a pair.1 pair.2

noncomputable def partialTestUnion
    (regret : Finset A → D → ℝ) (eps : ℝ) (queries : Finset A) :
    Finset (SupportPair A) := by
  classical
  exact queries.biUnion (supportCellTest regret eps)

def PartialTestCover
    (regret : Finset A → D → ℝ) (eps : ℝ) (queries : Finset A) : Prop :=
  partialTestUnion regret eps queries = incompatibleSupportPairs regret eps

theorem mem_incompatibleSupportPairs_iff
    (regret : Finset A → D → ℝ) (eps : ℝ) (pair : SupportPair A) :
    pair ∈ incompatibleSupportPairs regret eps ↔
      Incompatible regret eps pair.1 pair.2 := by
  classical
  simp [incompatibleSupportPairs]

theorem mem_supportCellTest_iff
    (regret : Finset A → D → ℝ) (eps : ℝ) (a : A) (pair : SupportPair A) :
    pair ∈ supportCellTest regret eps a ↔
      Incompatible regret eps pair.1 pair.2 ∧ Distinguishes a pair.1 pair.2 := by
  classical
  simp [supportCellTest, incompatibleSupportPairs]

theorem partialTestUnion_subset_incompatiblePairs
    (regret : Finset A → D → ℝ) (eps : ℝ) (queries : Finset A) :
    partialTestUnion regret eps queries ⊆ incompatibleSupportPairs regret eps := by
  classical
  intro pair hpair
  rcases Finset.mem_biUnion.mp hpair with ⟨a, ha, htest⟩
  exact (mem_incompatibleSupportPairs_iff regret eps pair).2
    ((mem_supportCellTest_iff regret eps a pair).1 htest).1

/-- Exact reduction: the semantically universal support-query predicate is
precisely coverage of every incompatible support-world pair by the tests
induced by queried support cells. -/
theorem SUPPORT_separating_queries_iff_partial_test_cover
    (regret : Finset A → D → ℝ) (eps : ℝ) (queries : Finset A) :
    Separates regret eps queries ↔ PartialTestCover regret eps queries := by
  classical
  constructor
  · intro hSeparate
    apply Finset.Subset.antisymm (partialTestUnion_subset_incompatiblePairs regret eps queries)
    intro pair hPair
    have hIncompatible := (mem_incompatibleSupportPairs_iff regret eps pair).1 hPair
    rcases hSeparate pair.1 pair.2 hIncompatible with ⟨a, ha, hDistinguishes⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨a, ha, (mem_supportCellTest_iff regret eps a pair).2
      ⟨hIncompatible, hDistinguishes⟩⟩
  · intro hCover
    intro omega₁ omega₂ hIncompatible
    let pair : SupportPair A := (omega₁, omega₂)
    have hPair : pair ∈ incompatibleSupportPairs regret eps :=
      (mem_incompatibleSupportPairs_iff regret eps pair).2 hIncompatible
    have hUnion : pair ∈ partialTestUnion regret eps queries := by
      rw [hCover]
      exact hPair
    rcases Finset.mem_biUnion.mp hUnion with ⟨a, ha, htest⟩
    exact ⟨a, ha, (mem_supportCellTest_iff regret eps a pair).1 htest |>.2⟩

noncomputable def minimumSupportQueryCardinality
    (regret : Finset A → D → ℝ) (eps : ℝ) : ℕ :=
  sInf {K : ℕ | ∃ queries : Finset A,
    queries.card ≤ K ∧ Separates regret eps queries}

noncomputable def partialTestCoverOptimum
    (regret : Finset A → D → ℝ) (eps : ℝ) : ℕ :=
  sInf {K : ℕ | ∃ queries : Finset A,
    queries.card ≤ K ∧ PartialTestCover regret eps queries}

/-- The two optimization problems have literally the same feasible cardinality
levels.  This is the promised minimum-cardinality partial-test-cover mapping. -/
theorem SUPPORT_min_query_cardinality_eq_partial_test_cover_optimum
    (regret : Finset A → D → ℝ) (eps : ℝ) :
    minimumSupportQueryCardinality regret eps =
      partialTestCoverOptimum regret eps := by
  unfold minimumSupportQueryCardinality partialTestCoverOptimum
  congr 1
  ext K
  constructor
  · rintro ⟨queries, hCard, hSeparate⟩
    exact ⟨queries, hCard,
      (SUPPORT_separating_queries_iff_partial_test_cover regret eps queries).1 hSeparate⟩
  · rintro ⟨queries, hCard, hCover⟩
    exact ⟨queries, hCard,
      (SUPPORT_separating_queries_iff_partial_test_cover regret eps queries).2 hCover⟩

end CIGAMF.P13.SupportPartialTestCover
