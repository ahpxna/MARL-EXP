import Mathlib
import «LeanQuerySufficiencyV4»

/-! Decision-theoretic necessity of query representations. -/

namespace CIGAMF.V7.QueryRepresentationNecessity

variable {M S D : Type*}

def Good (eps : ℝ) (L : M → D → ℝ) (Lstar : M → ℝ) (m : M) : Set D :=
  {d | L m d - Lstar m ≤ eps}

def CommonGoodOnFiber (eps : ℝ) (summary : M → S)
    (L : M → D → ℝ) (Lstar : M → ℝ) (s : S) (d : D) : Prop :=
  ∀ m, summary m = s → d ∈ Good eps L Lstar m

theorem QN1_same_summary_rule_implies_common_good
    (eps : ℝ) (summary : M → S) (L : M → D → ℝ) (Lstar : M → ℝ)
    (psi : S → D) (m1 m2 : M)
    (hsame : summary m1 = summary m2)
    (h1 : psi (summary m1) ∈ Good eps L Lstar m1)
    (h2 : psi (summary m2) ∈ Good eps L Lstar m2) :
    (Good eps L Lstar m1 ∩ Good eps L Lstar m2).Nonempty := by
  refine ⟨psi (summary m1), h1, ?_⟩
  simpa [hsame] using h2

theorem QN2_disjoint_good_sets_force_representation_separation
    (eps : ℝ) (summary : M → S) (L : M → D → ℝ) (Lstar : M → ℝ)
    (psi : S → D) (m1 m2 : M)
    (hdisjoint : Disjoint (Good eps L Lstar m1) (Good eps L Lstar m2))
    (h1 : psi (summary m1) ∈ Good eps L Lstar m1)
    (h2 : psi (summary m2) ∈ Good eps L Lstar m2) :
    summary m1 ≠ summary m2 := by
  intro hsame
  have hne := QN1_same_summary_rule_implies_common_good eps summary L Lstar
    psi m1 m2 hsame h1 h2
  exact Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hdisjoint) hne

section SubsetSelection

variable {ι : Type*} [DecidableEq ι]

theorem good_set_eq_singleton_of_unique_margin
    (eps : ℝ) (L : Finset ι → ℝ) (opt : Finset ι)
    (hself : L opt - L opt ≤ eps)
    (hmargin : ∀ d, d ≠ opt → eps < L d - L opt) :
    {d | L d - L opt ≤ eps} = ({opt} : Set (Finset ι)) := by
  ext d
  constructor
  · intro hd
    simp only [Set.mem_setOf_eq] at hd
    by_contra hne
    exact (not_lt_of_ge hd) (hmargin d hne)
  · intro hd
    simp only [Set.mem_singleton_iff] at hd
    subst d
    exact hself
    
theorem QN3_distinct_unique_subset_optima_have_disjoint_good_sets
    (eps : ℝ) (L1 L2 : Finset ι → ℝ) (opt1 opt2 : Finset ι)
    (hne : opt1 ≠ opt2)
    (hself1 : L1 opt1 - L1 opt1 ≤ eps)
    (hself2 : L2 opt2 - L2 opt2 ≤ eps)
    (hmargin1 : ∀ d, d ≠ opt1 → eps < L1 d - L1 opt1)
    (hmargin2 : ∀ d, d ≠ opt2 → eps < L2 d - L2 opt2) :
    Disjoint
      ({d | L1 d - L1 opt1 ≤ eps} : Set (Finset ι))
      ({d | L2 d - L2 opt2 ≤ eps} : Set (Finset ι)) := by
  rw [good_set_eq_singleton_of_unique_margin eps L1 opt1 hself1 hmargin1,
    good_set_eq_singleton_of_unique_margin eps L2 opt2 hself2 hmargin2]
  rw [Set.disjoint_left]
  intro d hd1 hd2
  simp only [Set.mem_singleton_iff] at hd1 hd2
  exact hne (hd1.symm.trans hd2)

end SubsetSelection

theorem QN4_uniform_fiber_optimality_requires_common_good_decision
    (eps : ℝ) (summary : M → S) (L : M → D → ℝ) (Lstar : M → ℝ)
    (psi : S → D) (s : S)
    (huniform : ∀ m, summary m = s → psi (summary m) ∈ Good eps L Lstar m) :
    CommonGoodOnFiber eps summary L Lstar s (psi s) := by
  intro m hm
  simpa [hm] using huniform m hm

theorem QN4_common_good_decision_is_sufficient_on_fiber
    (eps : ℝ) (summary : M → S) (L : M → D → ℝ) (Lstar : M → ℝ)
    (s : S) (d : D)
    (hcommon : CommonGoodOnFiber eps summary L Lstar s d) :
    ∃ psi : S → D, psi s = d ∧
      ∀ m, summary m = s → psi (summary m) ∈ Good eps L Lstar m := by
  let psi : S → D := fun _ => d
  refine ⟨psi, rfl, ?_⟩
  intro m hm
  change d ∈ Good eps L Lstar m
  exact hcommon m hm

end CIGAMF.V7.QueryRepresentationNecessity
