import «LeanPaperBGeometryV1»

/-!
# Paper B: the observation-order partition, DERIVED from a query family

`LeanPaperBGeometryV1.IndistAt` reads

    IndistAt s θ lam := θ = lam ∨ (s ≤ θ ∧ s ≤ lam),

which is a partition of the **world index**.  Every consequence drawn from it in the
geometry section is therefore conditional on that partition being the one an observer
actually faces, and nothing so far derived it from what an observer can measure.  This
module derives it, for an explicit moment family, in both directions:

* a query of order at most `s` is a linear functional of the moments of order `1..s`, and
  two worlds whose moments agree there give it the same value --- so the query is blind to
  the difference; and
* for every pair NOT in the same class at order `s` there IS a query of order at most `s`
  separating them.

Together: the order-`s` indistinguishability classes of this family are exactly
`classAt s`.  So on this family the partition is a theorem rather than a definition.

THE COEFFICIENT TABLE, AND WHAT IT IS NOT.  World `i` is the one whose first non-vanishing
coefficient sits at order `i+1`:

    coefOf i k = 1 if k = i + 1, else 0.

**These are expansion coefficients in the perturbation scale `h`, NOT raw moments of a
random variable.**  Read as raw moments the table is not realisable by any law: world `0`
would need `E X = 1` and `E X^2 = 0`, contradicting `(E X)^2 <= E X^2`.  An earlier version
of this file called them moments and said only that "a distribution realising them is not
constructed"; that understated the problem, because no distribution realises them.  What the
table is is the *shape* an order-`s` observer sees --- the first index at which two worlds'
density expansions differ --- and the theorems below are about the partition such a table
induces.

WHAT IS STILL OWED, AND IT IS THE SUBSTANCE.  The table is *posited* here.  Paper B's
obligation is to DERIVE it from the actual densities `p^q_{θ,h}` of the observation model:
the coefficient of `h^k` in the density expansion, uniformly over the admissible query
class.  Until that is done, the theorems below say what follows *from* a resolving-order
table, not that the model has this one.  Nor does this touch the safe-set family used by
`EXP_paperB_obstruction_law.py`, whose safe sets are equal within `u` and disjoint across it
--- that is a *different* family from the intersecting one the geometry theorems are about,
and the two must not be joined by prose.
-/

namespace CIGAMF.P13.PaperBIndist

open Finset
open CIGAMF.P13.PaperBGeometry

variable {m : ℕ}

/-! ## The family, and what a bounded-order query can see -/

/-- World `i`'s coefficient table: its first non-vanishing coefficient sits at order
`i+1`.  Expansion coefficients in `h`, **not** raw moments --- see the header. -/
def coefOf (m : ℕ) : Fin m → ℕ → ℝ := fun i k => if k = (i : ℕ) + 1 then 1 else 0

theorem coefOf_self (i : Fin m) : coefOf m i ((i : ℕ) + 1) = 1 := by
  simp [coefOf]

theorem coefOf_other (i : Fin m) (k : ℕ) (h : k ≠ (i : ℕ) + 1) :
    coefOf m i k = 0 := by
  simp [coefOf, h]

/-- Coefficients of order `1..s` agreeing: what an order-`s` observer records. -/
def AgreeUpTo (s : ℕ) (θ lam : Fin m) : Prop :=
  ∀ k, 1 ≤ k → k ≤ s → coefOf m θ k = coefOf m lam k

/-- A query of order at most `s`: a linear functional supported on coefficients `1..s`. -/
def QueryOfOrder (s : ℕ) (q : ℕ → ℝ) : Prop := ∀ k, (k = 0 ∨ s < k) → q k = 0

/-- Its value at a world. -/
noncomputable def queryValue (m : ℕ) (q : ℕ → ℝ) (θ : Fin m) : ℝ :=
  ∑ k ∈ Finset.range (m + 2), q k * coefOf m θ k

/-! ## The partition is exactly moment agreement -/

/-- **Agreement on coefficients `1..s` is the index condition.**  Computed from the table,
not posited on the index. -/
theorem agreeUpTo_iff_indistAt (s : ℕ) (θ lam : Fin m) :
    AgreeUpTo s θ lam ↔ IndistAt s θ lam := by
  constructor
  · intro hag
    by_cases hEq : θ = lam
    · exact Or.inl hEq
    · refine Or.inr ⟨?_, ?_⟩
      · by_contra hlt
        have hle : (θ : ℕ) + 1 ≤ s := by omega
        have h := hag ((θ : ℕ) + 1) (by omega) hle
        rw [coefOf_self θ] at h
        have hne : (θ : ℕ) + 1 ≠ (lam : ℕ) + 1 := by
          intro hc
          exact hEq (Fin.ext (by omega))
        rw [coefOf_other lam _ hne] at h
        norm_num at h
      · by_contra hlt
        have hle : (lam : ℕ) + 1 ≤ s := by omega
        have h := hag ((lam : ℕ) + 1) (by omega) hle
        rw [coefOf_self lam] at h
        have hne : (lam : ℕ) + 1 ≠ (θ : ℕ) + 1 := by
          intro hc
          exact hEq (Fin.ext (by omega))
        rw [coefOf_other θ _ hne] at h
        norm_num at h
  · intro hind k hk1 hks
    rcases hind with rfl | ⟨h1, h2⟩
    · rfl
    · have hθ : k ≠ (θ : ℕ) + 1 := by omega
      have hlam : k ≠ (lam : ℕ) + 1 := by omega
      rw [coefOf_other θ k hθ, coefOf_other lam k hlam]

/-- **A bounded-order query cannot separate worlds in the same class.** -/
theorem query_blind_of_indistAt (s : ℕ) (q : ℕ → ℝ) (hq : QueryOfOrder s q)
    (θ lam : Fin m) (h : IndistAt s θ lam) :
    queryValue m q θ = queryValue m q lam := by
  have hag := (agreeUpTo_iff_indistAt s θ lam).mpr h
  unfold queryValue
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk0 : k = 0
  · rw [hq k (Or.inl hk0)]; ring
  · by_cases hks : s < k
    · rw [hq k (Or.inr hks)]; ring
    · rw [hag k (by omega) (by omega)]

/-- **And for every pair outside the class there is one that does.**  The separating query
is the indicator at the order where the resolved world first moves. -/
theorem exists_query_separating (s : ℕ) (θ lam : Fin m) (h : ¬ IndistAt s θ lam) :
    ∃ q : ℕ → ℝ, QueryOfOrder s q ∧ queryValue m q θ ≠ queryValue m q lam := by
  classical
  have hEq : θ ≠ lam := fun hc => h (Or.inl hc)
  have hsplit : (θ : ℕ) < s ∨ (lam : ℕ) < s := by
    by_contra hc
    push_neg at hc
    exact h (Or.inr ⟨hc.1, hc.2⟩)
  have key : ∀ a b : Fin m, a ≠ b → (a : ℕ) < s →
      ∃ q : ℕ → ℝ, QueryOfOrder s q ∧ queryValue m q a ≠ queryValue m q b := by
    intro a b hab ha
    refine ⟨fun k => if k = (a : ℕ) + 1 then 1 else 0, ?_, ?_⟩
    · intro k hk
      rcases hk with hk | hk
      · have : k ≠ (a : ℕ) + 1 := by omega
        simp [this]
      · have : k ≠ (a : ℕ) + 1 := by omega
        simp [this]
    · have hmem : (a : ℕ) + 1 ∈ Finset.range (m + 2) := by
        have hlt := a.isLt
        rw [Finset.mem_range]
        omega
      have hval : ∀ x : Fin m,
          queryValue m (fun k => if k = (a : ℕ) + 1 then (1 : ℝ) else 0) x
            = coefOf m x ((a : ℕ) + 1) := by
        intro x
        unfold queryValue
        have hterm : ∀ k ∈ Finset.range (m + 2),
            (if k = (a : ℕ) + 1 then (1 : ℝ) else 0) * coefOf m x k
              = if k = (a : ℕ) + 1 then coefOf m x k else 0 := by
          intro k _
          by_cases hk : k = (a : ℕ) + 1 <;> simp [hk]
        rw [Finset.sum_congr rfl hterm,
            Finset.sum_ite_eq' (Finset.range (m + 2)) ((a : ℕ) + 1) (coefOf m x),
            if_pos hmem]
      have hne : (a : ℕ) + 1 ≠ (b : ℕ) + 1 := by
        intro hc
        exact hab (Fin.ext (by omega))
      rw [hval a, hval b, coefOf_self a, coefOf_other b _ hne]
      norm_num
  rcases hsplit with hθ | hlam
  · exact key θ lam hEq hθ
  · obtain ⟨q, hq, hne⟩ := key lam θ hEq.symm hlam
    exact ⟨q, hq, hne.symm⟩

/-- **The partition is exactly the observational one.**  Same class at order `s` iff no
query of order at most `s` separates the two worlds --- the statement Paper B needs in place
of a definition on the index. -/
theorem indistAt_iff_no_separating_query (s : ℕ) (θ lam : Fin m) :
    IndistAt s θ lam ↔
      ∀ q : ℕ → ℝ, QueryOfOrder s q → queryValue m q θ = queryValue m q lam := by
  constructor
  · intro h q hq
    exact query_blind_of_indistAt s q hq θ lam h
  · intro hall
    by_contra hcon
    obtain ⟨q, hq, hne⟩ := exists_query_separating s θ lam hcon
    exact hne (hall q hq)

/-! ## Audit -/

#print axioms coefOf_self
#print axioms agreeUpTo_iff_indistAt
#print axioms query_blind_of_indistAt
#print axioms exists_query_separating
#print axioms indistAt_iff_no_separating_query

end CIGAMF.P13.PaperBIndist
