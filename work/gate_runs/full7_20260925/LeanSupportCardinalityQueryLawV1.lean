import «LeanSupportAdaptiveQuerySeparationV1»

/-! Exact adaptive membership cost for every cardinality s<m in the actual
multi-tip support family. Zero-error worst-case complexity is exactly s,
including s=0. The decoder uses the known cardinality bound. -/
namespace CIGAMF.P13.SupportCardinalityQueryLaw
open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportUnboundedObstruction (tip)
open CIGAMF.P13.SupportMultiTipGeometry
open CIGAMF.P13.SupportAdaptiveQuerySeparation (Tree depth run positiveQueries positiveOutput
  positive_card_le_depth search depth_search)
noncomputable section
variable {m : ℕ}

def oracle (W : Finset (Fin m)) (a : Fin m) : Bool := decide (tip a ∈ support W)

lemma oracle_formula (hm : 2 ≤ m) (W : Finset (Fin m)) (a : Fin m) :
    oracle W a = decide (a ∈ W) := by simp [oracle,physical_membership_iff hm]

lemma run_positive (hm : 2 ≤ m) (t : Tree m) (W : Finset (Fin m))
    (hW : positiveQueries t ⊆ W) : run (oracle W) t=positiveOutput t := by
  induction t with
  | leaf j => rfl
  | ask a no yes ihno ihyes =>
    have ha : a ∈ W := hW (mem_insert_self _ _)
    have hy : positiveQueries yes ⊆ W := fun i hi => hW (mem_insert_of_mem hi)
    simpa [run,oracle_formula hm,ha,positiveOutput] using ihyes hy

theorem adaptive_cardinality_lower (hm : 2 ≤ m) (s : ℕ) (hs : s < m) (t : Tree m)
    (hsound : ∀ W : Finset (Fin m), W.card=s →
      selectedRadius (components W) {run (oracle W) t}=0) : s ≤ depth t := by
  by_contra h
  have hd : depth t < s := by omega
  let Q := insert (positiveOutput t) (positiveQueries t)
  have hQ : Q.card ≤ s := by
    have hc := card_insert_le (positiveOutput t) (positiveQueries t)
    have ht := positive_card_le_depth t
    dsimp [Q];omega
  obtain ⟨W,hQW,_,hcard⟩ := exists_subsuperset_card_eq
    (subset_univ Q) hQ (show s ≤ (univ : Finset (Fin m)).card by simp;omega)
  have hp : positiveQueries t ⊆ W := fun i hi => hQW (mem_insert_of_mem hi)
  have he := hsound W hcard
  rw [run_positive hm t W hp] at he
  exact ((zero_radius_iff hm W (positiveOutput t)).mp he) (hQW (mem_insert_self _ _))

lemma search_dichotomy (hm : 2 ≤ m) (W : Finset (Fin m)) (fallback : Fin m)
    (xs : List (Fin m)) :
    run (oracle W) (search fallback xs) ∉ W ∨
      (run (oracle W) (search fallback xs)=fallback ∧ xs.toFinset ⊆ W) := by
  induction xs with
  | nil => exact Or.inr ⟨rfl,empty_subset _⟩
  | cons a xs ih =>
    by_cases ha : a ∈ W
    · simp only [search,run,oracle_formula hm,ha,decide_true,↓reduceIte]
      rcases ih with h | ⟨he,hsub⟩
      · exact Or.inl h
      · exact Or.inr ⟨he,by simpa using insert_subset ha hsub⟩
    · exact Or.inl (by simpa [search,run,oracle_formula hm,ha] using ha)

theorem bounded_cardinality_search_sound (hm : 2 ≤ m) (s : ℕ)
    (W Q : Finset (Fin m)) (hW : W.card ≤ s) (hQ : Q.card=s)
    (fallback : Fin m) (hf : fallback ∉ Q) :
    selectedRadius (components W) {run (oracle W) (search fallback Q.toList)}=0 := by
  apply (zero_radius_iff hm W _).mpr
  rcases search_dichotomy hm W fallback Q.toList with h | ⟨he,hsub⟩
  · exact h
  · rw [he]
    have hsub' : Q ⊆ W := by simpa using hsub
    have hEq : Q=W := eq_of_subset_of_card_le hsub' (by omega)
    rwa [← hEq]

/-- A single tree is chosen before W, attains s queries, and is sound even
under the stronger promise |W|≤s. -/
theorem adaptive_cardinality_attained (hm : 2 ≤ m) (s : ℕ) (hs : s < m)
    (fallback : Fin m) :
    ∃ t : Tree m, depth t=s ∧ ∀ W : Finset (Fin m), W.card ≤ s →
      selectedRadius (components W) {run (oracle W) t}=0 := by
  obtain ⟨Q,hQsub,hQ⟩ := (univ.erase fallback).exists_subset_card_eq
    (show s ≤ (univ.erase fallback).card by simp;omega)
  have hf : fallback ∉ Q := by
    intro h;exact (mem_erase.mp (hQsub h)).1 rfl
  refine ⟨search fallback Q.toList,by simp [depth_search,hQ],?_⟩
  intro W hW
  exact bounded_cardinality_search_sound hm s W Q hW hQ fallback hf

#print axioms adaptive_cardinality_lower
#print axioms bounded_cardinality_search_sound
#print axioms adaptive_cardinality_attained
end
end CIGAMF.P13.SupportCardinalityQueryLaw
