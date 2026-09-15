import «LeanStructuralOrderedRadiusStepV1»

/-! A single full ranking from every exact budget anchor, with ordered-radius
error control simultaneously at all later budgets. -/
namespace CIGAMF.P13.StructuralOrderedRadiusChain
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension CIGAMF.P13.StructuralToleranceBudgetNet
open CIGAMF.P13.StructuralOrderedRadiusStep
open CIGAMF.P13.StructuralOrdinaryChainCharacterization
open CIGAMF.P13.StructuralMinimumTransversalWidth
noncomputable section
variable {m : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def next (c : Fin m → ℝ) (hc : Monotone c) (S : Finset (Fin m)) : Finset (Fin m) :=
  if hs : S.card < m then insert (Classical.choose (cheap_outside c hc S hs)) S else S

def evolution (c : Fin m → ℝ) (hc : Monotone c) (S : Finset (Fin m)) : ℕ → Finset (Fin m)
  | 0 => S
  | t+1 => next c hc (evolution c hc S t)

def accumulated (c : Fin m → ℝ) (a t : ℕ) := ∑ z ∈ range t,charge c (a+z)

lemma subset_next (c : Fin m → ℝ) (hc : Monotone c) (S : Finset (Fin m)) : S ⊆ next c hc S := by
  unfold next;split_ifs <;> simp

lemma evolution_mono (c : Fin m → ℝ) (hc : Monotone c) (S : Finset (Fin m)) :
    Monotone (evolution c hc S) := by
  apply monotone_nat_of_le_succ
  intro t
  exact subset_next c hc _

lemma evolution_card (c : Fin m → ℝ) (hc : Monotone c) (S : Finset (Fin m))
    (t : ℕ) (ht : S.card+t ≤ m) : (evolution c hc S t).card=S.card+t := by
  induction t with
  | zero => simp [evolution]
  | succ t ih =>
    have hcard := ih (by omega)
    have hs : (evolution c hc S t).card < m := by omega
    have hi := (Classical.choose_spec (cheap_outside c hc _ hs)).1
    change (next c hc (evolution c hc S t)).card = _
    rw [next,dif_pos hs,card_insert_of_notMem hi,hcard]
    omega

lemma evolution_optimal (f : Fin m → Ω → ℝ) (c : Fin m → ℝ) (hc : Monotone c)
    (hf : ∀ i, osc (f i)/2 ≤ c i) (S : Finset (Fin m))
    (ho : EpsilonOptimalAt (selectedRadius f) 0 S.card S)
    (t : ℕ) (ht : S.card+t ≤ m) :
    EpsilonOptimalAt (selectedRadius f) (accumulated c S.card t)
      (S.card+t) (evolution c hc S t) := by
  induction t with
  | zero => simpa [evolution,accumulated] using ho
  | succ t ih =>
    have hprev := ih (by omega)
    have hcard := evolution_card c hc S t (by omega)
    have hs : (evolution c hc S t).card < m := by omega
    have hcheap := Classical.choose_spec (cheap_outside c hc _ hs)
    have he := optimal_step_of_cheap f c hc hf _ _ hcheap.1 hcheap.2
      (accumulated c S.card t) (by rw [hcard];exact hprev)
    change EpsilonOptimalAt _ _ _ (next c hc (evolution c hc S t))
    rw [next,dif_pos hs]
    simpa only [accumulated,sum_range_succ,hcard,Nat.add_assoc] using he

/-- One ranking realizes the entire cheap-extension trajectory. -/
theorem anchored_ranking (f : Fin m → Ω → ℝ) (c : Fin m → ℝ) (hc : Monotone c)
    (hf : ∀ i, osc (f i)/2 ≤ c i) (S : Finset (Fin m))
    (ho : EpsilonOptimalAt (selectedRadius f) 0 S.card S) :
    ∃ r : List (Fin m), IsFullRanking r ∧ ∀ t, S.card+t ≤ m →
      EpsilonOptimalAt (selectedRadius f) (accumulated c S.card t)
        (S.card+t) (prefixSet r (S.card+t)) := by
  let C := (range (m-S.card+1)).image (evolution c hc S)
  have hC : InclusionChain C := by
    intro A hA B hB
    obtain ⟨a,_,rfl⟩ := mem_image.mp hA
    obtain ⟨b,_,rfl⟩ := mem_image.mp hB
    rcases le_total a b with h | h
    · exact Or.inl (evolution_mono c hc S h)
    · exact Or.inr (evolution_mono c hc S h)
  obtain ⟨r,hr,hprefix⟩ := finite_inclusion_chain_extends_to_full_ranking C hC
  refine ⟨r,hr,?_⟩
  intro t ht
  have hmem : evolution c hc S t ∈ C := mem_image.mpr ⟨t,mem_range.mpr (by omega),rfl⟩
  have he := hprefix _ hmem
  rw [evolution_card c hc S t ht] at he
  rw [he]
  exact evolution_optimal f c hc hf S ho t ht

#print axioms evolution_card
#print axioms evolution_optimal
#print axioms anchored_ranking
end
end CIGAMF.P13.StructuralOrderedRadiusChain
