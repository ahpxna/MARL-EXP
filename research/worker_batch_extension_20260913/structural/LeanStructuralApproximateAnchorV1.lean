import «LeanStructuralOrderedRadiusStepV1»

/-! Finite-minimum cheap extension from an approximate budget anchor.
The anchor error is carried through every extension step. -/
namespace CIGAMF.P13.StructuralApproximateAnchor
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension CIGAMF.P13.StructuralToleranceBudgetNet
open CIGAMF.P13.StructuralOrderedRadiusStep
open CIGAMF.P13.StructuralOrdinaryChainCharacterization
open CIGAMF.P13.StructuralMinimumTransversalWidth
section
variable {m : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]

lemma complement_nonempty (S : Finset (Fin m)) (hs : S.card < m) : Sᶜ.Nonempty := by
  apply card_pos.mp
  simp only [card_compl,card_univ,Fintype.card_fin]
  omega

/-- Uses the smallest unused index; it does not compare real-valued radii. -/
def nextIndex (S : Finset (Fin m)) (hs : S.card < m) : Fin m :=
  Sᶜ.min' (complement_nonempty S hs)

lemma nextIndex_not_mem (S : Finset (Fin m)) (hs : S.card < m) : nextIndex S hs ∉ S := by
  have h := min'_mem Sᶜ (complement_nonempty S hs)
  simpa only [nextIndex,mem_compl] using h

lemma nextIndex_cheap (c : Fin m → ℝ) (hc : Monotone c) (S : Finset (Fin m))
    (hs : S.card < m) : c (nextIndex S hs) ≤ weight c S.card := by
  obtain ⟨i,hi,hci⟩ := cheap_outside c hc S hs
  have hmin : nextIndex S hs ≤ i := min'_le Sᶜ i (mem_compl.mpr hi)
  exact (hc hmin).trans hci

def next (c : Fin m → ℝ) (hc : Monotone c) (S : Finset (Fin m)) : Finset (Fin m) :=
  if hs : S.card < m then insert (nextIndex S hs) S else S

def evolution (c : Fin m → ℝ) (hc : Monotone c) (S : Finset (Fin m)) : ℕ → Finset (Fin m)
  | 0 => S
  | t+1 => next c hc (evolution c hc S t)

noncomputable def accumulated (c : Fin m → ℝ) (a t : ℕ) := ∑ z ∈ range t,charge c (a+z)

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
    have hi := nextIndex_not_mem (evolution c hc S t) hs
    change (next c hc (evolution c hc S t)).card = _
    rw [next,dif_pos hs,card_insert_of_notMem hi,hcard]
    omega

theorem evolution_approx_optimal (f : Fin m → Ω → ℝ) (c : Fin m → ℝ) (hc : Monotone c)
    (hf : ∀ i, osc (f i)/2 ≤ c i) (S : Finset (Fin m))
    (eps : ℝ) (ho : EpsilonOptimalAt (selectedRadius f) eps S.card S)
    (t : ℕ) (ht : S.card+t ≤ m) :
    EpsilonOptimalAt (selectedRadius f) (eps+accumulated c S.card t)
      (S.card+t) (evolution c hc S t) := by
  induction t with
  | zero => simpa [evolution,accumulated] using ho
  | succ t ih =>
    have hprev := ih (by omega)
    have hcard := evolution_card c hc S t (by omega)
    have hs : (evolution c hc S t).card < m := by omega
    have hcheap := nextIndex_cheap c hc (evolution c hc S t) hs
    have hnot := nextIndex_not_mem (evolution c hc S t) hs
    have he := optimal_step_of_cheap f c hc hf _ _ hnot hcheap
      (eps+accumulated c S.card t) (by rw [hcard];exact hprev)
    change EpsilonOptimalAt _ _ _ (next c hc (evolution c hc S t))
    rw [next,dif_pos hs]
    simpa only [accumulated,sum_range_succ,hcard,Nat.add_assoc,add_assoc] using he

/-- One ranking realizes the entire cheap-extension trajectory. -/
theorem approximate_anchored_ranking (f : Fin m → Ω → ℝ) (c : Fin m → ℝ) (hc : Monotone c)
    (hf : ∀ i, osc (f i)/2 ≤ c i) (S : Finset (Fin m))
    (eps : ℝ) (ho : EpsilonOptimalAt (selectedRadius f) eps S.card S) :
    ∃ r : List (Fin m), IsFullRanking r ∧ ∀ t, S.card+t ≤ m →
      EpsilonOptimalAt (selectedRadius f) (eps+accumulated c S.card t)
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
  exact evolution_approx_optimal f c hc hf S eps ho t ht

#print axioms nextIndex_not_mem
#print axioms nextIndex_cheap
#print axioms evolution_card
#print axioms evolution_approx_optimal
#print axioms approximate_anchored_ranking
end
end CIGAMF.P13.StructuralApproximateAnchor
