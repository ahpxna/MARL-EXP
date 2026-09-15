import «LeanStructuralToleranceBudgetNetV1»
import Mathlib.Order.Interval.Finset.Fin

/-! Order-statistic extension step. Component radii need not be balanced.
Coordinates are ordered by their radius; the budget error charges one forward
and one reversed order statistic. -/
namespace CIGAMF.P13.StructuralOrderedRadiusStep
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.StructuralPrefixCoverDimension CIGAMF.P13.StructuralToleranceBudgetNet
noncomputable section
variable {m : ℕ} {Ω : Type*} [Fintype Ω] [Nonempty Ω]

def weight (c : Fin m → ℝ) (k : ℕ) : ℝ := if h : k < m then c ⟨k,h⟩ else 0

def charge (c : Fin m → ℝ) (k : ℕ) : ℝ := weight c k+weight c (m-1-k)

lemma cheap_outside (c : Fin m → ℝ) (hc : Monotone c) (S : Finset (Fin m))
    (hs : S.card < m) : ∃ i ∉ S, c i ≤ weight c S.card := by
  let a : Fin m := ⟨S.card,hs⟩
  have hn : ¬ Iic a ⊆ S := by
    intro h
    have hh := card_le_card h
    simp only [Fin.card_Iic] at hh
    dsimp [a] at hh
    omega
  obtain ⟨i,hi,hni⟩ := not_subset.mp hn
  refine ⟨i,hni,?_⟩
  have hh := hc (mem_Iic.mp hi)
  simpa [weight,hs,a] using hh

lemma cheap_inside (c : Fin m → ℝ) (hc : Monotone c) (T : Finset (Fin m))
    (ht : 0 < T.card) : ∃ i ∈ T, c i ≤ weight c (m-T.card) := by
  have hcomp : Tᶜ.card < m := by simpa only [card_compl,card_univ,Fintype.card_fin] using (Nat.sub_lt (lt_of_lt_of_le ht (by simpa using card_le_univ T)) ht)
  obtain ⟨i,hi,hc'⟩ := cheap_outside c hc Tᶜ hcomp
  exact ⟨i,by simpa using hi,by simpa [card_compl] using hc'⟩

lemma radius_add_bound (f : Fin m → Ω → ℝ) (c : Fin m → ℝ)
    (hc : ∀ i, osc (f i)/2 ≤ c i) (S : Finset (Fin m)) (i : Fin m) (hi : i ∉ S) :
    |selectedRadius f (insert i S)-selectedRadius f S| ≤ c i := by
  have h := radius_nested_change f S (insert i S) (subset_insert _ _)
  have he : insert i S\S = {i} := by ext j;by_cases hji : j=i <;> simp [hji,hi]
  rw [he,sum_singleton] at h
  simpa [abs_sub_comm] using h.trans (hc i)

/-- Extending an epsilon optimum by a cheap coordinate increases error by
c[k]+c[m-1-k]. This is an actual selectedRadius statement, not an abstract
Lipschitz contract supplied by the caller. -/
theorem optimal_step (f : Fin m → Ω → ℝ) (c : Fin m → ℝ) (hc : Monotone c)
    (hf : ∀ i, osc (f i)/2 ≤ c i) (S : Finset (Fin m)) (hs : S.card < m)
    (eps : ℝ) (ho : EpsilonOptimalAt (selectedRadius f) eps S.card S) :
    ∃ i ∉ S, EpsilonOptimalAt (selectedRadius f) (eps+charge c S.card)
      (S.card+1) (insert i S) := by
  obtain ⟨i,hi,hci⟩ := cheap_outside c hc S hs
  refine ⟨i,hi,by simp [hi],?_⟩
  intro T hT
  obtain ⟨j,hj,hcj⟩ := cheap_inside c hc T (by omega)
  have he : (T.erase j).card=S.card := by rw [card_erase_of_mem hj,hT];omega
  have ht := ho.2 (T.erase j) he
  have h1 := (abs_le.mp (radius_add_bound f c hf S i hi)).2
  have h2 := (abs_le.mp (radius_add_bound f c hf (T.erase j) j (by simp))).1
  rw [insert_erase hj] at h2
  have hh : m-T.card=m-1-S.card := by omega
  rw [hh] at hcj
  unfold charge
  linarith

theorem optimal_step_of_cheap (f : Fin m → Ω → ℝ) (c : Fin m → ℝ) (hc : Monotone c)
    (hf : ∀ i, osc (f i)/2 ≤ c i) (S : Finset (Fin m)) (i : Fin m)
    (hi : i ∉ S) (hci : c i ≤ weight c S.card)
    (eps : ℝ) (ho : EpsilonOptimalAt (selectedRadius f) eps S.card S) :
    EpsilonOptimalAt (selectedRadius f) (eps+charge c S.card) (S.card+1) (insert i S) := by
  refine ⟨by simp [hi],?_⟩
  intro T hT
  obtain ⟨j,hj,hcj⟩ := cheap_inside c hc T (by omega)
  have he : (T.erase j).card=S.card := by rw [card_erase_of_mem hj,hT];omega
  have ht := ho.2 (T.erase j) he
  have h1 := (abs_le.mp (radius_add_bound f c hf S i hi)).2
  have h2 := (abs_le.mp (radius_add_bound f c hf (T.erase j) j (by simp))).1
  rw [insert_erase hj] at h2
  have hh : m-T.card=m-1-S.card := by omega
  rw [hh] at hcj
  unfold charge
  linarith

lemma weight_sum (c : Fin m → ℝ) : (∑ k ∈ range m,weight c k)=∑ i,c i := by
  rw [← Fin.sum_univ_eq_sum_range (f := fun k => weight c k)]
  apply sum_congr rfl
  intro i _
  simp [weight,i.isLt]

theorem total_charge (c : Fin m → ℝ) : (∑ k ∈ range m,charge c k)=2*∑ i,c i := by
  simp only [charge,sum_add_distrib]
  have he : (∑ k ∈ range m,weight c (m-1-k)) = ∑ k ∈ range m,weight c k := by
    convert sum_range_reflect (weight c) m using 1 <;> congr 1 <;> funext k <;> congr 1 <;> omega
  rw [he,weight_sum]
  ring

#print axioms total_charge
#print axioms cheap_outside
#print axioms optimal_step
#print axioms weight_sum
end
end CIGAMF.P13.StructuralOrderedRadiusStep
