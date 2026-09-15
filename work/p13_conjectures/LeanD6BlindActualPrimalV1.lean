import «LeanD6BlindActualMomentsV1»
import «LeanD6BlindPrimalCertificateV1»

/-! A single explicit legal allocation, independent of A, realizes the blind
primal lower bound simultaneously on the entire D6 hidden-label family.
This is a static primal theorem; the universal blind dual and adaptive
matching regret are separate obligations. -/
namespace CIGAMF.P13.D6BlindActualPrimal
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationMargin
open CIGAMF.P13.D6BlindActualMoments CIGAMF.P13.D6BlindPrimalCertificate
open CIGAMF.P13.D6BlindSaddleCertificate
noncomputable section

def queries (q : ℕ) (j : I (2*q+1)) : Finset (Measurement (2*q+1)) :=
  ((univ.erase j).image Sum.inl) ∪ ((univ.erase j).powersetCard q).image (fun G => .inr (G,false))

def weights (q : ℕ) (j : I (2*q+1)) (w : ℝ) (e : Measurement (2*q+1)) : ℝ :=
  (∑ i ∈ univ.erase j,if e = .inl i then (1-w)/(2*q+1) else 0)+
    ∑ G ∈ (univ.erase j).powersetCard q,if e = .inr (G,false) then
      w/((univ.erase j).powersetCard q).card else 0

theorem weighted_sum (q : ℕ) (j : I (2*q+1)) (w : ℝ) (f : Measurement (2*q+1) → ℝ) :
    (∑ e ∈ queries q j,weights q j w e*f e)=
      (1-w)/(2*q+1)*(∑ i ∈ univ.erase j,f (.inl i))+
      w/((univ.erase j).powersetCard q).card*(∑ G ∈ (univ.erase j).powersetCard q,f (.inr (G,false))) := by
  have hi : ∀ i ∈ univ.erase j,(.inl i : Measurement (2*q+1)) ∈ queries q j := by
    intro i hi
    exact mem_union_left _ (mem_image_of_mem _ hi)
  have hg : ∀ G ∈ (univ.erase j).powersetCard q,(.inr (G,false) : Measurement (2*q+1)) ∈ queries q j := by
    intro G hG
    exact mem_union_right _ (mem_image_of_mem _ hG)
  unfold weights
  simp only [add_mul,sum_add_distrib,sum_mul]
  rw [sum_comm, sum_comm (s := queries q j)]
  congr 1
  · rw [mul_sum]
    apply sum_congr rfl; intro i him
    simp [ite_mul,hi i him]
  · rw [mul_sum]
    apply sum_congr rfl; intro G hG
    simp [ite_mul,hg G hG]

theorem distribution (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1)) (w : ℝ)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (∀ e ∈ queries q j,Legal j q e) ∧ (∀ e,0 ≤ weights q j w e) ∧
      (∑ e ∈ queries q j,weights q j w e)=1 := by
  have hU : (univ.erase j).card=2*q+1 := by simp [I]
  have hK : (0:ℝ) < ((univ.erase j).powersetCard q).card := by
    exact_mod_cast card_pos.mpr (powersetCard_nonempty.mpr (by rw [hU]; omega))
  have hn : 0 < 2*(q:ℝ)+1 := by positivity
  refine ⟨?_,?_,?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp he
      trivial
    · obtain ⟨G,hG,rfl⟩ := mem_image.mp he
      exact qoff_legal q hq j G hG
  · intro e
    unfold weights
    apply add_nonneg
    · apply sum_nonneg; intro i hi
      split <;> first | exact div_nonneg (by linarith) hn.le | exact le_rfl
    · apply sum_nonneg; intro G hG
      split <;> first | exact div_nonneg hw hK.le | exact le_rfl
  · have hh := weighted_sum q j w (fun _ => 1)
    simp only [mul_one,sum_const,nsmul_eq_mul,mul_one,hU] at hh
    rw [hh]
    push_cast
    field_simp
    <;> ring

theorem actual_information (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1))
    (A A' : Finset (I (2*q+1))) (hj : j ∉ A) (hj' : j ∉ A')
    (hc : A'.card=A.card) (hB : (others A j).card=q) (mu z w : ℝ) :
    (∑ e ∈ queries q j,weights q j w e*information A A' j mu (mu+z) e)=
      V q w*z^2/2+(A \ A').card*B q mu w*z+(A \ A').card*C q mu w := by
  rw [weighted_sum]
  have hs := actual_scalar_average A A' j q mu z hj hj' hc (by exact_mod_cast hB)
  have hg := actual_qoff_average q hq j A A' hj hj' hc hB mu z
  change (1-w)/(2*(q:ℝ)+1)*(∑ i ∈ univ.erase j,scalarKL A A' j i mu (mu+z))+
      w/((univ.erase j).powersetCard q).card*(∑ G ∈ (univ.erase j).powersetCard q,queryKL A A' G j false mu (mu+z))=_
  unfold UniformSubsetMoments.avg at hg
  have he : (1-w)/(2*(q:ℝ)+1)*(∑ i ∈ univ.erase j,scalarKL A A' j i mu (mu+z))+
      w/((univ.erase j).powersetCard q).card*(∑ G ∈ (univ.erase j).powersetCard q,queryKL A A' G j false mu (mu+z))=
      (1-w)*((∑ i ∈ univ.erase j,scalarKL A A' j i mu (mu+z))/(2*(q:ℝ)+1))+
      w*((∑ G ∈ (univ.erase j).powersetCard q,queryKL A A' G j false mu (mu+z))/((univ.erase j).powersetCard q).card) := by ring
  rw [he]
  push_cast at hs
  rw [hs,hg]
  unfold V B C v0 top kap
  ring

/-- One A-independent actual-query distribution works for every world in the
family and every same-size alternative, at every nuisance margin. -/
theorem family_primal (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1)) (mu : ℝ)
    (hm : 0 < mu) (hm1 : mu < 1) (hhigh : (q+1)*(1-mu)^2 < 2*mu^2) :
    ∃ a w : ℝ,0 < a ∧ a < mu/q ∧ 0 < w ∧ w < 1 ∧
      (∀ e ∈ queries q j,Legal j q e) ∧ (∀ e,0 ≤ weights q j w e) ∧
      (∑ e ∈ queries q j,weights q j w e)=1 ∧
      (∀ A A' : Finset (I (2*q+1)),j ∉ A → j ∉ A' → A'.card=A.card →
        (others A j).card=q → A' ≠ A → ∀ nu : ℝ,
        scalar q mu a ≤ ∑ e ∈ queries q j,weights q j w e*information A A' j mu nu e) := by
  have hqr : (3:ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨a,w,ha,haq,hw,hw1,_,_,_,hbound,_⟩ := constructed_primal q mu hqr hm hm1 hhigh
  have hd := distribution q hq j w hw.le hw1.le
  refine ⟨a,w,ha,haq,hw,hw1,hd.1,hd.2.1,hd.2.2,?_⟩
  intro A A' hj hj' hc hB hne nu
  have hdistance := CIGAMF.P13.D6AllocationSharp.alternative_distance_bounds A A' j q hj' hc hne (by exact_mod_cast hB)
  have hh := actual_information q hq j A A' hj hj' hc hB mu (nu-mu) w
  rw [show mu+(nu-mu)=nu by ring] at hh
  rw [hh]
  exact hbound _ _ hdistance.1 hdistance.2

#print axioms weighted_sum
#print axioms distribution
#print axioms actual_information
#print axioms family_primal
end
end CIGAMF.P13.D6BlindActualPrimal
