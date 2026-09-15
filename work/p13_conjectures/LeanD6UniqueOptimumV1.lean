import «LeanD6GeometricRealizationV1»

/-! Uniqueness among every original cardinality-feasible selection, not only
among complement labels. In the real support realization, feasibility means
`liftedSelection S`; the interaction coordinate `none` remains omitted. -/
namespace CIGAMF.P13.D6UniqueOptimum
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6Geometry
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

/-- Equality with the complement's actual compression loss forces the whole
selection to equal that complement. -/
theorem actual_loss_eq_iff (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcard : S.card=A.card) (hbal : Aᶜ.card=A.card) (hB : 2 ≤ (others A j).card) :
    productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) S =
      productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) Aᶜ ↔ S=Aᶜ := by
  constructor
  · intro hl
    have hr := actual_regret A S j hj mu hmu hmu1 hcard hbal hB
    rw [hl, sub_self] at hr
    have hp : 0 < 2-mu := by linarith
    have hc : ((S ∩ A).card : ℝ)=0 := by
      have he : (2-mu)*((S ∩ A).card : ℝ)=0 := by linarith [hr]
      exact (mul_eq_zero.mp he).resolve_left (ne_of_gt hp)
    have hempty : S ∩ A=∅ := card_eq_zero.mp (by exact_mod_cast hc)
    have hs : S ⊆ Aᶜ := by
      intro i hi
      apply mem_compl.mpr
      intro hai
      have hm : i ∈ S ∩ A := mem_inter.mpr ⟨hi,hai⟩
      rw [hempty] at hm
      simpa using hm
    exact eq_of_subset_of_card_le hs (hbal.trans hcard.symm).le
  · intro he
    rw [he]

/-- The actual optimization answer region is the singleton {Aᶜ}: every
same-cardinality competing selection is quantified explicitly. -/
theorem actual_optimal_iff (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcard : S.card=A.card) (hbal : Aᶜ.card=A.card) (hB : 2 ≤ (others A j).card) :
    (∀ T : Finset (I n), T.card=A.card →
      productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) S ≤
        productCompressionLoss (world A j mu) (productResponse corner (world A j mu)) T) ↔ S=Aᶜ := by
  constructor
  · intro ho
    apply (actual_loss_eq_iff A S j hj mu hmu hmu1 hcard hbal hB).mp
    exact le_antisymm (ho Aᶜ hbal) (complement_optimal A S j hj mu hmu hmu1 hcard hbal hB)
  · intro he
    subst S
    intro T hT
    exact complement_optimal A T j hj mu hmu hmu1 hT hbal hB

/-- The same uniqueness holds for the literal finite real support and fixed
ambient projections, over all feasible lifted selections. -/
theorem geometric_optimal_iff (A S : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcard : S.card=A.card) (hbal : Aᶜ.card=A.card) (hB : 2 ≤ (others A j).card) :
    (∀ T : Finset (I n), T.card=A.card →
      selectedRadius (restrictedProjection (world A j mu) (productResponse corner (world A j mu)))
        (liftedSelection S) ≤
      selectedRadius (restrictedProjection (world A j mu) (productResponse corner (world A j mu)))
        (liftedSelection T)) ↔ S=Aᶜ := by
  simp_rw [actual_geometric_radius]
  exact actual_optimal_iff A S j hj mu hmu hmu1 hcard hbal hB

/-- Every explicit D6 width m=2(r+1)>=6 has a unique geometric optimum for
every admissible nuisance margin, including both endpoints. -/
theorem all_width_geometric_optimal_iff (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A S : Finset (I (2*r+1))) (hA : A ∈ worlds r j) (hS : S ∈ actions r)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    (∀ T : Finset (I (2*r+1)), T ∈ actions r →
      selectedRadius (restrictedProjection (world A j mu) (productResponse corner (world A j mu)))
        (liftedSelection S) ≤
      selectedRadius (restrictedProjection (world A j mu) (productResponse corner (world A j mu)))
        (liftedSelection T)) ↔ S=Aᶜ := by
  have hp := world_parameters r j hr hA
  have hsCard : S.card=A.card := (mem_powersetCard.mp hS).2.trans hp.2.1.symm
  have hm : ∀ T : Finset (I (2*r+1)), T ∈ actions r ↔ T.card=A.card := by
    intro T
    simp [actions, mem_powersetCard, hp.2.1]
  simp_rw [hm]
  exact geometric_optimal_iff A S j hp.1 mu hmu hmu1 hsCard hp.2.2.1 hp.2.2.2

#print axioms actual_loss_eq_iff
#print axioms actual_optimal_iff
#print axioms geometric_optimal_iff
#print axioms all_width_geometric_optimal_iff
end
end CIGAMF.P13.D6UniqueOptimum
