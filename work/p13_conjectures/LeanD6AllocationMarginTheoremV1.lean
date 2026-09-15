import «LeanD6AllocationMarginSharpV1»
import «LeanD6AllocationMarginRegionV1»
import «LeanD6UniqueOptimumV1»

/-! End-to-end theorem for every explicit D6 width m=2(r+1)>=8.
A single allocation for a fixed world label A is optimal at every true margin
in the stated interval. It is an oracle information design: A is an argument
of the design, and no sequential learning or stopping theorem is asserted.
All means come from the constructed worlds; geometry uses the literal support
and the original cardinality-feasible lifted selections. -/
namespace CIGAMF.P13.D6AllocationMarginTheorem
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6Geometry
open CIGAMF.P13.D6ExpandedAllocation CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationSharp CIGAMF.P13.D6AllocationDistribution
open CIGAMF.P13.D6AllocationMargin CIGAMF.P13.D6AllocationMarginSharp
open CIGAMF.P13.D6AllocationMarginRegion CIGAMF.P13.D6UniqueOptimum
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
noncomputable section

private theorem width_counts (r : ℕ) (j : I (2*r+1)) (hr : 3 ≤ r)
    (A : Finset (I (2*r+1))) (hmem : A ∈ worlds r j) :
    j ∉ A ∧ (A.card : ℝ)=(r:ℝ)+1 ∧ ((others A j).card : ℝ)=(r:ℝ) := by
  have hp := world_parameters r j (by omega) hmem
  have hb : (others A j).card=r := by
    have hjc : j ∈ Aᶜ := by simpa using hp.1
    have he : (others A j).card+1=Aᶜ.card := by
      unfold others
      rw [← compl_eq_univ_sdiff A]
      exact card_erase_add_one hjc
    rw [hp.2.2.1,hp.2.1] at he
    omega
  exact ⟨hp.1,by exact_mod_cast hp.2.1,by exact_mod_cast hb⟩

private theorem alternative_mem (r : ℕ) (j : I (2*r+1)) (hr : 3 ≤ r)
    (A A' : Finset (I (2*r+1))) (hmem : A ∈ worlds r j)
    (hj' : j ∉ A') (hcard : A'.card=A.card) : A' ∈ worlds r j := by
  have hp := world_parameters r j (by omega) hmem
  apply mem_powersetCard.mpr
  refine ⟨?_,hcard.trans hp.2.1⟩
  intro i hi
  have hij : i ≠ j := by intro he; subst i; exact hj' hi
  simp [positiveGround,hij]

/-- The displayed closed form is the actual information-game value. -/
theorem rate_closed_form (q mu : ℝ) (hq : 3 ≤ q) :
    rate q (1-mu) =
      (1-mu)^2*(scale q)^2*(q-1)^2/(2*(q-2+scale q)^2) := by
  have hc := scale_properties q hq
  have hd : q-2+scale q ≠ 0 := by linarith [hc.1]
  unfold rate value
  field_simp [hd] <;> ring

/-- A fixed explicit probability vector works throughout the entire true-margin
interval. Its worst actual alternative attains the bound at every margin. -/
theorem all_width_uniform_interval_design (r : ℕ) (j : I (2*r+1)) (hr : 3 ≤ r)
    (A : Finset (I (2*r+1))) (hmem : A ∈ worlds r j) :
    (∀ e ∈ primalQueries A j, Legal j r e) ∧
    (∀ e ∈ primalQueries A j, 0 ≤ primalWeight A j r e) ∧
    (∑ e ∈ primalQueries A j, primalWeight A j r e)=1 ∧
    (∀ mu : ℝ, marginMin r ≤ mu → mu ≤ marginMax r →
      (∀ A' ∈ worlds r j, A' ≠ A → ∀ nu : ℝ, 0 ≤ nu → nu ≤ 1 →
        rate r (1-mu) ≤ ∑ e ∈ primalQueries A j,
          primalWeight A j r e*information A A' j mu nu e) ∧
      (∃ A' ∈ worlds r j, ∃ nu : ℝ, A' ≠ A ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
        (∑ e ∈ primalQueries A j, primalWeight A j r e*information A A' j mu nu e)=
          rate r (1-mu))) := by
  have hq : (3:ℝ) ≤ r := by exact_mod_cast hr
  have hp := width_counts r j hr A hmem
  have hp0 := world_parameters r j (by omega) hmem
  have hd := primal_distribution A j r hq hp.1 hp.2.1 hp.2.2
  refine ⟨hd.1,(fun e _ => hd.2.1 e),hd.2.2,?_⟩
  intro mu hlo hhi
  have hI := (interior_iff_margin r mu hq).mpr ⟨hlo,hhi⟩
  constructor
  · intro A' hm' hne nu _ _
    have hp' := world_parameters r j (by omega) hm'
    have he := margin_distribution_lower A A' j r (1-mu) nu hq hI.1 hp.1 hp'.1
      (hp'.2.1.trans hp0.2.1.symm) hne hp.2.1 hp.2.2
    simpa only [sub_sub_cancel] using he
  · obtain ⟨A',nu,hne,hcard,hj',hnu,hnu1,he⟩ :=
      margin_value_attained A j r (1-mu) hq hI hp.1 hp.2.1 hp.2.2
    exact ⟨A',alternative_mem r j hr A A' hmem hj' hcard,nu,hne,hnu,hnu1,
      by simpa only [sub_sub_cancel] using he⟩

/-- Every competing query distribution admits one real alternative world with
small information, a unique different geometric answer, and positive regret
for the original answer. The alternative is chosen after the whole allocation. -/
theorem all_width_interval_geometric_upper (r : ℕ) (j : I (2*r+1)) (hr : 3 ≤ r)
    (A : Finset (I (2*r+1))) (hmem : A ∈ worlds r j)
    (mu : ℝ) (hlo : marginMin r ≤ mu) (hhi : mu ≤ marginMax r)
    (E : Finset (Measurement (2*r+1))) (w : Measurement (2*r+1) → ℝ)
    (hlegal : ∀ e ∈ E, Legal j r e) (hw : ∀ e ∈ E, 0 ≤ w e) (hnorm : ∑ e ∈ E, w e=1) :
    ∃ A' ∈ worlds r j, ∃ nu : ℝ, A' ≠ A ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
      (∑ e ∈ E, w e*information A A' j mu nu e) ≤ rate r (1-mu) ∧
      (∀ S ∈ actions r,
        (∀ T ∈ actions r,
          selectedRadius (restrictedProjection (world A' j nu) (productResponse corner (world A' j nu)))
            (liftedSelection S) ≤
          selectedRadius (restrictedProjection (world A' j nu) (productResponse corner (world A' j nu)))
            (liftedSelection T)) ↔ S=A'ᶜ) ∧
      0 < selectedRadius (restrictedProjection (world A' j nu) (productResponse corner (world A' j nu)))
        (liftedSelection Aᶜ) -
      selectedRadius (restrictedProjection (world A' j nu) (productResponse corner (world A' j nu)))
        (liftedSelection A'ᶜ) := by
  have hq : (3:ℝ) ≤ r := by exact_mod_cast hr
  have hp := width_counts r j hr A hmem
  have hI := (interior_iff_margin r mu hq).mpr ⟨hlo,hhi⟩
  obtain ⟨A',nu,hne,hcard,hj',hnu,hnu1,he⟩ :=
    arbitrary_margin_allocation_upper A j r (1-mu) hq hI hp.1 hp.2.1 hp.2.2 E w hlegal hw hnorm
  have hm' := alternative_mem r j hr A A' hmem hj' hcard
  refine ⟨A',hm',nu,hne,hnu,hnu1,by simpa only [sub_sub_cancel] using he,?_,?_⟩
  · intro S hS
    exact all_width_geometric_optimal_iff r j (by omega) A' S hm' hS nu hnu hnu1
  · exact geometric_wrong_optimum_regret r j hr A A' hmem hm' hne nu hnu hnu1

#print axioms rate_closed_form
#print axioms all_width_uniform_interval_design
#print axioms all_width_interval_geometric_upper
end
end CIGAMF.P13.D6AllocationMarginTheorem
