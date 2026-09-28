import «LeanD6AllocationDualBridgeV1»
import «LeanD6GeometricRealizationV1»

/-! The sharp actual-query allocation certificate. The true margin is 1/2;
all alternative margins are in [0,1]. Unit Gaussian variance and unit query
cost are represented by squared mean difference / 2. The library consists of
all scalar Q_i and both joint query types with |G|<=q=k-1. This is an oracle
information-allocation theorem, not a sequential stopping-time theorem. -/
namespace CIGAMF.P13.D6AllocationSharp
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationPrimalBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6ExpandedAllocation
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

theorem alternative_distance_bounds (A A' : Finset (I n)) (j : I n) (q : ℝ)
    (hj' : j ∉ A') (hcard : A'.card=A.card) (hne : A' ≠ A)
    (hB : ((others A j).card : ℝ)=q) :
    1 ≤ ((A \ A').card : ℝ) ∧ ((A \ A').card : ℝ) ≤ q := by
  have hnot : ¬A ⊆ A' := by
    intro hs
    exact hne (eq_of_subset_of_card_le hs hcard.le).symm
  have hpos : 0 < (A \ A').card := card_pos.mpr (sdiff_nonempty.mpr hnot)
  have hs : A' \ A ⊆ others A j := by
    intro i hi
    have hij : i ≠ j := by intro he; subst i; exact hj' (mem_sdiff.mp hi).1
    simp [others, hij, (mem_sdiff.mp hi).2]
  have hds := card_sdiff_comm hcard
  have hle : (A \ A').card ≤ (others A j).card := by rw [← hds]; exact card_le_card hs
  refine ⟨by exact_mod_cast hpos, ?_⟩
  rw [← hB]
  exact_mod_cast hle

/-- The stated primal really is a probability allocation on legal queries. -/
theorem primal_feasible (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    0 ≤ weight q (scale q) ∧ 0 ≤ (1-weight q (scale q))/(q+1) ∧
    (∑ _a ∈ A, (1-weight q (scale q))/(q+1))+weight q (scale q)=1 ∧
    Legal j q (.inr (others A j,true)) ∧
    (∀ a ∈ A, Legal j q (.inr (A.erase a,false))) := by
  have hc := scale_properties q hq
  have hw := parameters q _ hq hc.1 hc.2.1
  have hk : 0 < q+1 := by linarith
  refine ⟨hw.1.le, div_nonneg (by linarith [hw.2.1]) hk.le, ?_, ?_, ?_⟩
  · simp only [sum_const, nsmul_eq_mul, hA]
    field_simp [ne_of_gt hk]
    ring
  · exact ⟨by simp [others], hB.le, by simp⟩
  · intro a ha
    have hAn : 4 ≤ A.card := by exact_mod_cast (show (4:ℝ) ≤ A.card by linarith)
    have hl := erased_query_legal A j a hj ha hAn
    have he : ((A.erase a).card : ℝ)+1=A.card := by exact_mod_cast card_erase_add_one ha
    exact ⟨hl.1, by linarith, by intro _; exact hl.2⟩

/-- Actual primal guarantee for EVERY distinct legal hidden set and margin;
the distance bounds are consequences, no longer extra assumptions. -/
theorem every_alternative_primal_lower (A A' : Finset (I n)) (j : I n) (q nu : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card) (hne : A' ≠ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    value q (scale q)/8 ≤ actualPrimal A A' j q (scale q) (2*(1-nu)) := by
  have hd := alternative_distance_bounds A A' j q hj' hcard hne hB
  exact actual_primal_lower A A' j q _ hq hj hj' hcard hA hB hd.1 hd.2

/-- Matching lower and upper certificates on actual observations. The lower
holds simultaneously for all alternatives; the upper applies to any legal
query allocation and produces one actual adversarial alternative. -/
theorem sharp_actual_allocation (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    (∀ A' : Finset (I n), j ∉ A' → A'.card=A.card → A' ≠ A → ∀ nu : ℝ,
      value q (scale q)/8 ≤ actualPrimal A A' j q (scale q) (2*(1-nu))) ∧
    (∀ (E : Finset (Measurement n)) (w : Measurement n → ℝ),
      (∀ e ∈ E, Legal j q e) → (∀ e ∈ E, 0 ≤ w e) → (∑ e ∈ E, w e=1) →
      ∃ A' : Finset (I n), ∃ nu : ℝ,
        A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
        (∑ e ∈ E, w e*information A A' j (1/2) nu e) ≤ value q (scale q)/8) := by
  constructor
  · intro A' hj' hcard hne nu
    exact every_alternative_primal_lower A A' j q nu hq hj hj' hcard hne hA hB
  · intro E w hl hw hn
    exact arbitrary_allocation_upper A j q hq hj hA hB E w hl hw hn

/-- Natural-width specialization: every member of the explicit D6 family
has the sharp actual allocation value, for every m=2(r+1)>=8. -/
theorem all_width_sharp (r : ℕ) (j : I (2*r+1)) (hr : 3 ≤ r)
    (A : Finset (I (2*r+1))) (hmem : A ∈ worlds r j) :
    (∀ A' : Finset (I (2*r+1)), j ∉ A' → A'.card=A.card → A' ≠ A → ∀ nu : ℝ,
      value r (scale r)/8 ≤ actualPrimal A A' j r (scale r) (2*(1-nu))) ∧
    (∀ (E : Finset (Measurement (2*r+1))) (w : Measurement (2*r+1) → ℝ),
      (∀ e ∈ E, Legal j r e) → (∀ e ∈ E, 0 ≤ w e) → (∑ e ∈ E, w e=1) →
      ∃ A' : Finset (I (2*r+1)), ∃ nu : ℝ,
        A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
        (∑ e ∈ E, w e*information A A' j (1/2) nu e) ≤ value r (scale r)/8) := by
  have hp := world_parameters r j (by omega) hmem
  have hA : (A.card : ℝ)=(r:ℝ)+1 := by exact_mod_cast hp.2.1
  have hb : (others A j).card=r := by
    have hjc : j ∈ Aᶜ := by simpa using hp.1
    have he : (others A j).card+1=Aᶜ.card := by
      unfold others
      rw [← compl_eq_univ_sdiff A]
      exact card_erase_add_one hjc
    rw [hp.2.2.1, hp.2.1] at he
    omega
  exact sharp_actual_allocation A j r (by exact_mod_cast hr) hp.1 hA (by exact_mod_cast hb)

#print axioms alternative_distance_bounds
#print axioms primal_feasible
#print axioms every_alternative_primal_lower
#print axioms sharp_actual_allocation
#print axioms all_width_sharp

/-- The identified label controls the actual support-geometry decision:
using A's optimum on a distinct alternative A' incurs positive real radius
regret. Thus the allocation game is about genuine geometric answers. -/
theorem geometric_wrong_optimum_regret (r : ℕ) (j : I (2*r+1)) (hr : 3 ≤ r)
    (A A' : Finset (I (2*r+1))) (hA : A ∈ worlds r j) (hA' : A' ∈ worlds r j)
    (hne : A' ≠ A) (nu : ℝ) (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) :
    0 < CIGAMF.V4.SupportGeometry.selectedRadius
      (CIGAMF.P13.D6Geometry.restrictedProjection (world A' j nu) (productResponse corner (world A' j nu)))
      (liftedSelection Aᶜ) - CIGAMF.V4.SupportGeometry.selectedRadius
      (CIGAMF.P13.D6Geometry.restrictedProjection (world A' j nu) (productResponse corner (world A' j nu)))
      (liftedSelection A'ᶜ) := by
  have hp := world_parameters r j (by omega) hA
  have hp' := world_parameters r j (by omega) hA'
  have hcard : A'.card=A.card := hp'.2.1.trans hp.2.1.symm
  rw [CIGAMF.P13.D6Geometry.actual_geometric_radius,
      CIGAMF.P13.D6Geometry.actual_geometric_radius,
      actual_regret A' Aᶜ j hp'.1 nu hnu hnu1 (hp.2.2.1.trans hcard.symm) hp'.2.2.1 hp'.2.2.2]
  have he : Aᶜ ∩ A'=A' \ A := by ext i; simp [and_comm]
  rw [he]
  have hn : ¬A' ⊆ A := by
    intro hs
    exact hne (eq_of_subset_of_card_le hs hcard.symm.le)
  have hd : 0 < ((A' \ A).card : ℝ) := by exact_mod_cast card_pos.mpr (sdiff_nonempty.mpr hn)
  exact div_pos (mul_pos (by linarith) hd) (by norm_num)

#print axioms geometric_wrong_optimum_regret

/-- End-to-end dual witness: one admissible real support geometry has a
strictly different optimum yet remains hard for the entire query allocation. -/
theorem all_width_geometric_upper (r : ℕ) (j : I (2*r+1)) (hr : 3 ≤ r)
    (A : Finset (I (2*r+1))) (hmem : A ∈ worlds r j)
    (E : Finset (Measurement (2*r+1))) (w : Measurement (2*r+1) → ℝ)
    (hlegal : ∀ e ∈ E, Legal j r e) (hw : ∀ e ∈ E, 0 ≤ w e) (hnorm : ∑ e ∈ E, w e=1) :
    ∃ A' ∈ worlds r j, ∃ nu : ℝ, 0 ≤ nu ∧ nu ≤ 1 ∧
      (∑ e ∈ E, w e*information A A' j (1/2) nu e) ≤ value r (scale r)/8 ∧
      0 < CIGAMF.V4.SupportGeometry.selectedRadius
        (CIGAMF.P13.D6Geometry.restrictedProjection (world A' j nu) (productResponse corner (world A' j nu)))
        (liftedSelection Aᶜ) - CIGAMF.V4.SupportGeometry.selectedRadius
        (CIGAMF.P13.D6Geometry.restrictedProjection (world A' j nu) (productResponse corner (world A' j nu)))
        (liftedSelection A'ᶜ) := by
  obtain ⟨A',nu,hne,hcard,hj',hnu,hnu1,hinfo⟩ :=
    (all_width_sharp r j hr A hmem).2 E w hlegal hw hnorm
  have hp := world_parameters r j (by omega) hmem
  have hmem' : A' ∈ worlds r j := by
    apply mem_powersetCard.mpr
    refine ⟨?_,hcard.trans hp.2.1⟩
    intro i hi
    have hij : i ≠ j := by intro he; subst i; exact hj' hi
    simp [positiveGround, hij]
  exact ⟨A',hmem',nu,hnu,hnu1,hinfo,
    geometric_wrong_optimum_regret r j hr A A' hmem hmem' hne nu hnu hnu1⟩

#print axioms all_width_geometric_upper
end
end CIGAMF.P13.D6AllocationSharp
