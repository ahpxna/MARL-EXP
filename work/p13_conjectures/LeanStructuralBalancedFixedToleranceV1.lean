import «LeanStructuralToleranceBudgetNetV1»

/-! Dimension-independent fixed-tolerance upper bound for balanced component
radii. The balance hypothesis is substantive; total normalization alone does
not imply it. No claim that this general Lipschitz argument is novel is made. -/
namespace CIGAMF.P13.StructuralBalancedFixedTolerance
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralToleranceBudgetNet
noncomputable section
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]

theorem balanced_fixed_tolerance (f : I → Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (K : ℕ) (hK : 0 < K) (hKm : K ≤ Fintype.card I)
    (hc : ∀ i, osc (f i)/2 ≤ C/Fintype.card I) :
    PrefixCoverDimensionAtMost (selectedRadius f) (2*C/K) (2*K) := by
  let m := Fintype.card I
  let h := m/K
  have hh : 0 < h := Nat.div_pos hKm hK
  have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m from lt_of_lt_of_le hK hKm)
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hprod : (h:ℝ)*K ≤ m := by exact_mod_cast (Nat.div_mul_le_self m K)
  have hmupper : m < (h+1)*K :=
    (Nat.div_lt_iff_lt_mul hK).mp (by dsimp [h];omega)
  have hscale : (h+1)*K ≤ (2*K)*h := by nlinarith
  have hcount : m/h+1 ≤ 2*K := by
    have hd : m/h < 2*K := (Nat.div_lt_iff_lt_mul hh).mpr (hmupper.trans_le hscale)
    omega
  have heps : 2*(C/(m:ℝ))*h ≤ 2*C/K := by
    have he : 2*(C/(m:ℝ))*h = (2*C*h)/m := by ring
    rw [he]
    apply (div_le_div_iff₀ hmpos hKpos).mpr
    nlinarith [mul_nonneg (show 0 ≤ 2*C by positivity) (sub_nonneg.mpr hprod)]
  obtain ⟨menu,hcard,hcover⟩ := budget_net_cover f (C/m) (by positivity) hc h hh
  refine ⟨menu,hcard.trans hcount,hcover.1,hcover.2.1,?_⟩
  intro k hk
  obtain ⟨r,hr,ho⟩ := hcover.2.2 k hk
  refine ⟨r,hr,ho.1,?_⟩
  intro T hT
  have ht := ho.2 T hT
  linarith

#print axioms balanced_fixed_tolerance
end
end CIGAMF.P13.StructuralBalancedFixedTolerance
