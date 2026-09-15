import «LeanStructuralRadiusReindexV1»
import «LeanStructuralStaircaseToleranceLowerV1»

/-! The normalized fixed-tolerance law: universal O(1/epsilon) without
component balance, and a staircase family with Omega(1/epsilon) obstruction. -/
namespace CIGAMF.P13.StructuralNormalizedToleranceLaw
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension CIGAMF.P13.StructuralRadiusReindex
open CIGAMF.P13.StructuralStaircaseFamily CIGAMF.P13.StructuralStaircaseToleranceLower
noncomputable section
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [Nonempty Ω]

theorem normalized_upper (f : I → Ω → ℝ) (B : ℝ)
    (hB : B=∑ i,osc (f i)/2) (hpos : 0 < B) (eps : ℝ) (heps : 0 < eps) :
    PrefixCoverDimensionAtMost (fun S => selectedRadius f S/B) eps (⌊2/eps⌋₊+1) := by
  have hh := intrinsic_upper f (B*eps) (mul_pos hpos heps)
  rw [← hB] at hh
  have he : 2*B/(B*eps)=2/eps := by field_simp
  rw [he] at hh
  obtain ⟨menu,hcard,hne,hfull,hcover⟩ := hh
  refine ⟨menu,hcard,hne,hfull,?_⟩
  intro k hk
  obtain ⟨r,hr,ho⟩ := hcover k hk
  refine ⟨r,hr,ho.1,?_⟩
  intro T hT
  have hv := (div_le_div_of_nonneg_right (ho.2 T hT) hpos.le)
  have he' : (selectedRadius f T+B*eps)/B=selectedRadius f T/B+eps := by field_simp
  rwa [he'] at hv

/-- For every 0<epsilon<=1/4, the normalized staircase with
r=floor(1/(4epsilon)) needs at least r rankings. The family changes with epsilon;
this does not claim an unbounded dimension at a single normalized tolerance. -/
theorem normalized_lower (eps : ℝ) (heps : 0 < eps) (heps' : eps ≤ 1/4) :
    let r := ⌊1/(4*eps)⌋₊
    0 < r ∧ ¬ PrefixCoverDimensionAtMost
      (fun S : Finset (StairRel r) => selectedRadius staircaseF S/(r:ℝ)) eps (r-1) := by
  let r := ⌊1/(4*eps)⌋₊
  have h4 : 0 < 4*eps := by positivity
  have hone : 1 ≤ 1/(4*eps) := (le_div_iff₀ h4).mpr (by linarith)
  have hr : 0 < r := Nat.floor_pos.mpr hone
  refine ⟨hr,normalized_tolerance_lower hr eps ?_⟩
  have hf : (r:ℝ) ≤ 1/(4*eps) := Nat.floor_le (by positivity)
  have hm := (le_div_iff₀ h4).mp hf
  nlinarith

#print axioms normalized_upper
#print axioms normalized_lower
end
end CIGAMF.P13.StructuralNormalizedToleranceLaw
