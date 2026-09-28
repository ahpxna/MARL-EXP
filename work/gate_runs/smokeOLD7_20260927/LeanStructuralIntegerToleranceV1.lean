import «LeanStructuralScalarChi5GeometryKernelV1»

/-! Quantized objectives retain their exact optimal prefixes below one grid
unit. Applied to the actual scalar witness after total-radius normalization. -/
namespace CIGAMF.P13.StructuralIntegerTolerance
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralScalarChi5Witness
open CIGAMF.P13.StructuralScalarChi5GeometryKernel
open CIGAMF.V4.SupportGeometry
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem epsilonOptimal_on_grid (cost : Finset I → ℕ) (scale eps : ℝ)
    (hscale : 0 < scale) (heps : scale * eps < 1)
    (k : ℕ) (S : Finset I)
    (h : EpsilonOptimalAt (fun T => (cost T:ℝ)/scale) eps k S) :
    EpsilonOptimalAt (fun T => (cost T:ℝ)/scale) 0 k S := by
  refine ⟨h.1, ?_⟩
  intro T hT
  have hb := h.2 T hT
  have hb' : (cost S:ℝ) ≤ (cost T:ℝ) + scale*eps := by
    have hh := (div_le_iff₀ hscale).mp hb
    field_simp at hh
    nlinarith [hh]
  have hlt : (cost S:ℝ) < (cost T:ℝ) + 1 := by linarith
  have hnat : cost S < cost T + 1 := by exact_mod_cast hlt
  have hle : (cost S:ℝ) ≤ cost T := by exact_mod_cast (Nat.lt_succ_iff.mp hnat)
  simpa using div_le_div_of_nonneg_right hle hscale.le

noncomputable def normalizedScalarObjective (S : Finset (Fin 7)) : ℝ :=
  selectedRadius scalarF7 S / 57

theorem normalized_formula (S : Finset (Fin 7)) :
    normalizedScalarObjective S = (complementAbs7 S:ℝ)/114 := by
  rw [normalizedScalarObjective,scalar_selectedRadius_formula]
  ring

/-- Five rankings remain necessary throughout 0 <= epsilon < 1/114 under
normalization sum_j osc(f_j)/2 = 1 (divide the original functions by 57). -/
theorem normalized_chi_at_least_five (eps : ℝ) (heps : eps < 1/114) :
    ¬ PrefixCoverDimensionAtMost normalizedScalarObjective eps 4 := by
  rintro ⟨menu,hcard,hcover⟩
  apply CIGAMF.P13.StructuralScalarChi5GeometryKernel.STRUCT_SCALAR_CHI5_prefix_cover_not_at_most_four
  refine ⟨menu,hcard,hcover.1,hcover.2.1,?_⟩
  intro k hk
  obtain ⟨r,hr,ho⟩ := hcover.2.2 k hk
  have ho' : EpsilonOptimalAt (fun S => (complementAbs7 S:ℝ)/114) eps k
      (CIGAMF.V4.StructuralRankability.prefixSet r k) := by
    simpa only [EpsilonOptimalAt,normalized_formula] using ho
  have hz := epsilonOptimal_on_grid complementAbs7 114 eps (by norm_num)
    (by linarith) k _ ho'
  refine ⟨r,hr,hz.1,?_⟩
  intro T hT
  have hh := hz.2 T hT
  rw [scalar_selectedRadius_formula,scalar_selectedRadius_formula]
  linarith

#print axioms epsilonOptimal_on_grid
#print axioms normalized_formula
#print axioms normalized_chi_at_least_five
end CIGAMF.P13.StructuralIntegerTolerance
