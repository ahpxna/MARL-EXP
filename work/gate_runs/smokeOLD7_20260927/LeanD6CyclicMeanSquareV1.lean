import «LeanD6CyclicPhaseLawV1»

/-! Squared-error control for the actual A-free cyclic estimator, including
projection onto a known interval. No correctness event for discovery is
assumed in the estimator law. -/
namespace CIGAMF.P13.D6CyclicMeanSquare
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6CyclicPhaseLaw
noncomputable section

/-- Projection cannot increase distance to a point in the interval. -/
def clip (lo hi x : ℝ) : ℝ := max lo (min hi x)

theorem clip_mem (lo hi x : ℝ) (h : lo ≤ hi) :
    lo ≤ clip lo hi x ∧ clip lo hi x ≤ hi := by
  unfold clip
  exact ⟨le_max_left _ _,max_le h (min_le_left _ _)⟩

theorem clip_error (lo hi mu x : ℝ) (hl : lo ≤ mu) (hu : mu ≤ hi) :
    |clip lo hi x-mu| ≤ |x-mu| := by
  unfold clip
  rcases le_total x lo with h | h
  · rw [min_eq_right (h.trans (hl.trans hu)),max_eq_left h]
    rw [abs_of_nonpos (by linarith),abs_of_nonpos (by linarith)]
    linarith
  · rcases le_total hi x with hh | hh
    · rw [min_eq_left hh,max_eq_right (hl.trans hu)]
      rw [abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
      linarith
    · rw [min_eq_right hh,max_eq_right h]

lemma gaussian_mean_square {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {mu : ℝ} {v : NNReal} (h : HasLaw X (gaussianReal mu v) P) :
    (∫⁻ x,ENNReal.ofReal ((X x-mu)^2) ∂P)=ENNReal.ofReal (v:ℝ) := by
  rw [h.lintegral_comp (show AEMeasurable (fun y : ℝ => ENNReal.ofReal ((y-mu)^2)) (gaussianReal mu v) by fun_prop)]
  have he := evariance_eq_lintegral_ofReal (fun y : ℝ => y) (gaussianReal mu v)
  simp only [integral_id_gaussianReal] at he
  rw [← he]
  have hmem : MemLp (fun y : ℝ => y) 2 (gaussianReal mu v) :=
    IsGaussian.memLp_two_id (μ:=gaussianReal mu v)
  have hv := ofReal_variance hmem
  rw [variance_fun_id_gaussianReal] at hv
  exact hv.symm

theorem clipped_mean_square {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {mu lo hi : ℝ} {v : NNReal}
    (h : HasLaw X (gaussianReal mu v) P) (hl : lo ≤ mu) (hu : mu ≤ hi) :
    (∫⁻ x,ENNReal.ofReal ((clip lo hi (X x)-mu)^2) ∂P) ≤ ENNReal.ofReal (v:ℝ) := by
  rw [← gaussian_mean_square h]
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  have he := clip_error lo hi mu (X x) hl hu
  have hs := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr he
  simpa only [sq_abs] using hs

/-- Actual cyclic query observations give the finite-sample bound
|C|/(L*q^4). The mean-sum premise is discharged by actual_mean_sum for the
concrete cyclic design, as in actual_design_law_exists. -/
theorem cyclic_clipped_mean_square {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (G : C → Finset (I n)) (A : Finset (I n)) (j : I n)
    (q L : ℕ) (hq : 0 < q) (hL : 0 < L) (mu lo hi : ℝ)
    (hm : (∑ t, D6GaussianQueryDominance.actualMean A j mu (.inr (G t,false)))=
      Fintype.card C+(q:ℝ)^2*(1-mu)) (hl : lo ≤ mu) (hu : mu ≤ hi) :
    (∫⁻ x,ENNReal.ofReal ((clip lo hi (estimate (C:=C) q L x)-mu)^2)
      ∂observations G A j mu L) ≤ ENNReal.ofReal ((Fintype.card C:ℝ)/((L:ℝ)*(q:ℝ)^4)) := by
  have hh := clipped_mean_square (estimate_law G A j q L hq hL mu hm) hl hu
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hL0 : (L:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
  convert hh using 1
  congr 1
  push_cast
  field_simp
  <;> ring

#print axioms clip_error
#print axioms gaussian_mean_square
#print axioms clipped_mean_square
#print axioms cyclic_clipped_mean_square
end
end CIGAMF.P13.D6CyclicMeanSquare
