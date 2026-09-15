import «LeanD6ScaledValueErrorV1»

/-! Uniform finite value error and eventual strong restriction on compact tau
intervals. The boundary-window expansion is a separate, unproved obligation. -/
namespace CIGAMF.P13.D6UniformScaledBounds
open Filter
open scoped Topology
open CIGAMF.P13.D6ScaledReferenceCoefficients CIGAMF.P13.D6ScaledReferencePhase
open CIGAMF.P13.D6ScaledValueError
noncomputable section

lemma constants_mono (tau U : ℝ) (ht : 0 ≤ tau) (htu : tau ≤ U) :
    D tau ≤ D U ∧ Db tau ≤ Db U ∧ Cv tau ≤ Cv U := by
  have hU : 0 ≤ U := ht.trans htu
  have hC : limitC U ≤ limitC tau := Real.exp_le_exp.mpr (by linarith)
  have hCU : 0 < limitC U := Real.exp_pos _
  have hCt : 0 < limitC tau := Real.exp_pos _
  have hD : D tau ≤ D U := by unfold D;gcongr
  have hDb : Db tau ≤ Db U := by unfold Db D;gcongr
  refine ⟨hD,hDb,?_⟩
  unfold Cv Nv Dt Da Db D
  gcongr

/-- One explicit constant and one explicit size threshold work for all
rho in [1,2] and all tau in [0,U]. -/
theorem uniform_finite_value_error (U : ℝ) (hU : 0 ≤ U) (k : ℕ) (hk : 2 ≤ k)
    (hkt : 2*U ≤ (k:ℝ)) (hlarge : 2*D U/(k:ℝ) ≤ limitC U) :
    ∀ tau ∈ Set.Icc 0 U,∀ rho ∈ Set.Icc (1:ℝ) 2,
      |value tau rho k/(k:ℝ)-limitValue tau rho| ≤ Cv U/(k:ℝ) := by
  intro tau ht rho hr
  have hm := constants_mono tau U ht.1 ht.2
  have hC : limitC U ≤ limitC tau := Real.exp_le_exp.mpr (by linarith [ht.2])
  have hs : 2*D tau/(k:ℝ) ≤ limitC tau := by
    calc
      _ ≤ 2*D U/(k:ℝ) := by gcongr;exact hm.1
      _ ≤ limitC U := hlarge
      _ ≤ limitC tau := hC
  exact (finite_value_error tau rho ht.1 hr.1 hr.2 k hk (by linarith [ht.2]) hs).trans
    (div_le_div_of_nonneg_right hm.2.2 (Nat.cast_nonneg k))

/-- The physical strong restriction holds uniformly away from tau=0. -/
theorem strong_uniform_eventually (L U : ℝ) (hL : 0 < L) (hLU : L ≤ U) :
    ∀ᶠ k : ℕ in atTop,∀ tau ∈ Set.Icc L U,1 ≤ ((k:ℝ)-2)*b tau k := by
  have hU : 0 ≤ U := hL.le.trans hLU
  let B := L*limitC U
  have hB : 0 < B := mul_pos hL (Real.exp_pos _)
  have herr : Tendsto (fun k : ℕ => Db U/(k:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hs : ∀ᶠ k : ℕ in atTop,Db U/(k:ℝ) ≤ B/2 :=
    herr.eventually (eventually_le_nhds (by linarith))
  have hsize : ∀ᶠ k : ℕ in atTop,2+2/B ≤ (k:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop).eventually (eventually_ge_atTop _)
  have htu : ∀ᶠ k : ℕ in atTop,2*U ≤ (k:ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop).eventually (eventually_ge_atTop _)
  filter_upwards [hs,hsize,htu,eventually_ge_atTop (2:ℕ)] with k hs hk hku hk2
  intro tau ht
  have ht0 : 0 ≤ tau := hL.le.trans ht.1
  have hm := constants_mono tau U ht0 ht.2
  have he := (coefficients tau ht0 k hk2 (by linarith [ht.2])).2.2.2.2.2.2.2
  have he' : |b tau k-tau*limitC tau| ≤ B/2 :=
    he.trans ((div_le_div_of_nonneg_right hm.2.1 (Nat.cast_nonneg k)).trans hs)
  have hC : limitC U ≤ limitC tau := Real.exp_le_exp.mpr (by linarith [ht.2])
  have hbbase : B ≤ tau*limitC tau :=
    mul_le_mul ht.1 hC (Real.exp_pos _).le ht0
  have hb : B/2 ≤ b tau k := by have := (abs_le.mp he').1;linarith
  have hdiv : (2/B)*B=2 := div_mul_cancel₀ 2 hB.ne'
  have hk0 : 0 ≤ (k:ℝ)-2 := by
    have : 0<2/B := by positivity
    linarith
  nlinarith [mul_nonneg hk0 (show 0 ≤ b tau k-B/2 by linarith)]

#print axioms constants_mono
#print axioms uniform_finite_value_error
#print axioms strong_uniform_eventually
end
end CIGAMF.P13.D6UniformScaledBounds
