import «LeanD6BlindPhaseBlocksV1»

/-! Exact finite-budget phase error on the raw independent three-query blocks.
The score is computed without the hidden label or the true side. A budget of
3*M queries has error Phi(-q*epsilon*sqrt(3*M)/3) on either side. -/
namespace CIGAMF.P13.D6BlindPhaseDecision
open MeasureTheory ProbabilityTheory Set
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6BlindPhaseBlocks
open CIGAMF.P13.AdaptiveTranscriptKernel CIGAMF.P13.GaussianSampleProduct
open CIGAMF.P13.GaussianProductOverlap CIGAMF.P13.D6GaussianOverlap
noncomputable section

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
def sampleMap (f : X → Y) : (M : ℕ) → Samples X M → Samples Y M
  | 0 => id
  | M+1 => fun x => (sampleMap f M x.1,f x.2)

lemma measurable_sampleMap (f : X → Y) (hf : Measurable f) (M : ℕ) :
    Measurable (sampleMap f M) := by
  induction M with
  | zero => exact measurable_id
  | succ M ih => exact (ih.comp measurable_fst).prodMk (hf.comp measurable_snd)

lemma sampleMap_law (f : X → Y) (hf : Measurable f) (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q] (hl : HasLaw f Q P) (M : ℕ) :
    HasLaw (sampleMap f M) (resource Q M ()) (resource P M ()) := by
  induction M with
  | zero => exact HasLaw.id
  | succ M ih =>
    have he (R : Measure X) [IsProbabilityMeasure R] : resource R (M+1) ()=(resource R M ()).prod R := by
      rw [resource,Kernel.prod_apply,Kernel.const_apply]
    have he' : resource Q (M+1) ()=(resource Q M ()).prod Q := by
      rw [resource,Kernel.prod_apply,Kernel.const_apply]
    rw [he,he']
    have hx : HasLaw (Prod.fst : Samples X M × X → Samples X M) (resource P M ())
        ((resource P M ()).prod P) := by refine ⟨by fun_prop,?_⟩; simp
    have hy : HasLaw (Prod.snd : Samples X M × X → X) P
        ((resource P M ()).prod P) := by refine ⟨by fun_prop,?_⟩; simp
    have hi : IndepFun (fun x : Samples X M × X => sampleMap f M x.1) (fun x => f x.2)
        ((resource P M ()).prod P) :=
      (indepFun_prod measurable_id measurable_id).comp (measurable_sampleMap f hf M) hf
    exact hi.hasLaw_prod (ih.fun_comp hx) (hl.fun_comp hy)

variable {n q : ℕ} {j : I n}

def scores (q : ℕ) (mu0 : ℝ) (M : ℕ) := sampleMap (blockScore q mu0) M

theorem actual_score_samples_law (p : ThreePartition j q) (hq : 3 ≤ q)
    (A : Finset (I n)) (hj : j ∉ A) (hB : (others A j).card=q) (mu mu0 : ℝ) (M : ℕ) :
    HasLaw (scores q mu0 M) (resource (gaussianReal (q*(mu-mu0)/Real.sqrt 3) 1) M ())
      (resource (blockLaw p A mu) M ()) := by
  exact sampleMap_law _ (by unfold blockScore blockSum; fun_prop) _ _
    (actual_score_law p hq A hj hB mu mu0) M

lemma budget_scale (q epsilon : ℝ) (M : ℕ) :
    (q*epsilon/Real.sqrt 3)*Real.sqrt M=q*epsilon*Real.sqrt (3*(M:ℝ))/3 := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
  have hs : Real.sqrt (3:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have he : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith only [congrArg (fun x : ℝ => q*epsilon*Real.sqrt M*x) he]

/-- Minus-side probability of incorrectly choosing plus from the raw data. -/
theorem actual_minus_error (p : ThreePartition j q) (hq : 3 ≤ q)
    (A : Finset (I n)) (hj : j ∉ A) (hB : (others A j).card=q)
    (mu0 epsilon : ℝ) (M : ℕ) (hM : 0 < M) :
    (resource (blockLaw p A (mu0-epsilon)) M ()
      {x | 0 ≤ sumSamples M (scores q mu0 M x)}).toReal=
      standardTail (q*epsilon*Real.sqrt (3*(M:ℝ))/3) := by
  have hl := actual_score_samples_law p hq A hj hB (mu0-epsilon) mu0 M
  have he : (q:ℝ)*((mu0-epsilon)-mu0)/Real.sqrt 3= -(q*epsilon/Real.sqrt 3) := by ring
  rw [he] at hl
  have hm := hl.measure_eq (p := fun x => 0 ≤ sumSamples M x)
    (measurableSet_le measurable_const (measurable_sumSamples M))
  rw [negative_sum_half_mass _ M hM,budget_scale] at hm
  exact congrArg ENNReal.toReal hm

/-- Plus-side probability of incorrectly choosing minus; ties choose plus. -/
theorem actual_plus_error (p : ThreePartition j q) (hq : 3 ≤ q)
    (A : Finset (I n)) (hj : j ∉ A) (hB : (others A j).card=q)
    (mu0 epsilon : ℝ) (M : ℕ) (hM : 0 < M) :
    (resource (blockLaw p A (mu0+epsilon)) M ()
      {x | sumSamples M (scores q mu0 M x) < 0}).toReal=
      standardTail (q*epsilon*Real.sqrt (3*(M:ℝ))/3) := by
  have hl := actual_score_samples_law p hq A hj hB (mu0+epsilon) mu0 M
  have he : (q:ℝ)*((mu0+epsilon)-mu0)/Real.sqrt 3=q*epsilon/Real.sqrt 3 := by ring
  rw [he] at hl
  have hm := hl.measure_eq (p := fun x => sumSamples M x < 0)
    (measurableSet_lt (measurable_sumSamples M) measurable_const)
  rw [positive_sum_half_mass _ M hM,budget_scale] at hm
  exact congrArg ENNReal.toReal hm

#print axioms sampleMap_law
#print axioms actual_score_samples_law
#print axioms budget_scale
#print axioms actual_minus_error
#print axioms actual_plus_error
end
end CIGAMF.P13.D6BlindPhaseDecision
