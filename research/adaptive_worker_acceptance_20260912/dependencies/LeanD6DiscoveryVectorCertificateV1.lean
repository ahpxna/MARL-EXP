import «LeanD6DiscoveryPathLawV1»

/-! Simultaneous label discovery on one product of infinite raw-query paths.
The finite mean identity is the only construction-specific input in the generic
vector lemmas; the D6 bridge supplies it from actual legal queries. -/
namespace CIGAMF.P13.D6DiscoveryVectorCertificate
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6DiscoveryPathLaw
open CIGAMF.P13.D6NuisanceFreeDiscoveryLaw
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Sample (I : Type*) := I → ((ℕ × Fin 4) → ℝ)

def vectorPath (means : I → Fin 4 → ℝ) : Measure (Sample I) := Measure.pi (fun i => path (means i))

instance vector_probability (means : I → Fin 4 → ℝ) : IsProbabilityMeasure (vectorPath means) := by
  unfold vectorPath;infer_instance

def score (r : ℕ) (x : Sample I) (i : I) : ℝ := average r (x i)

def target (B : Finset I) (a i : I) : ℝ := (if i ∈ B then 1 else 0)-(if a ∈ B then 1 else 0)

def bad (B : Finset I) (a : I) (r : ℕ) : Set (Sample I) :=
  {x | ∃ i, 1/4 ≤ |score r x i-target B a i|}

def Certified (r : ℕ) (q : ℕ) (x : Sample I) (S : Finset I) : Prop :=
  S.card=q ∧ ∀ i ∈ S, ∀ j ∉ S, score r x j+1/2 < score r x i

def accepts (r q : ℕ) (x : Sample I) : Prop := ∃ S, Certified r q x S

lemma score_measurable (r : ℕ) (i : I) : Measurable (fun x : Sample I => score r x i) := by
  unfold score D6DiscoveryPathLaw.average
  exact (Finset.measurable_fun_sum (f := fun (t : Fin r × Fin 4) (x : Sample I) => signs t.2*x i (t.1.val,t.2)) univ (fun t _ =>
    measurable_const.mul ((measurable_pi_apply (t.1.val,t.2)).comp (measurable_pi_apply i)))).div_const r

lemma accepts_measurable (r q : ℕ) : MeasurableSet {x : Sample I | accepts r q x} := by
  simp only [accepts,Certified,Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro S
  by_cases hS : S.card=q
  · simp only [hS,true_and,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ : i ∈ S =>
      MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ : j ∉ S =>
        measurableSet_lt ((score_measurable r j).add_const _) (score_measurable r i)))))
  · simp [hS]

lemma error_lt_of_not_bad (B : Finset I) (a : I) (r : ℕ) (x : Sample I)
    (hx : x ∉ bad B a r) (i : I) : |score r x i-target B a i| < 1/4 := by
  exact lt_of_not_ge (fun h => hx ⟨i,h⟩)

theorem good_accepts (B : Finset I) (a : I) (r : ℕ) (x : Sample I)
    (hx : x ∉ bad B a r) : accepts r B.card x := by
  refine ⟨B,rfl,?_⟩
  intro i hi j hj
  have h1 := (abs_lt.mp (error_lt_of_not_bad B a r x hx i)).1
  have h2 := (abs_lt.mp (error_lt_of_not_bad B a r x hx j)).2
  simp only [target,hi,hj,↓reduceIte] at h1 h2
  linarith

theorem good_certificate_correct (B S : Finset I) (a : I) (r : ℕ) (x : Sample I)
    (hx : x ∉ bad B a r) (hS : Certified r B.card x S) : S=B := by
  have hcard := hS.1
  apply eq_of_subset_of_card_le ?_ (by omega)
  intro i hi
  by_contra hiB
  have hn : ¬ B ⊆ S := by
    intro h
    have he : B=S := eq_of_subset_of_card_le h (by omega)
    exact hiB (he.symm ▸ hi)
  obtain ⟨j,hjB,hjS⟩ := not_subset.mp hn
  have hgap := hS.2 i hi j hjS
  have h1 := (abs_lt.mp (error_lt_of_not_bad B a r x hx i)).2
  have h2 := (abs_lt.mp (error_lt_of_not_bad B a r x hx j)).1
  simp only [target,hiB,hjB,↓reduceIte] at h1 h2
  linarith

theorem vector_tail (means : I → Fin 4 → ℝ) (B : Finset I) (a : I)
    (hm : ∀ i, (∑ t,signs t*means i t)=target B a i)
    (r : ℕ) (hr : 0 < r) :
    (vectorPath means).real (bad B a r) ≤
      2*(Fintype.card I:ℝ)*Real.exp (-(r:ℝ)/128) := by
  have hi (i : I) : (vectorPath means).real {x | 1/4 ≤ |score r x i-target B a i|} ≤
      2*Real.exp (-(r:ℝ)/128) := by
    have he : HasLaw (fun x : Sample I => x i) (path (means i)) (vectorPath means) :=
      (measurePreserving_eval (fun i => path (means i)) i).hasLaw
    have hp := repeated_contrast_tail (means i) r hr (1/4) (by norm_num)
    rw [hm i] at hp
    have hmeas : MeasurableSet {y | (1:ℝ)/4 ≤ |D6DiscoveryPathLaw.average r y-target B a i|} := by
      apply measurableSet_le measurable_const
      have hmean : Measurable (D6DiscoveryPathLaw.average r) := by
        unfold D6DiscoveryPathLaw.average
        exact (Finset.measurable_fun_sum (f := fun (t : Fin r × Fin 4) (y : (ℕ × Fin 4) → ℝ) => signs t.2*y (t.1.val,t.2)) univ (fun t _ =>
          measurable_const.mul (measurable_pi_apply (t.1.val,t.2)))).div_const r
      exact (hmean.sub_const _).abs
    have heq := he.measureReal_eq hmeas
    have hex : -(r:ℝ)*((1:ℝ)/4)^2/8=-(r:ℝ)/128 := by ring
    simpa only [score,hex] using heq.trans_le hp
  have he : bad B a r = ⋃ i,{x | 1/4 ≤ |score r x i-target B a i|} := by ext x;simp [bad]
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _i : I, 2*Real.exp (-(r:ℝ)/128) := sum_le_sum (fun i _ => hi i)
    _ = _ := by simp;ring

#print axioms good_accepts
#print axioms good_certificate_correct
#print axioms vector_tail
end
end CIGAMF.P13.D6DiscoveryVectorCertificate
