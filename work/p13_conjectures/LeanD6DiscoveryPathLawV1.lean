import «LeanD6NuisanceFreeDiscoveryLawV1»
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Moments.SubGaussian

/-! One canonical infinite raw-observation probability space for discovery.
Finite repeated contrasts are derived as marginals; Gaussian concentration is
proved from the resulting law rather than supplied as an assumption. -/
namespace CIGAMF.P13.D6DiscoveryPathLaw
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6NuisanceFreeDiscoveryLaw
open CIGAMF.P13.FiniteGaussianSumLaw
noncomputable section

def path (means : Fin 4 → ℝ) : Measure ((ℕ × Fin 4) → ℝ) :=
  Measure.infinitePi (fun t => gaussianReal (means t.2) 1)

instance path_probability (means : Fin 4 → ℝ) : IsProbabilityMeasure (path means) := by
  unfold path;infer_instance

def restrict (r : ℕ) (x : (ℕ × Fin 4) → ℝ) (t : Fin r × Fin 4) : ℝ := x (t.1.val,t.2)

theorem finite_raw_law (means : Fin 4 → ℝ) (r : ℕ) :
    HasLaw (restrict r) (law (fun t : Fin r × Fin 4 => means t.2)) (path means) := by
  have hinj : Function.Injective (fun t : Fin r × Fin 4 => (t.1.val,t.2)) := by
    intro a b h
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst h)
    · exact congrArg (fun x : ℕ × Fin 4 => x.2) h
  refine ⟨(measurable_pi_iff.mpr (fun t => measurable_pi_apply (t.1.val,t.2))).aemeasurable,?_⟩
  unfold path restrict law
  rw [Measure.map_infinitePi_infinitePi_of_inj hinj,Measure.infinitePi_eq_pi]

def average (r : ℕ) (x : (ℕ × Fin 4) → ℝ) : ℝ :=
  (∑ t : Fin r × Fin 4,signs t.2*x (t.1.val,t.2))/(r:ℝ)

theorem repeated_contrast_law (means : Fin 4 → ℝ) (r : ℕ) (hr : 0 < r) :
    HasLaw (average r) (gaussianReal (∑ t,signs t*means t) (4/(r:NNReal))) (path means) := by
  have hs : ∀ t : Fin r × Fin 4, (signs t.2)^2=1 := by
    intro t;rcases t with ⟨u,t⟩;fin_cases t <;> norm_num [signs]
  have hh := (signed_sum_law (fun t : Fin r × Fin 4 => means t.2)
    (fun t => signs t.2) hs univ).fun_comp (finite_raw_law means r)
  have hm : (∑ t : Fin r × Fin 4, signs t.2*means t.2) =
      (r:ℝ)*(∑ t,signs t*means t) := by simp [Fintype.sum_prod_type]
  have hv : NNReal.mk ((1/(r:ℝ))^2) (sq_nonneg _) * (Fintype.card (Fin r × Fin 4):NNReal) = 4/(r:NNReal) := by
    have hn : (r:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
    apply Subtype.ext
    change (1/(r:ℝ))^2*(Fintype.card (Fin r × Fin 4):ℝ)=4/(r:ℝ)
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
    <;> ring
  have hn : (r:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have h := gaussianReal_const_mul hh (1/(r:ℝ))
  simp only [Finset.card_univ,hm,hv] at h
  have he : (1/(r:ℝ))*((r:ℝ)*(∑ t,signs t*means t)) = ∑ t,signs t*means t := by field_simp
  rw [he] at h
  unfold average
  simpa [restrict,div_eq_mul_inv,mul_comm] using h

lemma gaussian_centered_subgaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (mu : ℝ) (v : NNReal)
    (hlaw : HasLaw X (gaussianReal mu v) P) :
    HasSubgaussianMGF (fun x => X x-mu) v P := by
  have hc : HasLaw (fun x => X x-mu) (gaussianReal 0 v) P := by
    simpa [sub_eq_add_neg] using gaussianReal_add_const hlaw (-mu)
  have hg : HasSubgaussianMGF id v (gaussianReal 0 v) := by
    refine ⟨fun t => integrable_exp_mul_gaussianReal t,?_⟩
    intro t
    rw [mgf_id_gaussianReal]
    simp
  have ht : HasSubgaussianMGF id v (P.map (fun x => X x-mu)) := by rw [hc.map_eq];exact hg
  exact (HasSubgaussianMGF.id_map_iff hc.aemeasurable).mp ht

/-- Two-sided tail on the same path at every repetition count r. -/
theorem repeated_contrast_tail (means : Fin 4 → ℝ) (r : ℕ) (hr : 0 < r)
    (eps : ℝ) (heps : 0 ≤ eps) :
    (path means).real {x | eps ≤ |average r x-(∑ t,signs t*means t)|} ≤
      2*Real.exp (-(r:ℝ)*eps^2/8) := by
  let X := fun x => average r x-(∑ t,signs t*means t)
  have h := gaussian_centered_subgaussian _ _ (repeated_contrast_law means r hr)
  have hp := h.measure_ge_le heps
  have hn := h.neg.measure_ge_le heps
  have he : {x | eps ≤ |X x|} = {x | eps ≤ X x} ∪ {x | eps ≤ -X x} := by
    ext x;simp only [Set.mem_setOf_eq,Set.mem_union,le_abs]
  have hu := measureReal_union_le (μ := path means) {x | eps ≤ X x} {x | eps ≤ -X x}
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hex : -eps^2/(2*(↑(4/(r:NNReal)):ℝ)) = -(r:ℝ)*eps^2/8 := by
    simp only [NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_natCast]
    field_simp
    <;> ring
  rw [hex] at hp hn
  change (path means).real {x | eps ≤ |X x|} ≤ _
  rw [he]
  change (path means).real {x | eps ≤ X x} ≤ _ at hp
  change (path means).real {x | eps ≤ -X x} ≤ _ at hn
  linarith

#print axioms finite_raw_law
#print axioms repeated_contrast_law
#print axioms repeated_contrast_tail
end
end CIGAMF.P13.D6DiscoveryPathLaw
