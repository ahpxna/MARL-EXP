import «LeanD6CyclicPhaseLawV1»
import «LeanD6DiscoveryPathLawV1»

/-! A06: one canonical infinite stream of actual cyclic queries, and an
all-epoch confidence sequence. Repetition counts are nested prefixes of the
same stream. The estimator does not receive the hidden label or true phase.

The error budget is delta/((s+1)(s+2)), not a fixed per-epoch delta. This module
proves coverage, including at a selected epoch; it does not assert adapted
stopping, termination, allocation tracking, or an expected Gamma rate. -/
namespace CIGAMF.P13.D6CyclicConfidenceSequence
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6CyclicPhaseDesign
open CIGAMF.P13.D6CyclicPhaseLaw
noncomputable section
variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]

abbrev Sample (C : Type*) := (ℕ × C) → ℝ

def path (G : C → Finset (I n)) (A : Finset (I n)) (j : I n) (mu : ℝ) :
    Measure (Sample C) :=
  Measure.infinitePi (fun t => gaussianReal (actualMean A j mu (.inr (G t.2,false))) 1)

instance path_probability (G : C → Finset (I n)) (A : Finset (I n)) (j : I n) (mu : ℝ) :
    IsProbabilityMeasure (path G A j mu) := by unfold path; infer_instance

def restrict (L : ℕ) (x : Sample C) (t : Fin L × C) : ℝ := x (t.1.val,t.2)

theorem finite_raw_law (G : C → Finset (I n)) (A : Finset (I n)) (j : I n)
    (mu : ℝ) (L : ℕ) :
    HasLaw (restrict (C:=C) L) (observations G A j mu L) (path G A j mu) := by
  have hinj : Function.Injective (fun t : Fin L × C => (t.1.val,t.2)) := by
    intro a b h
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst h)
    · exact congrArg (fun x : ℕ × C => x.2) h
  refine ⟨(measurable_pi_iff.mpr (fun t => measurable_pi_apply (t.1.val,t.2))).aemeasurable,?_⟩
  unfold path restrict observations FiniteGaussianSumLaw.law
  rw [Measure.map_infinitePi_infinitePi_of_inj hinj,Measure.infinitePi_eq_pi]

def varianceParameter (q L : ℕ) : NNReal :=
  (Fintype.card C : NNReal)/((L:NNReal)*(q:NNReal)^4)

def pathEstimate (q L : ℕ) (x : Sample C) : ℝ := estimate q L (restrict L x)

theorem path_estimate_law (G : C → Finset (I n)) (A : Finset (I n)) (j : I n)
    (q L : ℕ) (hq : 0 < q) (hL : 0 < L) (mu : ℝ)
    (hm : (∑ t,actualMean A j mu (.inr (G t,false))) =
      Fintype.card C+(q:ℝ)^2*(1-mu)) :
    HasLaw (pathEstimate (C:=C) q L) (gaussianReal mu (varianceParameter (C:=C) q L))
      (path G A j mu) := by
  have h := (estimate_law G A j q L hq hL mu hm).fun_comp (finite_raw_law G A j mu L)
  have hv : ((L*Fintype.card C:ℕ):NNReal) /
      NNReal.mk (((L:ℝ)*(q:ℝ)^2)^2) (sq_nonneg _) = varianceParameter (C:=C) q L := by
    apply Subtype.ext
    change ((L*Fintype.card C:ℕ):ℝ) / (((L:ℝ)*(q:ℝ)^2)^2) =
      (Fintype.card C:ℝ)/((L:ℝ)*(q:ℝ)^4)
    rw [Nat.cast_mul]
    have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    have hL0 : (L:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    field_simp
    <;> ring
  rw [hv] at h
  exact h

theorem variance_parameter_pos (q L : ℕ) (hq : 0 < q) (hL : 0 < L)
    (hC : 0 < Fintype.card C) : 0 < varianceParameter (C:=C) q L := by
  unfold varianceParameter
  positivity

/-- Generic two-sided Gaussian concentration, reused on the derived path law. -/
theorem gaussian_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (mu : ℝ) (v : NNReal)
    (hlaw : HasLaw X (gaussianReal mu v) P) (eps : ℝ) (heps : 0 ≤ eps) :
    P.real {x | eps ≤ |X x-mu|} ≤ 2*Real.exp (-eps^2/(2*(v:ℝ))) := by
  have h := D6DiscoveryPathLaw.gaussian_centered_subgaussian mu v hlaw
  have hp := h.measure_ge_le heps
  have hn := h.neg.measure_ge_le heps
  have he : {x | eps ≤ |X x-mu|} =
      {x | eps ≤ X x-mu} ∪ {x | eps ≤ -(X x-mu)} := by
    ext x
    simp only [Set.mem_setOf_eq,Set.mem_union,le_abs]
  have hu := measureReal_union_le (μ:=P) {x | eps ≤ X x-mu} {x | eps ≤ -(X x-mu)}
  rw [he]
  change P.real {x | eps ≤ -(X x-mu)} ≤ _ at hn
  linarith

def radius (v : NNReal) (delta : ℝ) : ℝ := Real.sqrt (2*(v:ℝ)*Real.log (2/delta))

theorem gaussian_radius_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (mu : ℝ) (v : NNReal) (hv : 0 < v)
    (hlaw : HasLaw X (gaussianReal mu v) P) (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1) :
    P {x | radius v delta ≤ |X x-mu|} ≤ ENNReal.ofReal delta := by
  have hvR : (0:ℝ) < (v:ℝ) := hv
  have hlog : 0 ≤ Real.log (2/delta) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hd).mpr
    linarith
  have hs : (radius v delta)^2 = 2*(v:ℝ)*Real.log (2/delta) :=
    Real.sq_sqrt (by positivity)
  have hh := gaussian_tail mu v hlaw (radius v delta) (Real.sqrt_nonneg _)
  have hex : -(radius v delta)^2/(2*(v:ℝ)) = -Real.log (2/delta) := by
    rw [hs]
    field_simp
    <;> ring
  rw [hex,Real.exp_neg,Real.exp_log (by positivity : (0:ℝ)<2/delta)] at hh
  have he : 2*(2/delta)⁻¹=delta := by field_simp
  rw [he] at hh
  have hen := ENNReal.ofReal_le_ofReal hh
  rwa [ofReal_measureReal] at hen

/-- Summable confidence spending with logarithmic dependence on epoch index. -/
def epochError (delta : ℝ) (s : ℕ) : ℝ := delta/(((s:ℝ)+1)*((s:ℝ)+2))

theorem epoch_error_pos (delta : ℝ) (hd : 0 < delta) (s : ℕ) : 0 < epochError delta s := by
  unfold epochError
  positivity

theorem epoch_error_le (delta : ℝ) (hd : 0 ≤ delta) (s : ℕ) : epochError delta s ≤ delta := by
  unfold epochError
  have hs : (0:ℝ) ≤ s := by positivity
  apply (div_le_iff₀ (by positivity : (0:ℝ)<((s:ℝ)+1)*((s:ℝ)+2))).mpr
  have hden : (1:ℝ) ≤ ((s:ℝ)+1)*((s:ℝ)+2) := by nlinarith
  exact le_mul_of_one_le_right hd hden

theorem epoch_error_partial_sum (delta : ℝ) (N : ℕ) :
    (∑ s ∈ range N,epochError delta s)=delta-delta/((N:ℝ)+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ,ih]
      simp only [epochError,Nat.cast_add,Nat.cast_one]
      have h1 : (N:ℝ)+1 ≠ 0 := by positivity
      have h2 : (N:ℝ)+2 ≠ 0 := by positivity
      field_simp
      <;> ring

theorem epoch_error_budget (delta : ℝ) (hd : 0 ≤ delta) :
    (∑' s : ℕ,ENNReal.ofReal (epochError delta s)) ≤ ENNReal.ofReal delta := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => by unfold epochError; positivity),
    epoch_error_partial_sum]
  apply ENNReal.ofReal_le_ofReal
  have h : 0 ≤ delta/((N:ℝ)+1) := by positivity
  linarith

def epochLength (L0 s : ℕ) : ℕ := L0*2^s

def width (q L0 s : ℕ) (delta : ℝ) : ℝ :=
  radius (varianceParameter (C:=C) q (epochLength L0 s)) (epochError delta s)

/-- Explicit q-dependence, including the error-spending factor in the logarithm. -/
theorem width_formula (q L0 s : ℕ) (delta : ℝ) :
    width (C:=C) q L0 s delta =
      Real.sqrt (2*((Fintype.card C:ℝ)/((epochLength L0 s:ℝ)*(q:ℝ)^4))*
        Real.log (2/(delta/(((s:ℝ)+1)*((s:ℝ)+2))))) := by
  simp [width,radius,varianceParameter,epochError]

/-- All epochs on the SAME raw-query path, with no path-law or tail premise. -/
theorem cyclic_confidence_sequence (G : C → Finset (I n)) (A : Finset (I n)) (j : I n)
    (q L0 : ℕ) (hq : 0 < q) (hL : 0 < L0) (hC : 0 < Fintype.card C)
    (mu : ℝ) (hm : (∑ t,actualMean A j mu (.inr (G t,false))) =
      Fintype.card C+(q:ℝ)^2*(1-mu))
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1) :
    (path G A j mu) (⋃ s : ℕ,
      {x | width (C:=C) q L0 s delta ≤ |pathEstimate q (epochLength L0 s) x-mu|})
      ≤ ENNReal.ofReal delta := by
  apply (measure_iUnion_le _).trans
  apply (ENNReal.tsum_le_tsum (fun s => ?_)).trans (epoch_error_budget delta hd.le)
  have hLs : 0 < epochLength L0 s := Nat.mul_pos hL (by positivity)
  exact gaussian_radius_tail mu _ (variance_parameter_pos q _ hq hLs hC)
    (path_estimate_law G A j q _ hq hLs mu hm) (epochError delta s)
    (epoch_error_pos delta hd s) ((epoch_error_le delta hd.le s).trans hd1)

/-- Coverage survives choosing an epoch from the data; this does not assert
that a particular choice is an adapted stopping time or that it terminates. -/
theorem selected_epoch_error (G : C → Finset (I n)) (A : Finset (I n)) (j : I n)
    (q L0 : ℕ) (hq : 0 < q) (hL : 0 < L0) (hC : 0 < Fintype.card C)
    (mu : ℝ) (hm : (∑ t,actualMean A j mu (.inr (G t,false))) =
      Fintype.card C+(q:ℝ)^2*(1-mu))
    (delta : ℝ) (hd : 0 < delta) (hd1 : delta ≤ 1) (select : Sample C → ℕ) :
    (path G A j mu) {x | width (C:=C) q L0 (select x) delta ≤
      |pathEstimate q (epochLength L0 (select x)) x-mu|} ≤ ENNReal.ofReal delta := by
  apply le_trans (measure_mono ?_) (cyclic_confidence_sequence G A j q L0 hq hL hC mu hm delta hd hd1)
  intro x hx
  exact Set.mem_iUnion.mpr ⟨select x,hx⟩

/-- One legal cyclic design chosen without A works for every hidden A and every
real mu; no assumption of knowing the allocation phase is used. -/
theorem actual_cyclic_confidence_sequence_exists (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1)) :
    ∃ G : ZMod (2*q+1) → Finset (I (2*q+1)),
      (∀ t,Legal j q (.inr (G t,false)) ∧ (G t).card=q) ∧
      ∀ A : Finset (I (2*q+1)), j ∉ A → (others A j).card=q →
      ∀ L0 : ℕ, 0 < L0 → ∀ mu delta : ℝ, 0 < delta → delta ≤ 1 →
      (path G A j mu) (⋃ s : ℕ,
        {x | width (C:=ZMod (2*q+1)) q L0 s delta ≤
          |pathEstimate q (epochLength L0 s) x-mu|}) ≤ ENNReal.ofReal delta := by
  obtain ⟨G,hlegal,hm⟩ := design_exists q hq j
  refine ⟨G,hlegal,?_⟩
  intro A hj hB L0 hL mu delta hd hd1
  apply cyclic_confidence_sequence G A j q L0 (by omega) hL
    (by simp) mu ?_ delta hd hd1
  simpa using hm A hj hB mu

#print axioms finite_raw_law
#print axioms path_estimate_law
#print axioms gaussian_tail
#print axioms gaussian_radius_tail
#print axioms epoch_error_partial_sum
#print axioms epoch_error_budget
#print axioms width_formula
#print axioms cyclic_confidence_sequence
#print axioms selected_epoch_error
#print axioms actual_cyclic_confidence_sequence_exists
end
end CIGAMF.P13.D6CyclicConfidenceSequence
