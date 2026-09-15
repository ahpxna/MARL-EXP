import Mathlib
import «LeanMasterReferenceUncertaintyV1»

/-! Minimal reference-kernel non-identifiability witnesses. -/

namespace CIGAMF.V7.ReferenceIdentifiability

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.JointKernel
open CIGAMF.V4.Pairwise

def kernelFlat (a b : Fin 2) : ℝ := if b = 0 then 1 else 0

def kernelReactive (a b : Fin 2) : ℝ := if b = a then 1 else 0

def observedSource : Finset (Fin 2) := {0}

theorem kernelFlat_valid : Valid kernelFlat := by
  constructor
  · intro a b
    unfold kernelFlat
    split_ifs <;> norm_num
  · intro a
    fin_cases a <;> norm_num [kernelFlat, Fin.sum_univ_two]

theorem kernelReactive_valid : Valid kernelReactive := by
  constructor
  · intro a b
    unfold kernelReactive
    split_ifs <;> norm_num
  · intro a
    fin_cases a <;> norm_num [kernelReactive, Fin.sum_univ_two]

theorem RI1_observed_source_indistinguishable :
    (∀ a ∈ observedSource, kernelFlat a = kernelReactive a) ∧
    kernelFlat 1 ≠ kernelReactive 1 := by
  constructor
  · intro a ha
    simp [observedSource] at ha
    subst a
    funext b
    fin_cases b <;> norm_num [kernelFlat, kernelReactive]
  · intro h
    have := congrFun h (1 : Fin 2)
    norm_num [kernelFlat, kernelReactive] at this

def complementSignal (b : Fin 2) : ℝ := if b = 0 then 0 else 1

theorem flat_expectation_zero :
    (fun a => expectation kernelFlat complementSignal a) =
      (fun _ : Fin 2 => 0) := by
  funext a
  fin_cases a <;>
    norm_num [expectation, kernelFlat, complementSignal, Fin.sum_univ_two]

theorem reactive_expectation_signal :
    (fun a => expectation kernelReactive complementSignal a) =
      complementSignal := by
  funext a
  fin_cases a <;>
    norm_num [expectation, kernelReactive, complementSignal, Fin.sum_univ_two]

theorem osc_const_zero_fin2 : osc (fun _ : Fin 2 => (0 : ℝ)) = 0 := by
  have hmax : maxVal (fun _ : Fin 2 => (0 : ℝ)) = 0 := by
    apply le_antisymm
    · exact maxVal_le _ (fun _ => le_rfl)
    · exact le_maxVal (fun _ : Fin 2 => (0 : ℝ)) (0 : Fin 2)
  have hmin : minVal (fun _ : Fin 2 => (0 : ℝ)) = 0 := by
    apply le_antisymm
    · exact minVal_le (fun _ : Fin 2 => (0 : ℝ)) (0 : Fin 2)
    · exact le_minVal _ (fun _ => le_rfl)
  simp [osc, hmax, hmin]

theorem osc_complementSignal : osc complementSignal = 1 := by
  have hmax : maxVal complementSignal = 1 := by
    apply le_antisymm
    · apply maxVal_le
      intro a
      fin_cases a <;> norm_num [complementSignal]
    · simpa [complementSignal] using le_maxVal complementSignal (1 : Fin 2)
  have hmin : minVal complementSignal = 0 := by
    apply le_antisymm
    · simpa [complementSignal] using minVal_le complementSignal (0 : Fin 2)
    · apply le_minVal
      intro a
      fin_cases a <;> norm_num [complementSignal]
  simp [osc, hmax, hmin]

theorem RI2_indistinguishable_kernels_different_chi :
    osc (fun a => expectation kernelFlat complementSignal a) = 0 ∧
    osc (fun a => expectation kernelReactive complementSignal a) = 1 := by
  rw [flat_expectation_zero, reactive_expectation_signal]
  exact ⟨osc_const_zero_fin2, osc_complementSignal⟩

noncomputable def scoreFlat (j : Fin 2) : ℝ := if j = 0 then 0 else 1 / 2
noncomputable def scoreReactive (j : Fin 2) : ℝ := if j = 0 then 1 else 1 / 2

theorem topFlat_relation_one :
    IsTopKByScore scoreFlat ({1} : Finset (Fin 2)) 1 := by
  constructor
  · simp
  · intro candidate hc
    rcases Finset.card_eq_one.mp hc with ⟨j, rfl⟩
    fin_cases j <;> norm_num [scoreFlat]

theorem topReactive_relation_zero :
    IsTopKByScore scoreReactive ({0} : Finset (Fin 2)) 1 := by
  constructor
  · simp
  · intro candidate hc
    rcases Finset.card_eq_one.mp hc with ⟨j, rfl⟩
    fin_cases j <;> norm_num [scoreReactive]

/- Relation zero's score is exactly the kernel-induced span from RI2, while
relation one is a fixed half-span.  Hence the observationally indistinguishable
kernels reverse the unique Top-1 decision. -/
theorem RI2_downstream_top1_changes :
    scoreFlat 0 = osc (fun a => expectation kernelFlat complementSignal a) ∧
    scoreReactive 0 = osc (fun a => expectation kernelReactive complementSignal a) ∧
    IsTopKByScore scoreFlat ({1} : Finset (Fin 2)) 1 ∧
    IsTopKByScore scoreReactive ({0} : Finset (Fin 2)) 1 ∧
    ({1} : Finset (Fin 2)) ≠ {0} := by
  rw [RI2_indistinguishable_kernels_different_chi.1,
    RI2_indistinguishable_kernels_different_chi.2]
  exact ⟨by norm_num [scoreFlat], by norm_num [scoreReactive],
    topFlat_relation_one, topReactive_relation_zero, by decide⟩

end CIGAMF.V7.ReferenceIdentifiability
