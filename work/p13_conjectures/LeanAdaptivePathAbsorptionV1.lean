import «LeanAdaptivePathLawV1»
import Mathlib.MeasureTheory.Measure.Continuity

/-! Absorption on the canonical path follows from the one-step kernels.
No persistence assumption is imposed on impossible sequences of states. -/
namespace CIGAMF.P13.AdaptivePathAbsorption
open MeasureTheory ProbabilityTheory Set Finset Function Preorder
open CIGAMF.P13.AdaptivePathLaw CIGAMF.P13.AdaptiveTranscriptKernel
noncomputable section
variable {H : Type*} [MeasurableSpace H]

theorem path_step_absorbing (initial : Measure H) [IsProbabilityMeasure initial]
    (step : ℕ → Kernel H H) [∀ t,IsMarkovKernel (step t)]
    (bad : Set H) (hbad : MeasurableSet bad)
    (absorb : ∀ t h,h ∈ bad → ∀ᵐ h' ∂step t h,h' ∈ bad) (N : ℕ) :
    ∀ᵐ omega ∂path initial step,omega N ∈ bad → omega (N+1) ∈ bad := by
  let pred : (Finset.Iic N → H) × H → Prop :=
    fun x => x.1 ⟨N,Finset.mem_Iic.mpr le_rfl⟩ ∈ bad → x.2 ∈ bad
  have hp : MeasurableSet {x | pred x} := by
    have h1 := hbad.preimage
      (show Measurable (fun x : (Finset.Iic N → H) × H => x.1 ⟨N,Finset.mem_Iic.mpr le_rfl⟩) by fun_prop)
    have h2 := hbad.preimage (measurable_snd : Measurable (Prod.snd : (Finset.Iic N → H) × H → H))
    convert h1.compl.union h2 using 1
    ext x
    simp only [pred,mem_setOf_eq,mem_union,mem_compl_iff,Set.mem_preimage]
    tauto
  have hh : ∀ᵐ x ∂((path initial step).map (frestrictLe N) ⊗ₘ historyStep step N),pred x := by
    apply Measure.ae_compProd_of_ae_ae hp
    apply Filter.Eventually.of_forall
    intro h
    rw [historyStep,Kernel.comp_deterministic_eq_comap,Kernel.comap_apply]
    by_cases hb : h ⟨N,Finset.mem_Iic.mpr le_rfl⟩ ∈ bad
    · exact (absorb N _ hb).mono (fun _ hb' => fun _ => hb')
    · exact Filter.Eventually.of_forall (fun _ => fun hh => False.elim (hb hh))
  have he := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ => H) (μ₀ := initial) (κ := historyStep step) (a := N)
  change (path initial step).map (frestrictLe N) ⊗ₘ historyStep step N =
    (path initial step).map (fun x => (frestrictLe N x,x (N+1))) at he
  rw [he] at hh
  exact (ae_map_iff (by fun_prop) hp).mp hh

theorem path_absorbing (initial : Measure H) [IsProbabilityMeasure initial]
    (step : ℕ → Kernel H H) [∀ t,IsMarkovKernel (step t)]
    (bad : Set H) (hbad : MeasurableSet bad)
    (absorb : ∀ t h,h ∈ bad → ∀ᵐ h' ∂step t h,h' ∈ bad) :
    ∀ᵐ omega ∂path initial step,∀ N,omega N ∈ bad → omega (N+1) ∈ bad := by
  exact ae_all_iff.mpr (fun N => path_step_absorbing initial step bad hbad absorb N)

/-- The uniform finite-time bound becomes an anytime bound on the actual path.
Both the marginal laws and almost-sure absorption are derived here. -/
theorem anytime_from_actual_marginals (initial : Kernel Unit H) [IsMarkovKernel initial]
    (step : ℕ → Kernel H H) [∀ t,IsMarkovKernel (step t)]
    (bad : Set H) (hbad : MeasurableSet bad)
    (absorb : ∀ t h,h ∈ bad → ∀ᵐ h' ∂step t h,h' ∈ bad)
    (delta : ENNReal) (hbound : ∀ N,trajectory initial step N () bad ≤ delta) :
    path (initial ()) step {omega | ∃ N,omega N ∈ bad} ≤ delta := by
  let P := path (initial ()) step
  let good := {omega : ℕ → H | ∀ N,omega N ∈ bad → omega (N+1) ∈ bad}
  let F := fun N => {omega : ℕ → H | omega ∈ good ∧ omega N ∈ bad}
  have hg : ∀ᵐ omega ∂P,omega ∈ good := path_absorbing (initial ()) step bad hbad absorb
  have hmono : Monotone F := by
    apply monotone_nat_of_le_succ
    intro t omega hw
    exact ⟨hw.1,hw.1 t hw.2⟩
  have he : {omega | ∃ N,omega N ∈ bad} =ᵐ[P] ⋃ N,F N := by
    filter_upwards [hg] with omega hw
    simp [F,hw]
  rw [show path (initial ()) step=P from rfl,measure_congr he,hmono.measure_iUnion]
  apply iSup_le
  intro N
  have hm := (actual_path_marginals initial step N).measure_eq (p := fun h => h ∈ bad) hbad
  exact (measure_mono (show F N ⊆ {omega | omega N ∈ bad} from fun _ h => h.2)).trans
    (hm.le.trans (hbound N))

#print axioms path_step_absorbing
#print axioms path_absorbing
#print axioms anytime_from_actual_marginals
end
end CIGAMF.P13.AdaptivePathAbsorption
