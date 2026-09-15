import «LeanD6CyclicMeanSquareV1»
import «LeanD6UniformPhaseThreeRemainderV1»
import «LeanD6AdaptiveOracleRegretV1»
import «LeanD6DiscoveryGeometryV1»

/-! Total one-epoch recommendation regret in phase III, including wrong labels.
The label and margin estimate need not be independent. A later bridge supplies
the Gaussian law and bad-label probability from the actual discovery/cyclic
query experiments. This is not a full adaptive stopping-rate theorem. -/
namespace CIGAMF.P13.D6RandomLabelPhaseRegret
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6AdaptiveOracleRegret
open CIGAMF.P13.D6PhaseThreePrimal CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6UniformPhaseThreeRemainder CIGAMF.P13.D6CyclicMeanSquare
noncomputable section

lemma world_others_card (q : ℕ) (hq : 2 ≤ q) (j : I (2*q+1))
    (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j) : (others A j).card=q := by
  have hh := congrArg Finset.card (D6DiscoveryGeometry.encodedB_map A j)
  rw [Finset.card_map,D6DiscoveryGeometry.model_card q j hq A hA] at hh
  exact hh.symm

/-- The constant is proved to exist from the explicit phase-III geometry.
`hcorrect` specifies the decoder's behavior; it is not a regret premise.
The bad-label contribution is retained at its full loss scale. -/
theorem random_label_expected_regret (q : ℕ) (hq : 3 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (j : I (2*q+1)) (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j)
      (mu : ℝ) (hm : mu ∈ phaseInterval q)
      (X : Ω → ℝ) (v : NNReal) (hX : HasLaw X (gaussianReal mu v) P)
      (candidate : Ω → Finset (I (2*q+1)))
      (hcan : ∀ x,candidate x ∈ worlds q j)
      (bad : Set Ω) (hb : MeasurableSet bad)
      (hcorrect : ∀ x,x ∉ bad → candidate x=A),
      (∫⁻ x,ENNReal.ofReal (oracleRegret A j q mu (queries (candidate x) j)
        (weights (candidate x) j q (mass q (clip (marginMax q) (marginHigh q) (X x))))) ∂P) ≤
        ENNReal.ofReal C*ENNReal.ofReal (v:ℝ)+
          ENNReal.ofReal (max 0 (oracleValue A j q mu))*P bad := by
  obtain ⟨C,hC,hquad⟩ := uniform_actual_quadratic q (by exact_mod_cast hq)
  refine ⟨C,hC,?_⟩
  intro Ω inst P j A hA mu hm X v hX candidate hcan bad hb hcorrect
  let z : Ω → ℝ := fun x => clip (marginMax q) (marginHigh q) (X x)
  let loss : Ω → ℝ := fun x => oracleRegret A j q mu (queries (candidate x) j)
    (weights (candidate x) j q (mass q (z x)))
  let M : ℝ := max 0 (oracleValue A j q mu)
  have hz : ∀ x,z x ∈ phaseInterval q := fun x => clip_mem _ _ _ (hm.1.trans hm.2)
  have hparams := world_parameters q j (by omega) hA
  have ha : (A.card:ℝ)=(q:ℝ)+1 := by exact_mod_cast hparams.2.1
  have hB : ((others A j).card:ℝ)=(q:ℝ) := by exact_mod_cast world_others_card q (by omega) j A hA
  have hpoint : ∀ x,ENNReal.ofReal (loss x) ≤
      ENNReal.ofReal C*ENNReal.ofReal ((z x-mu)^2)+
        bad.indicator (fun _ => ENNReal.ofReal M) x := by
    intro x
    by_cases hx : x ∈ bad
    · rw [Set.indicator_of_mem hx]
      have hc := world_parameters q j (by omega) (hcan x)
      have hw := phase_mass_bounds q (z x) (by exact_mod_cast hq) (hz x).1 (hz x).2
      have hp := distribution (candidate x) j q (mass q (z x)) (by exact_mod_cast (show 0<q by omega))
        hw.1 (by linarith [hw.2]) (by exact_mod_cast world_others_card q (by omega) j (candidate x) (hcan x))
      have hh := oracle_regret_bounded A j q mu (queries (candidate x) j)
        (weights (candidate x) j q (mass q (z x))) (fun e _ => hp.2.1 e)
      exact (ENNReal.ofReal_le_ofReal hh).trans (le_add_left le_rfl)
    · rw [Set.indicator_of_notMem hx,add_zero,← ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      dsimp only [loss]
      rw [hcorrect x hx]
      exact hquad A j mu (z x) hm (hz x) hparams.1 ha hB
  have hzmeas : AEMeasurable z P := by dsimp [z,clip];fun_prop
  have hmse := clipped_mean_square hX hm.1 hm.2
  calc
    _ ≤ ∫⁻ x,ENNReal.ofReal C*ENNReal.ofReal ((z x-mu)^2)+
          bad.indicator (fun _ => ENNReal.ofReal M) x ∂P := lintegral_mono hpoint
    _ = ENNReal.ofReal C*(∫⁻ x,ENNReal.ofReal ((z x-mu)^2) ∂P)+
          ENNReal.ofReal M*P bad := by
      rw [lintegral_add_left' (by fun_prop),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator_const hb]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left hmse (show 0 ≤ ENNReal.ofReal C from zero_le)) le_rfl

#print axioms random_label_expected_regret
end
end CIGAMF.P13.D6RandomLabelPhaseRegret
