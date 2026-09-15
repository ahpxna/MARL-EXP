import «LeanD6ActualUnknownLabelPhaseRiskV1»
import «LeanD6GrowingPhaseThreeRemainderV1»

/-! Growing-q quantitative regret for an actual unknown-A recommendation in
phase III. No unknown C(q) remains: the estimation term is 64*(2q+1)/(L*q^6).
The decoder's wrong-label term is charged explicitly. This remains a one-epoch
bound with a known phase-III interval; it is not full adaptive matching. -/
namespace CIGAMF.P13.D6GrowingUnknownLabelPhaseRisk
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6AdaptiveOracleRegret
open CIGAMF.P13.D6PhaseThreePrimal CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6FrozenQuadraticBound CIGAMF.P13.D6UniformPhaseThreeRemainder
open CIGAMF.P13.D6GrowingPhaseThreeRemainder CIGAMF.P13.D6CyclicMeanSquare
open CIGAMF.P13.D6CyclicPhaseLaw CIGAMF.P13.D6ActualDiscoveryBridge
open CIGAMF.P13.D6DiscoveryVectorCertificate CIGAMF.P13.D6DiscoveryStopping
open CIGAMF.P13.D6RepeatedDiscovery CIGAMF.P13.D6DiscoveryWorldRecommendation
open CIGAMF.P13.D6RandomLabelPhaseRegret CIGAMF.P13.D6ActualUnknownLabelPhaseRisk
noncomputable section

lemma scaled_actual_quadratic (q : ℝ) (hq : 8 ≤ q)
    {n : ℕ} (A : Finset (I n)) (j : I n) (mu mu0 : ℝ)
    (hm : mu ∈ phaseInterval q) (h0 : mu0 ∈ phaseInterval q)
    (hj : j ∉ A) (hA : (A.card:ℝ)=q+1) (hB : ((others A j).card:ℝ)=q) :
    oracleRegret A j q mu (D6PhaseThreePrimal.queries A j) (weights A j q (mass q mu0)) ≤
      (64/q^2)*(mu0-mu)^2 := by
  have hh := actual_frozen_quadratic_regret A j q mu mu0 |mu-mu0| (by linarith)
    hm.1 hm.2 h0.1 h0.2 hj hA hB (abs_nonneg _) le_rfl
  rw [sq_abs] at hh
  have he : (mu-mu0)^2=(mu0-mu)^2 := by ring
  rw [← he]
  exact hh.trans (mul_le_mul_of_nonneg_right (remainder_scaled q mu0 hq h0) (sq_nonneg _))

theorem random_label_explicit_regret (q : ℕ) (hq : 8 ≤ q) :
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
        ENNReal.ofReal (64/(q:ℝ)^2)*ENNReal.ofReal (v:ℝ)+
          ENNReal.ofReal (max 0 (oracleValue A j q mu))*P bad := by
  let C : ℝ := 64/(q:ℝ)^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hquad := scaled_actual_quadratic (n:=2*q+1) (q:ℝ) (by exact_mod_cast hq)
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
      have hw := phase_mass_bounds q (z x) (by exact_mod_cast (show 3 ≤ q by omega)) (hz x).1 (hz x).2
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


theorem actual_unknown_label_explicit_bound (q : ℕ) (hq : 8 ≤ q) (j : I (2*q+1)) :
    ∃ (G : ZMod (2*q+1) → Finset (I (2*q+1))),
      (∀ t,Legal j q (.inr (G t,false)) ∧ (G t).card=q) ∧
      ∀ (fallback : Finset (I (2*q+1))) (hf : fallback ∈ worlds q j)
        (a : Off j) (helper : Off j → Off j)
        (ha : ∀ i,a ≠ helper i) (hi : ∀ i,i ≠ helper i)
        (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j)
        (mu : ℝ) (hm : mu ∈ phaseInterval q)
        (r0 : ℕ) (hr0 : 512 ≤ r0) (s L : ℕ) (hL : 0 < L),
        (∫⁻ x,ENNReal.ofReal (epochLoss q j fallback A mu (epochSamples r0 s) L x)
          ∂((vectorPath (means A j a helper mu)).prod (observations G A j mu L))) ≤
          ENNReal.ofReal (64/(q:ℝ)^2)*ENNReal.ofReal (((2*q+1:ℕ):ℝ)/((L:ℝ)*(q:ℝ)^4))+
            ENNReal.ofReal (max 0 (oracleValue A j q mu))*
              (eta (Fintype.card (Off j)) r0*(4⁻¹:ℝ≥0∞)^s) := by
  obtain ⟨G,hG,hlaw⟩ := actual_design_law_exists q (by omega) j
  refine ⟨G,hG,?_⟩
  intro fallback hf a helper ha hi A hA mu hm r0 hr0 s L hL
  have hp := world_parameters q j (by omega) hA
  have hcyc := hlaw A hp.1 (world_others_card q (by omega) j A hA) L hL mu
  let P := (vectorPath (means A j a helper mu)).prod (observations G A j mu L)
  letI : IsProbabilityMeasure (observations G A j mu L) := hcyc.isProbabilityMeasure
  let X : Sample (Off j) × (Fin L × ZMod (2*q+1) → ℝ) → ℝ :=
    fun x => estimate (C:=ZMod (2*q+1)) q L x.2
  have hX : HasLaw X _ P := hcyc.comp measurePreserving_snd.hasLaw
  let badSet : Set (Sample (Off j) × (Fin L × ZMod (2*q+1) → ℝ)) :=
    Prod.fst ⁻¹' bad (encodedB A j) a (epochSamples r0 s)
  have hb : MeasurableSet badSet := (bad_measurable _ _ _).preimage measurable_fst
  have hrec : ∀ x,x ∉ badSet → candidate q j fallback (epochSamples r0 s) x.1=A := by
    intro x hx
    exact candidate_correct_on_good q (by omega) j fallback A hA a _ x.1 hx
  have hh := random_label_explicit_regret q hq P j A hA mu hm X _ hX
    (fun x => candidate q j fallback (epochSamples r0 s) x.1)
    (fun x => candidate_valid q j fallback hf _ x.1) badSet hb hrec
  have hbad : P badSet ≤ eta (Fintype.card (Off j)) r0*(4⁻¹:ℝ≥0∞)^s := by
    have hf : HasLaw Prod.fst (vectorPath (means A j a helper mu)) P := measurePreserving_fst.hasLaw
    have he := hf.measure_eq (bad_measurable (encodedB A j) a (epochSamples r0 s))
    change P badSet=vectorPath (means A j a helper mu) (bad (encodedB A j) a (epochSamples r0 s)) at he
    rw [he]
    exact epoch_tail _ _ a (actual_mean_identity A j hp.1 a helper ha hi mu) r0 hr0 s
  have hv : (((((L*(2*q+1):ℕ):NNReal) /
      NNReal.mk (((L:ℝ)*(q:ℝ)^2)^2) (sq_nonneg _)):NNReal):ℝ) =
      ((2*q+1:ℕ):ℝ)/((L:ℝ)*(q:ℝ)^4) := by
    have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hL0 : (L:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
    push_cast
    field_simp
    <;> ring
  rw [hv] at hh
  exact hh.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hbad (show 0 ≤ ENNReal.ofReal (max 0 (oracleValue A j q mu)) from zero_le)))


#print axioms scaled_actual_quadratic
#print axioms random_label_explicit_regret
#print axioms actual_unknown_label_explicit_bound
end
end CIGAMF.P13.D6GrowingUnknownLabelPhaseRisk
