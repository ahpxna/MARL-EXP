import «LeanD6RandomLabelPhaseRegretV1»
import «LeanD6DiscoveryWorldRecommendationV1»

/-! An actual unknown-label one-epoch phase-III allocation bound. Discovery
and cyclic observations are generated on a canonical product probability space.
Both the label-error probability and the margin-estimator law are discharged.
The recommendation never takes true A as an input. This does not assert an
optimal total budget split, matching regret, or a full stopping/Gamma theorem. -/
namespace CIGAMF.P13.D6ActualUnknownLabelPhaseRisk
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6PhaseThreePrimal
open CIGAMF.P13.D6AllocationPhaseThreeParameters CIGAMF.P13.D6AllocationPhaseThreeFeasible
open CIGAMF.P13.D6AllocationMarginRegion CIGAMF.P13.D6UniformPhaseThreeRemainder
open CIGAMF.P13.D6CyclicMeanSquare CIGAMF.P13.D6CyclicPhaseLaw
open CIGAMF.P13.D6ActualDiscoveryBridge CIGAMF.P13.D6DiscoveryVectorCertificate
open CIGAMF.P13.D6DiscoveryStopping CIGAMF.P13.D6RepeatedDiscovery
open CIGAMF.P13.D6DiscoveryWorldRecommendation CIGAMF.P13.D6RandomLabelPhaseRegret
noncomputable section

/-- True A appears only in evaluation of regret, not in the chosen allocation. -/
def epochLoss (q : ℕ) (j : I (2*q+1)) (fallback A : Finset (I (2*q+1)))
    (mu : ℝ) (r L : ℕ)
    (x : Sample (Off j) × (Fin L × ZMod (2*q+1) → ℝ)) : ℝ :=
  let W := candidate q j fallback r x.1
  oracleRegret A j q mu (D6PhaseThreePrimal.queries W j)
    (weights W j q (mass q (clip (marginMax q) (marginHigh q)
      (estimate (C:=ZMod (2*q+1)) q L x.2))))

/-- For fixed q, C(q) is uniform over phase III. The two terms respectively
charge learning mu and every wrong/missing-label event, including fallback.
Raw information-acquisition cost is 4*(2q+1)*r0*(s+1)+(2q+1)*L queries. -/
theorem actual_unknown_label_phase_bound (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1)) :
    ∃ (G : ZMod (2*q+1) → Finset (I (2*q+1))) (C : ℝ),
      0 ≤ C ∧ (∀ t,Legal j q (.inr (G t,false)) ∧ (G t).card=q) ∧
      ∀ (fallback : Finset (I (2*q+1))) (hf : fallback ∈ worlds q j)
        (a : Off j) (helper : Off j → Off j)
        (ha : ∀ i,a ≠ helper i) (hi : ∀ i,i ≠ helper i)
        (A : Finset (I (2*q+1))) (hA : A ∈ worlds q j)
        (mu : ℝ) (hm : mu ∈ phaseInterval q)
        (r0 : ℕ) (hr0 : 512 ≤ r0) (s L : ℕ) (hL : 0 < L),
        (∫⁻ x,ENNReal.ofReal (epochLoss q j fallback A mu (epochSamples r0 s) L x)
          ∂((vectorPath (means A j a helper mu)).prod (observations G A j mu L))) ≤
          ENNReal.ofReal C*ENNReal.ofReal (((2*q+1:ℕ):ℝ)/((L:ℝ)*(q:ℝ)^4))+
            ENNReal.ofReal (max 0 (oracleValue A j q mu))*
              (eta (Fintype.card (Off j)) r0*(4⁻¹:ℝ≥0∞)^s) := by
  obtain ⟨G,hG,hlaw⟩ := actual_design_law_exists q hq j
  obtain ⟨C,hC,hbound⟩ := random_label_expected_regret q hq
  refine ⟨G,C,hC,hG,?_⟩
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
    exact candidate_correct_on_good q hq j fallback A hA a _ x.1 hx
  have hh := hbound P j A hA mu hm X _ hX
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

#print axioms actual_unknown_label_phase_bound
end
end CIGAMF.P13.D6ActualUnknownLabelPhaseRisk
