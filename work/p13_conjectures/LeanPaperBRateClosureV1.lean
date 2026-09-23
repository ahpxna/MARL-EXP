import «LeanPaperBEndgameV1»

/-!
DRAFT ENDGAME — not compiled. This is the final uniform-rate join, downstream of the
already-assigned continuous transcript and actual decoder proofs. It does not reprove
those upstream steps or substitute a discrete experiment for the Gaussian experiment.

A UniformProtocolCertificate is a named OPEN input. Its lower component must be derived
from the actual stopped transcript law and unsafe-obstruction argument; its upper component
must be the actual implementable decoder on the SAME Experiment. The theorem below turns
these obligations into the operational minimax rate, with all h/delta quantifiers explicit.
-/
namespace CIGAMF.P13.PaperBRateClosure
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal
open CIGAMF.P13.PaperBEndgame

variable {W A Pol Ω : Type*} [Fintype W] [Nonempty W] [MeasurableSpace Ω]

/-- The lower information cap a*h^(2s) is uniform over ALL allowed adaptive policies.
The decoder may depend on h and delta but NOT on the unknown world.
Constants may depend on the fixed experiment/order; none may depend on h or delta. -/
structure UniformProtocolCertificate (E : Experiment W A Pol Ω) (task : Task) (s : ℕ) where
  a : ℝ
  b : ℝ
  C : ℝ
  h₀ : ℝ
  δ₀ : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  C_pos : 0 < C
  h₀_pos : 0 < h₀
  δ₀_pos : 0 < δ₀
  δ₀_lt_one : δ₀<1
  lower : ∀ h δ, 0 < h → h ≤ h₀ → 0 < δ → δ ≤ δ₀ →
    HardPairCertificate E task h δ (ENNReal.ofReal (a*h^(2*s)))
      (ENNReal.ofReal (b*Real.log (1/δ)))
  upper : ∀ h δ, 0 < h → h ≤ h₀ → 0 < δ → δ ≤ δ₀ →
    DecoderWitness E task h δ (ENNReal.ofReal (C*scale h δ s))

/-- A deterministic fixed-budget decoder can fill the upper interface directly. The cost
counts every sample in every test. Its correctness proof is still an upstream obligation. -/
noncomputable def decoder_of_pointwise_budget (E : Experiment W A Pol Ω) (task : Task)
    (h δ : ℝ) (B : ℕ) (π : Pol) (hc : Correct E task h δ π)
    (hb : ∀ w, ∀ᵐ ω ∂E.law h π w, E.tau π ω ≤ (B : ℕ∞)) :
    DecoderWitness E task h δ (B : ℝ≥0∞) := by
  refine ⟨π,hc,?_⟩
  intro w
  letI := E.probability h π w
  calc costAt E h π w ≤ ∫⁻ _ω, (B : ℝ≥0∞) ∂E.law h π w := by
        apply lintegral_mono_ae
        filter_upwards [hb w] with ω hω
        exact_mod_cast hω
    _ = (B : ℝ≥0∞) := by simp

/-- Absorb rounding/test-count constants honestly when installing the upper witness. -/
noncomputable def enlarge_decoder_budget (E : Experiment W A Pol Ω) (task : Task) (h δ : ℝ)
    (B B' : ℝ≥0∞) (hB : B ≤ B') (U : DecoderWitness E task h δ B) :
    DecoderWitness E task h δ B' :=
  ⟨U.code,U.correct,fun w => (U.cost w).trans hB⟩

/-- Converts the lower certificate to the claimed REAL scaling before embedding in
ENNReal. In particular KL=top or expectation=top cannot silently become real zero. -/
lemma information_quotient (a b h δ : ℝ) (s : ℕ) (ha : 0 < a) (hh : 0 < h) :
    ENNReal.ofReal (b*Real.log (1/δ))/ENNReal.ofReal (a*h^(2*s)) =
      ENNReal.ofReal ((b/a)*scale h δ s) := by
  rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < a*h^(2*s))]
  congr 1
  unfold scale
  field_simp
  try ring

/-- The operational minimax rate for the whole policy class, not just one decoder and
not a numerical slope. This is a conditional downstream assembly until P is instantiated. -/
theorem hasRate_from_protocol (E : Experiment W A Pol Ω) (task : Task) (s : ℕ)
    (P : UniformProtocolCertificate E task s) : HasRate E task s := by
  refine ⟨P.b/P.a,P.C,P.h₀,P.δ₀,div_pos P.b_pos P.a_pos,P.C_pos,
    P.h₀_pos,P.δ₀_pos,P.δ₀_lt_one,?_⟩
  intro h δ hh hh₀ hδ hδ₀
  have hi0 : ENNReal.ofReal (P.a*h^(2*s)) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos P.a_pos (by positivity)))
  have hiTop : ENNReal.ofReal (P.a*h^(2*s))≠⊤ := ENNReal.ofReal_ne_top
  have hbounds := minimax_sandwich E task h δ _ _ _ hi0 hiTop
    (P.lower h δ hh hh₀ hδ hδ₀) (P.upper h δ hh hh₀ hδ hδ₀)
  rw [information_quotient P.a P.b h δ s P.a_pos hh] at hbounds
  exact hbounds

/-- The two rates must share the SAME E, policy class and sample-count convention. -/
theorem separated_tasks_from_protocols (E : Experiment W A Pol Ω) (s r : ℕ)
    (hsr : s < r) (P : UniformProtocolCertificate E .safe s)
    (Q : UniformProtocolCertificate E .identify r) : SeparatedTasksFinish E s r :=
  ⟨hsr,hasRate_from_protocol E .safe s P,hasRate_from_protocol E .identify r Q⟩

/-- Restricting to a COMMON h/delta rectangle is necessary before comparing the rates.
The constants remain uniform on that rectangle; there is no hidden h-dependent decoder cost. -/
theorem common_rate_rectangle (E : Experiment W A Pol Ω) (s r : ℕ)
    (P : UniformProtocolCertificate E .safe s)
    (Q : UniformProtocolCertificate E .identify r) :
    ∀ h δ, 0 < h → h ≤ min P.h₀ Q.h₀ → 0 < δ → δ ≤ min P.δ₀ Q.δ₀ →
      complexity E .safe h δ ≤ ENNReal.ofReal (P.C*scale h δ s) ∧
      ENNReal.ofReal ((Q.b/Q.a)*scale h δ r) ≤ complexity E .identify h δ := by
  intro h δ hh hh₀ hδ hδ₀
  have hPh := hh₀.trans (min_le_left _ _)
  have hQh := hh₀.trans (min_le_right _ _)
  have hPδ := hδ₀.trans (min_le_left _ _)
  have hQδ := hδ₀.trans (min_le_right _ _)
  constructor
  · let U := P.upper h δ hh hPh hδ hPδ
    exact (iInf_le _ ⟨U.code,U.correct⟩).trans (iSup_le U.cost)
  · have hi0 : ENNReal.ofReal (Q.a*h^(2*r)) ≠ 0 := by
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos Q.a_pos (by positivity)))
    have hbounds := minimax_sandwich E .identify h δ _ _ _ hi0 ENNReal.ofReal_ne_top
      (Q.lower h δ hh hQh hδ hQδ) (Q.upper h δ hh hQh hδ hQδ)
    rw [information_quotient Q.a Q.b h δ r Q.a_pos hh] at hbounds
    exact hbounds.1

/-- Full terminal join for the concrete support task. hloss ties the decoder's answer to
selectedRadius; the two protocol certificates supply the statistical content, separately.
Nothing here asserts an order law for arbitrary families or for another observation channel. -/
theorem tip_finish_from_protocols (m : ℕ) (hm : 3 ≤ m)
    (E : Experiment (Fin m) (Fin m) Pol Ω)
    (hloss : ∀ w a,E.loss w a=tipLoss m w a)
    (hε : 0 ≤ E.tolerance) (hεmax : E.tolerance < ((m:ℝ)-1)/2)
    (P : UniformProtocolCertificate E .safe 1)
    (Q : UniformProtocolCertificate E .identify (m-1)) : TipFinish m hm E := by
  haveI : NeZero m := ⟨by omega⟩
  exact ⟨hloss,hε,hεmax,separated_tasks_from_protocols E 1 (m-1) (by omega) P Q⟩

#print axioms decoder_of_pointwise_budget
#print axioms information_quotient
#print axioms hasRate_from_protocol
#print axioms separated_tasks_from_protocols
#print axioms common_rate_rectangle
#print axioms tip_finish_from_protocols
end CIGAMF.P13.PaperBRateClosure
