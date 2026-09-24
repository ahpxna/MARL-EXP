import «LeanPaperAActualDecisionBridgeV1»
import «LeanPaperAStoppingV1»

/-!
ENDGAME ASSEMBLY. Compiles clean; axioms are {propext, Classical.choice, Quot.sound}. Compiling is NOT the endpoint: the named obligations below are still uninstantiated where marked. This file is downstream of the earlier batch.
It does not re-prove the learner recursion, its tail, or the Gaussian RN derivative.

NEW assembly: strict alternatives + ALL allocations + actual response means; the separation
is therefore between optimized games on ONE centered compression class. The Gaussian KL
identification is an explicit UNDISCHARGED interface below, not an axiom or a proved model
bridge. A worker must instantiate it from the previous batch before citing actual_kl_separation.
The final operational target fixes r and M BEFORE delta tends to zero. No joint-limit or
finite-alpha assertion is obtained merely from these bounds.
-/
namespace CIGAMF.P13.PaperAEndgame
open Finset MeasureTheory ProbabilityTheory InformationTheory Filter
open CIGAMF.P13.PaperARPair CIGAMF.P13.PaperACentred
open CIGAMF.P13.PaperAStrict CIGAMF.P13.PaperAActualDecisionBridge
variable {r : ℕ}

/-- The separating family really has ONE correct compression answer at epsilon=0.
This discharges the max-over-correct-answers issue at this family; it does not assert
uniqueness for every world of the model. -/
theorem family_unique_answer (r : ℕ) :
    actualLossA (thetaC r)=1/8 ∧ actualLossB (thetaC r)=1/2 := by
  have hA : rangeA (thetaC r)=1 := by
    simp [rangeA,thetaC_0,thetaC_1]; norm_num
  have hB : rangeB (thetaC r)=1/4 := by
    have hhi : (BCells r).sup' (BCells_nonempty r) (thetaC r)=1/8 := by
      apply le_antisymm
      · exact Finset.sup'_le _ _ (fun e he => (thetaC_bcell_bound r e he).2)
      · have hmem : (Sum.inl 3 : Cell r) ∈ BCells r := by
          rw [BCells, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, rfl⟩
        have hle := Finset.le_sup' (thetaC r) hmem
        rwa [thetaC_3] at hle
    have hlo : (BCells r).inf' (BCells_nonempty r) (thetaC r)= -(1/8) := by
      apply le_antisymm
      · have hge := Finset.inf'_le (thetaC r) (bAnchor_mem r)
        rwa [thetaC_2] at hge
      · exact Finset.le_inf' _ _ (fun e he => (thetaC_bcell_bound r e he).1)
    unfold rangeB; rw [hhi,hlo]; norm_num
  rw [actualLossA_eq _ (thetaC_mem_centred r), actualLossB_eq _ (thetaC_mem_centred r),hA,hB]
  norm_num

/-- Move the strict witness to its boundary from INSIDE the bad-answer set. -/
theorem strict_design_upper (M : ℝ) (hM : 0 < M) (hr : 0 < r) [NeZero r]
    (w : Cell r → ℝ) (hw : IsAlloc w) :
    trueValueStrict M w ≤ 1 / (8*M*(r:ℝ)) := by
  obtain ⟨j,hj⟩ := exists_light_pair_le r hr (pairWeight w) 1
    (sum_pairWeight_le_one w hw)
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  apply le_of_forall_pos_le_add
  intro ε hε
  let d := min 1 (2*M*(r:ℝ)*ε)/2
  have hd : 0 < d := div_pos (lt_min one_pos (by positivity)) (by norm_num)
  have hd1 : d ≤ 1/2 := by dsimp [d]; linarith [min_le_left 1 (2*M*(r:ℝ)*ε)]
  have hdε : 2*d ≤ 2*M*(r:ℝ)*ε := by
    dsimp [d]; linarith [min_le_right 1 (2*M*(r:ℝ)*ε)]
  have hshift := trueValueStrict_le_shift M hM w hw.1 j d hd
  have hmono : pairWeight w j*(1/2+d)^2/(2*M)
      ≤ (1/2+d)^2/(2*M*(r:ℝ)) := by
    have := mul_le_mul_of_nonneg_right hj (sq_nonneg (1/2+d))
    apply (div_le_div_of_nonneg_right this (by positivity)).trans_eq
    field_simp
    try ring
  have hsmall : (1/2+d)^2/(2*M*(r:ℝ)) ≤ 1/(8*M*(r:ℝ))+ε := by
    rw [div_le_iff₀ (by positivity)]
    have heq : (1/(8*M*(r:ℝ))+ε)*(2*M*(r:ℝ)) = 1/4+2*M*(r:ℝ)*ε := by
      field_simp; ring
    rw [heq]
    nlinarith [sq_nonneg d]
  exact hshift.trans (hmono.trans hsmall)

theorem strict_game_bounds (M : ℝ) (hM : 0 < M) (hr : 0 < r) [NeZero r] :
    9/(128*(4+2*(r:ℝ)*M)) ≤ trueGameStrict r M ∧
    trueGameStrict r M ≤ 1/(8*M*(r:ℝ)) := by
  have hb : BddAbove (Set.range (fun w : {w : Cell r → ℝ // IsAlloc w} =>
      trueValueStrict M (w : Cell r → ℝ))) := by
    refine ⟨1/(8*M*(r:ℝ)), ?_⟩
    rintro _ ⟨w,rfl⟩
    exact strict_design_upper M hM hr w.val w.property
  constructor
  · exact (trueValueStrict_wCert_ge r M hM).trans
      (le_ciSup hb ⟨wCert r M, wCert_isAlloc r M hM⟩)
  · exact ciSup_le (fun w => strict_design_upper M hM hr w.val w.property)

/-- The separation survives STRICT bad answers and optimization of BOTH designs. -/
theorem strict_optimized_separation (M : ℝ) (hM : 0 < M) (hr : 0 < r) [NeZero r] :
    4/(4+2*(r:ℝ)*M) ≤ trueGameStrict r M / frozenGameC₀ r M ∧
    trueGameStrict r M / frozenGameC₀ r M ≤ 64/(9*M*(r:ℝ)) := by
  obtain ⟨hlo,hhi⟩ := strict_game_bounds M hM hr
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hrne : (r:ℝ) ≠ 0 := ne_of_gt hrR
  have hMne : M ≠ 0 := ne_of_gt hM
  have hdne : (4 + 2*(r:ℝ)*M) ≠ 0 := by positivity
  rw [frozenGameC₀_eq r M hM]
  constructor
  · rw [le_div_iff₀ (by norm_num : (0:ℝ) < 9/512)]
    have heq : 4/(4+2*(r:ℝ)*M) * (9/512) = 9/(128*(4+2*(r:ℝ)*M)) := by
      field_simp
      try ring
    rw [heq]; exact hlo
  · rw [div_le_iff₀ (by norm_num : (0:ℝ) < 9/512)]
    have heq : 64/(9*M*(r:ℝ)) * (9/512) = 1/(8*M*(r:ℝ)) := by
      field_simp
      try ring
    rw [heq]; exact hhi

/-- Explicit quantifiers: for EVERY accuracy factor, SOME finite unit-variance family
violates that factor. This is not an asymptotic statement at a frozen design. -/
theorem no_uniform_proxy_factor : ∀ ε : ℝ, 0 < ε → ∃ r : ℕ, 0 < r ∧
    0 < trueGameStrict r 1 ∧ trueGameStrict r 1 / frozenGameC₀ r 1 < ε := by
  intro ε hε
  obtain ⟨r,hr⟩ := exists_nat_gt (max 1 (64/(9*ε)))
  have hr1 : (1:ℝ) < r := (le_max_left _ _).trans_lt hr
  have hr0 : 0 < r := by exact_mod_cast (lt_trans zero_lt_one hr1)
  have : NeZero r := ⟨Nat.ne_of_gt hr0⟩
  have hrR : (0:ℝ) < (r:ℝ) := lt_trans zero_lt_one hr1
  refine ⟨r,hr0,?_,?_⟩
  · exact lt_of_lt_of_le (by positivity) (strict_game_bounds (r:=r) 1 (by norm_num) hr0).1
  · have hsep := (strict_optimized_separation (r:=r) 1 (by norm_num) hr0).2
    have hlarge : 64/(9*ε) < (r:ℝ) := (le_max_right _ _).trans_lt hr
    have hsmall : 64/(9*1*(r:ℝ)) < ε := by
      have h9 : (9:ℝ)*1*(r:ℝ) = 9*(r:ℝ) := by ring
      rw [h9, div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ (by positivity : (0:ℝ) < 9*ε)).mp hlarge
      nlinarith
    exact hsep.trans_lt hsmall

noncomputable def familyVariance (r : ℕ) (M : ℝ) (hM : 0 < M) : Cell r → NNReal :=
  fun e => ⟨pairVar M e, (pairVarC_pos M hM e).le⟩

/-- OPEN upstream obligation. Include finiteness: toReal alone must NOT hide KL=top. -/
def GaussianKLIdentification (r : ℕ) (M : ℝ) (hM : 0 < M) : Prop :=
  ∀ θ lam : Cell r → ℝ, θ ∈ Centred r → lam ∈ Centred r → ∀ e,
    let K := klDiv (observationLaw (familyVariance r M hM) θ e)
      (observationLaw (familyVariance r M hM) lam e)
    K ≠ ⊤ ∧ K.toReal = gaussKL (θ e) (lam e) (pairVar M e)

noncomputable def actualKLValue (M : ℝ) (hM : 0 < M) (w : Cell r → ℝ) : ℝ :=
  sInf ((fun lam => ∑ e, w e * (klDiv
    (observationLaw (familyVariance r M hM) (thetaC r) e)
    (observationLaw (familyVariance r M hM) lam e)).toReal) ''
      {lam : Cell r → ℝ | ActualBadA 0 lam ∧ lam ∈ Centred r})

noncomputable def actualKLGame (r : ℕ) (M : ℝ) (hM : 0 < M) : ℝ :=
  ⨆ w : {w : Cell r → ℝ // IsAlloc w}, actualKLValue M hM w.val

/-- The per-cell identification, summed against a design: the weighted observation
divergence IS the `energy` the strict game optimises. Stated separately because the two
sides differ only after the identification is applied cell by cell. -/
theorem kl_sum_eq_energy (M : ℝ) (hM : 0 < M)
    (hKL : GaussianKLIdentification r M hM) (w lam : Cell r → ℝ)
    (hlam : lam ∈ Centred r) :
    ∑ e, w e * (klDiv (observationLaw (familyVariance r M hM) (thetaC r) e)
      (observationLaw (familyVariance r M hM) lam e)).toReal
      = energy w (pairVar M) (thetaC r) lam := by
  rw [energy_eq_sum_gaussKL]
  refine Finset.sum_congr rfl fun e _ => ?_
  obtain ⟨-, h2⟩ := hKL (thetaC r) lam (thetaC_mem_centred r) hlam e
  rw [h2]

/-- CONDITIONAL model join: hKL must be instantiated, not passed by a new headline axiom. -/
theorem actualKLValue_eq (M : ℝ) (hM : 0 < M)
    (hKL : GaussianKLIdentification r M hM) (w : Cell r → ℝ) :
    actualKLValue M hM w = trueValueStrict M w := by
  unfold actualKLValue trueValueStrict
  apply congrArg sInf
  ext z
  constructor
  · rintro ⟨lam,⟨hbad,hc⟩,rfl⟩
    refine ⟨⟨lam,?_⟩,?_⟩
    · rw [← actual_strict_alternative_eq]; exact ⟨hbad,hc⟩
    · exact (kl_sum_eq_energy M hM hKL w lam hc).symm
  · rintro ⟨lam,rfl⟩
    have hmem : lam.val ∈ {x : Cell r → ℝ | ActualBadA 0 x ∧ x ∈ Centred r} := by
      rw [actual_strict_alternative_eq]; exact lam.property
    exact ⟨lam.val,hmem,kl_sum_eq_energy M hM hKL w lam.val hmem.2⟩

theorem actualKLGame_eq (M : ℝ) (hM : 0 < M)
    (hKL : GaussianKLIdentification r M hM) : actualKLGame r M hM = trueGameStrict r M := by
  unfold actualKLGame trueGameStrict
  congr 1; funext w; exact actualKLValue_eq M hM hKL w.val

/-- Actual compression information, after both optimizations, not merely a witness cost. -/
theorem actual_kl_separation (M : ℝ) (hM : 0 < M) (hr : 0 < r) [NeZero r]
    (hKL : GaussianKLIdentification r M hM) :
    4/(4+2*(r:ℝ)*M) ≤ actualKLGame r M hM / frozenGameC₀ r M ∧
    actualKLGame r M hM / frozenGameC₀ r M ≤ 64/(9*M*(r:ℝ)) := by
  rw [actualKLGame_eq M hM hKL]
  exact strict_optimized_separation M hM hr

/-- The optimized surrogate does not merely misestimate the value: every exact surrogate
optimizer has ZERO actual information, although the actual optimized game is positive.
This is about information under the fixed design, not a claim that an algorithm with forced
exploration never stops. -/
theorem proxy_optimizer_misses_actual_information (M : ℝ) (hM : 0 < M) (hr : 0 < r) [NeZero r]
    (hKL : GaussianKLIdentification r M hM) :
    0 < actualKLGame r M hM ∧ ∀ w : Cell r → ℝ, IsAlloc w →
      frozenValueC₀ M w=frozenGameC₀ r M → actualKLValue M hM w=0 := by
  constructor
  · rw [actualKLGame_eq M hM hKL]
    exact lt_of_lt_of_le (by positivity) (strict_game_bounds M hM hr).1
  · intro w hw hopt
    rw [actualKLValue_eq M hM hKL]
    apply frozen_optimum_trueValueStrict_zero M hM r hr w hw
    rw [hopt,frozenGameC₀_eq r M hM]

/-! Operational endpoint. The two one-sided obligations below are outputs of the previous
batch (actual learner analysis and actual multiple-answer lower bound). This section assembles
them; it does not claim to discharge them, and N must be the expected UNTRUNCATED hitting time. -/
def EventuallyAtZero (P : ℝ → Prop) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ, 0 < δ → δ < min δ₀ 1 → P δ

def UpperRate (N : ℝ → ℝ) (Γ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → EventuallyAtZero (fun δ => N δ / Real.log (1/δ) ≤ 1/Γ+ε)

def LowerRate (N : ℝ → ℝ) (Γ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → EventuallyAtZero (fun δ => 1/Γ-ε ≤ N δ / Real.log (1/δ))

theorem exact_rate_of_endpoints (N : ℝ → ℝ) (Γ : ℝ)
    (hU : UpperRate N Γ) (hL : LowerRate N Γ) :
    ∀ ε : ℝ, 0 < ε → EventuallyAtZero
      (fun δ => |N δ / Real.log (1/δ)-1/Γ| ≤ ε) := by
  intro ε hε
  obtain ⟨u,hu,hU⟩ := hU ε hε
  obtain ⟨l,hl,hL⟩ := hL ε hε
  refine ⟨min u l,lt_min hu hl,?_⟩
  intro δ hδ hd
  have hdu : δ < min u 1 := lt_min ((lt_min_iff.mp hd).1.trans_le (min_le_left _ _))
    (lt_min_iff.mp hd).2
  have hdl : δ < min l 1 := lt_min ((lt_min_iff.mp hd).1.trans_le (min_le_right _ _))
    (lt_min_iff.mp hd).2
  exact abs_le.mpr ⟨by linarith [hL δ hδ hdl],by linarith [hU δ hδ hdu]⟩

/-- Remaining FINAL target, not asserted as a theorem. The expectation is ENNReal until its
finiteness has been established. μ and τ must be the concrete protocol from the previous batch. -/
def OperationalFinish {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (τ : ℝ → Ω → ℕ∞) (Γ : ℝ) : Prop :=
  0 < Γ ∧
  (∀ δ, 0 < δ → δ < 1 → (∫⁻ ω, (τ δ ω).toENNReal ∂μ) ≠ ⊤) ∧
  ∀ ε, 0 < ε → EventuallyAtZero (fun δ =>
    |(∫⁻ ω, (τ δ ω).toENNReal ∂μ).toReal / Real.log (1/δ) - 1/Γ| ≤ ε)

/-- Concrete-family terminal assembly. hUpper and hLower are the obligations from the
previous batch, and hfinite must concern the untruncated ENat hitting time. This theorem
binds their rate to the ACTUAL KL game, not to a supplied unrelated scalar Gamma. -/
theorem family_operational_finish {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (τ : ℝ → Ω → ℕ∞) (M : ℝ) (hM : 0 < M) (hr : 0 < r) [NeZero r]
    (hKL : GaussianKLIdentification r M hM)
    (hfinite : ∀ δ, 0 < δ → δ < 1 → (∫⁻ ω,(τ δ ω).toENNReal ∂μ) ≠ ⊤)
    (hUpper : UpperRate (fun δ => (∫⁻ ω,(τ δ ω).toENNReal ∂μ).toReal) (actualKLGame r M hM))
    (hLower : LowerRate (fun δ => (∫⁻ ω,(τ δ ω).toENNReal ∂μ).toReal) (actualKLGame r M hM)) :
    OperationalFinish μ τ (actualKLGame r M hM) := by
  refine ⟨?_,hfinite,exact_rate_of_endpoints _ _ hUpper hLower⟩
  rw [actualKLGame_eq M hM hKL]
  exact lt_of_lt_of_le (by positivity) (strict_game_bounds M hM hr).1

#print axioms family_unique_answer
#print axioms family_operational_finish
#print axioms strict_game_bounds
#print axioms strict_optimized_separation
#print axioms no_uniform_proxy_factor
#print axioms actual_kl_separation
#print axioms proxy_optimizer_misses_actual_information
#print axioms exact_rate_of_endpoints
end CIGAMF.P13.PaperAEndgame
