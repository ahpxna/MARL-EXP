import «LeanPaperAGaussianKLV1»
import «LeanPaperALowerGameV1»
import «LeanPaperABridgeDummyV1»

/-!
# Paper A: every finite-horizon policy on the family needs `demand / actualKLGame` queries

The lower half of the operational rate, for the paper's own family and its own game value
`actualKLGame r M` (the one `LeanPaperAEndgameV1.OperationalFinish` names):

* the channel is Paper A's observation law on EVERY cell, with a FRESH dummy
  (`famChan`, over `Cell r ⊕ Unit`, `LeanPaperABridgeDummyV1`): real cell `e` is observed as
  `observationLaw (familyVariance r M) lambda e` in world `lambda` (`obsLaw_fam_real`), the
  dummy carries no information (`klq_dummy`);
* `family_policy_lower` -- a randomised adaptive policy with a finite horizon, whose answer
  event has probability `>= 1 - delta` at `thetaC` and `<= delta` at EVERY strict alternative
  (`TrueAltStrict r`), makes in expectation at least
  `((1 - delta) log(1/delta) - log 2) / actualKLGame r M` queries of real cells.

The alternatives range over the whole unbounded `TrueAltStrict r`; no box is used.  The bound
is `change_of_measure` (`LeanPaperALowerKLV1`) and `count_lower_bound`
(`LeanPaperALowerGameV1`), with the per-query divergences identified with the ones in
`actualKLValue` by `gaussianKLIdentification_holds`.
-/

namespace CIGAMF.P13.PaperAFamilyLower

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperABridge CIGAMF.P13.PaperABridgeDummy
open CIGAMF.P13.PaperAEndgame CIGAMF.P13.PaperAActualDecisionBridge CIGAMF.P13.PaperAStrict
open CIGAMF.P13.PaperACentred CIGAMF.P13.PaperARPair CIGAMF.P13.PaperAGaussianKL

variable {r : ℕ}

/-- The family's standard deviations on the extended query type. -/
noncomputable def famS (M : ℝ) : Cell r ⊕ Unit → ℝ :=
  Sum.elim (fun e => Real.sqrt (pairVar M e)) (fun _ => 1)

theorem famS_pos (M : ℝ) (hM : 0 < M) : ∀ q, 0 < famS (r := r) M q
  | Sum.inl e => Real.sqrt_pos.mpr (pairVarC_pos M hM e)
  | Sum.inr _ => one_pos

/-- **The family's channel**, every cell observed, plus a fresh dummy. -/
noncomputable def famChan (M : ℝ) (hM : 0 < M) :
    Channel (Cell r ⊕ Unit → ℝ) (Cell r ⊕ Unit) :=
  gChan dummyQ (famS M) (famS_pos M hM)

theorem obsLawC_gChan {Q : Type*} [Fintype Q] [DecidableEq Q] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] (d : Q) (s : Q → ℝ) (hs : ∀ q, 0 < s q) (w : Q → ℝ) (q : Q) :
    obsLawC (gChan d s hs) w q = gaussianReal (mz d w q) (vq s q) := by
  rw [gaussianReal_of_var_ne_zero _ (vq_ne_zero s hs q)]
  rfl

theorem vq_famS (M : ℝ) (hM : 0 < M) (e : Cell r) :
    vq (famS (r := r) M) (Sum.inl e) = familyVariance r M hM e := by
  apply NNReal.eq
  show (famS (r := r) M (Sum.inl e)) ^ 2 = pairVar M e
  exact Real.sq_sqrt (pairVarC_pos M hM e).le

/-- **A real cell is observed with the family's own law.** -/
theorem obsLaw_fam_real (M : ℝ) (hM : 0 < M) (lam : Cell r → ℝ) (hc : lam ∈ Centred r)
    (e : Cell r) :
    obsLawC (famChan M hM) (lift lam) (Sum.inl e)
      = observationLaw (familyVariance r M hM) lam e := by
  unfold famChan
  rw [obsLawC_gChan, vq_famS M hM e]
  unfold observationLaw
  rw [queryMean_eq lam hc]
  simp [mz, lift, dummyQ]

/-- The dummy carries no information. -/
theorem klq_dummy {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
    [DecidableEq Q] (C : Channel W Q) (θ l : W) : klq C θ l C.dummy = 0 := by
  unfold klq
  have : obsLawC C θ C.dummy = obsLawC C l C.dummy := by
    unfold obsLawC
    congr 1
    funext y
    rw [C.dummy_same θ l]
  rw [this, klDiv_self]

/-- The value of an allocation is at most the game, for the family. -/
theorem actualKLValue_le_game [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r) (w : Cell r → ℝ)
    (hw : IsAlloc w) : actualKLValue M hM w ≤ actualKLGame r M hM := by
  have hKL := gaussianKLIdentification_holds r M hM
  have hb : BddAbove (Set.range (fun w : {w : Cell r → ℝ // IsAlloc w} =>
      actualKLValue M hM w.val)) := by
    refine ⟨1 / (8 * M * (r : ℝ)), ?_⟩
    rintro _ ⟨w', rfl⟩
    show actualKLValue M hM w'.val ≤ _
    rw [actualKLValue_eq M hM hKL]
    exact strict_design_upper M hM hr w'.val w'.property
  exact le_ciSup hb ⟨w, hw⟩

/-- **The lower bound for every finite-horizon policy on the family.** -/
theorem family_policy_lower [NeZero r] (M : ℝ) (hM : 0 < M) (hr : 0 < r)
    (π : Policy (Cell r ⊕ Unit)) (n : ℕ) (S : Set (Hist (Cell r ⊕ Unit) n))
    (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hθ : 1 - δ ≤ (hist (famChan M hM) π (lift (thetaC r)) n).real S)
    (hl : ∀ lam ∈ TrueAltStrict r, (hist (famChan M hM) π (lift lam) n).real S ≤ δ)
    (hD : 0 < (1 - δ) * Real.log (1 / δ) - Real.log 2) :
    ((1 - δ) * Real.log (1 / δ) - Real.log 2) / actualKLGame r M hM
      ≤ ∑ e : Cell r, (∫⁻ ω, cntQ (Sum.inl e) n ω
          ∂hist (famChan M hM) π (lift (thetaC r)) n).toReal := by
  set C := famChan (r := r) M hM with hC
  set θ := lift (thetaC r) with hθdef
  have hKL := gaussianKLIdentification_holds r M hM
  have hθc := thetaC_mem_centred r
  -- the per-cell divergences are the family's
  have hk : ∀ lam ∈ TrueAltStrict r, ∀ e, klq C θ (lift lam) (Sum.inl e)
      = klDiv (observationLaw (familyVariance r M hM) (thetaC r) e)
          (observationLaw (familyVariance r M hM) lam e) := by
    intro lam hlam e
    unfold klq
    rw [obsLaw_fam_real M hM _ hθc, obsLaw_fam_real M hM lam hlam.2]
  have hfin : ∀ lam ∈ TrueAltStrict r, ∀ q, klq C θ (lift lam) q ≠ ⊤ := by
    intro lam hlam q
    cases q with
    | inl e => rw [hk lam hlam e]; exact (hKL _ _ hθc hlam.2 e).1
    | inr u =>
        have : (Sum.inr u : Cell r ⊕ Unit) = C.dummy := rfl
        rw [this, klq_dummy]; exact ENNReal.zero_ne_top
  have hΓ0 : 0 < actualKLGame r M hM := by
    rw [actualKLGame_eq M hM hKL]
    exact lt_of_lt_of_le (by positivity) (strict_game_bounds M hM hr).1
  obtain ⟨lam0⟩ := instNonemptyTrueAltStrict r
  refine count_lower_bound (TrueAltStrict r) ⟨lam0.val, lam0.property⟩
    (fun e => (∫⁻ ω, cntQ (Sum.inl e) n ω ∂hist C π θ n).toReal)
    (fun e => ENNReal.toReal_nonneg) (fun lam e => (klq C θ (lift lam) (Sum.inl e)).toReal)
    (fun lam e => ENNReal.toReal_nonneg) _ hD (fun lam hlam => ?_) _ hΓ0 (fun w hw => ?_)
  · -- the change of measure at this alternative, the dummy dropped
    have hc := change_of_measure C π θ (lift lam) n S hS δ hδ hδ1 hθ (hl lam hlam)
    have hre := real_of_change _ hD.le _ _ (fun q => lintegral_cntQ_ne_top C π θ q n)
      (hfin lam hlam) hc
    rw [Fintype.sum_sum_type] at hre
    have hdum : ∑ u : Unit, (∫⁻ ω, cntQ (Sum.inr u) n ω ∂hist C π θ n).toReal
        * (klq C θ (lift lam) (Sum.inr u)).toReal = 0 := by
      refine Finset.sum_eq_zero fun u _ => ?_
      have : (Sum.inr u : Cell r ⊕ Unit) = C.dummy := rfl
      rw [this, klq_dummy]
      simp
    linarith
  · -- the value of the allocation is the family's actual value, at most the game
    have hset : (fun lam => ∑ e, w e * (klq C θ (lift lam) (Sum.inl e)).toReal) '' TrueAltStrict r
        = (fun lam => ∑ e, w e * (klDiv (observationLaw (familyVariance r M hM) (thetaC r) e)
            (observationLaw (familyVariance r M hM) lam e)).toReal) ''
          {lam : Cell r → ℝ | ActualBadA 0 lam ∧ lam ∈ Centred r} := by
      rw [actual_strict_alternative_eq]
      refine Set.image_congr fun lam hlam => ?_
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [hk lam hlam e]
    rw [hset]
    exact actualKLValue_le_game M hM hr w ⟨hw.1, hw.2⟩

#print axioms obsLaw_fam_real
#print axioms klq_dummy
#print axioms actualKLValue_le_game
#print axioms family_policy_lower

end CIGAMF.P13.PaperAFamilyLower
