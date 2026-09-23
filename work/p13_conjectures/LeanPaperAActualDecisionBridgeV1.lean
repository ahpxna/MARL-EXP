import «LeanPaperAStrictV1»

/-!
DRAFT proof source, written without a compile pass at the user's request.
The bridge uses oscillation on the FULL product domain for BOTH retained choices.
The alternative equality is strict and quantified over every centered candidate.
The Gaussian integral theorem is about the actual marginal observation laws; a separate
identification with Mathlib's ENNReal klDiv is not asserted by this module.
-/
namespace CIGAMF.P13.PaperAActualDecisionBridge
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.PaperARPair CIGAMF.P13.PaperACentred
open CIGAMF.P13.PaperACentredModel CIGAMF.P13.PaperAStrict
variable {r : ℕ}

noncomputable def finiteOsc {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) : ℝ :=
  univ.sup' univ_nonempty f - univ.inf' univ_nonempty f

theorem finiteOsc_comp_surjective {X Y : Type*} [Fintype X] [Fintype Y]
    [Nonempty X] [Nonempty Y] (f : Y → ℝ) (π : X → Y) (hπ : Function.Surjective π) :
    finiteOsc (f ∘ π) = finiteOsc f := by
  classical
  have hmax : univ.sup' univ_nonempty (f ∘ π) = univ.sup' univ_nonempty f := by
    apply le_antisymm
    · exact sup'_le _ _ (fun x _ => le_sup' f (mem_univ (π x)))
    · refine sup'_le _ _ (fun y _ => ?_)
      obtain ⟨x, rfl⟩ := hπ y
      exact le_sup' (f ∘ π) (mem_univ x)
  have hmin : univ.inf' univ_nonempty (f ∘ π) = univ.inf' univ_nonempty f := by
    apply le_antisymm
    · refine le_inf' _ _ (fun y _ => ?_)
      obtain ⟨x, rfl⟩ := hπ y
      exact inf'_le (f ∘ π) (mem_univ x)
    · exact le_inf' _ _ (fun x _ => inf'_le f (mem_univ (π x)))
  exact congrArg₂ (· - ·) hmax hmin

theorem finiteOsc_bool (f : Bool → ℝ) : finiteOsc f = |f true - f false| := by
  classical
  have hmax : univ.sup' univ_nonempty f = max (f true) (f false) := by
    apply le_antisymm
    · refine sup'_le _ _ (fun b _ => ?_)
      cases b
      · exact le_max_right _ _
      · exact le_max_left _ _
    · exact max_le (le_sup' f (mem_univ true)) (le_sup' f (mem_univ false))
  have hmin : univ.inf' univ_nonempty f = min (f true) (f false) := by
    apply le_antisymm
    · exact le_min (inf'_le f (mem_univ true)) (inf'_le f (mem_univ false))
    · refine le_inf' _ _ (fun b _ => ?_)
      cases b
      · exact min_le_right _ _
      · exact min_le_left _ _
  unfold finiteOsc
  rw [hmax, hmin]
  by_cases h : f false ≤ f true
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
  · have h' := le_of_not_ge h
    rw [max_eq_right h', min_eq_left h', abs_of_nonpos (sub_nonpos.mpr h')]
    ring

noncomputable def residB (lam : Cell r → ℝ) (x : Bool × BIdx r) : ℝ :=
  respF lam x - margB lam x.2

theorem residB_eq (lam : Cell r → ℝ) (hc : lam ∈ Centred r) (x : Bool × BIdx r) :
    residB lam x = tblA lam x.1 := by
  have h := ((centred_iff_marginals lam).mp hc).2 x.2
  unfold residB respF
  rw [h]
  ring

noncomputable def actualLossA (lam : Cell r → ℝ) : ℝ := finiteOsc (residA lam) / 2
noncomputable def actualLossB (lam : Cell r → ℝ) : ℝ := finiteOsc (residB lam) / 2

theorem actualLossA_eq (lam : Cell r → ℝ) (hc : lam ∈ Centred r) :
    actualLossA lam = rangeB lam / 2 := by
  have hr : residA lam = tblB lam ∘ Prod.snd := funext (residA_eq lam hc)
  unfold actualLossA
  rw [hr, finiteOsc_comp_surjective (tblB lam) Prod.snd
    (fun b => ⟨(false,b),rfl⟩)]
  exact congrArg (· / 2) (rangeB_eq_osc lam).symm

theorem actualLossB_eq (lam : Cell r → ℝ) (hc : lam ∈ Centred r) :
    actualLossB lam = rangeA lam / 2 := by
  have hr : residB lam = tblA lam ∘ Prod.fst := funext (residB_eq lam hc)
  unfold actualLossB
  rw [hr, finiteOsc_comp_surjective (tblA lam) Prod.fst
    (fun a => ⟨(a,Sum.inl false),rfl⟩), finiteOsc_bool]
  rfl

def ActualBadA (eps : ℝ) (lam : Cell r → ℝ) : Prop :=
  actualLossA lam > min (actualLossA lam) (actualLossB lam) + eps

def ActualBadB (eps : ℝ) (lam : Cell r → ℝ) : Prop :=
  actualLossB lam > min (actualLossA lam) (actualLossB lam) + eps

theorem bad_against_min_iff (x y eps : ℝ) (heps : 0 ≤ eps) :
    x > min x y + eps ↔ x > y + eps := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy]; constructor <;> intro h <;> linarith
  · rw [min_eq_right (le_of_not_ge hxy)]

theorem actualBadA_iff (eps : ℝ) (heps : 0 ≤ eps) (lam : Cell r → ℝ)
    (hc : lam ∈ Centred r) : ActualBadA eps lam ↔ rangeB lam > rangeA lam + 2*eps := by
  unfold ActualBadA
  rw [bad_against_min_iff _ _ _ heps, actualLossA_eq lam hc, actualLossB_eq lam hc]
  constructor <;> intro h <;> linarith

theorem actualBadB_iff (eps : ℝ) (heps : 0 ≤ eps) (lam : Cell r → ℝ)
    (hc : lam ∈ Centred r) : ActualBadB eps lam ↔ rangeA lam > rangeB lam + 2*eps := by
  unfold ActualBadB
  rw [min_comm, bad_against_min_iff _ _ _ heps, actualLossA_eq lam hc, actualLossB_eq lam hc]
  constructor <;> intro h <;> linarith

theorem actual_strict_alternative_eq :
    {lam : Cell r → ℝ | ActualBadA 0 lam ∧ lam ∈ Centred r} = TrueAltStrict r := by
  ext lam
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨by simpa using (actualBadA_iff 0 (by norm_num) lam hc).mp h,hc⟩
  · rintro ⟨h,hc⟩
    exact ⟨(actualBadA_iff 0 (by norm_num) lam hc).mpr (by simpa using h),hc⟩

/-- The query table is assembled from actual marginals, not defined to be lam. -/
noncomputable def queryMean (lam : Cell r → ℝ) : Cell r → ℝ :=
  Sum.elim (fun i => if i=0 then margA lam false else if i=1 then margA lam true
    else if i=2 then margB lam (Sum.inl false) else margB lam (Sum.inl true))
    (fun p => margB lam (Sum.inr p))

theorem queryMean_eq (lam : Cell r → ℝ) (hc : lam ∈ Centred r) : queryMean lam = lam := by
  funext e
  obtain ⟨hA,hB⟩ := (centred_iff_marginals lam).mp hc
  cases e with
  | inl i => fin_cases i <;> simp [queryMean,hA,hB,tblA,tblB,aCell,bCell]
  | inr p => simpa [queryMean,tblB,bCell] using hB (Sum.inr p)

noncomputable def observationLaw (v : Cell r → NNReal) (lam : Cell r → ℝ) (e : Cell r) :
    Measure ℝ := gaussianReal (queryMean lam e) (v e)

/-- All centered worlds and candidates; the integral is the common-variance Gaussian
log density ratio in its completed-square form. -/
theorem actual_observation_information (v : Cell r → NNReal)
    (hv : ∀ e, 0 < (v e : ℝ)) (theta lam w : Cell r → ℝ)
    (htheta : theta ∈ Centred r) (hlam : lam ∈ Centred r) :
    (∑ e, w e * ∫ y : ℝ,
      (queryMean theta e-queryMean lam e)*(2*y-queryMean theta e-queryMean lam e)
        /(2*(v e : ℝ)) ∂observationLaw v theta e)
      = energy w (fun e => (v e : ℝ)) theta lam := by
  unfold observationLaw
  simp_rw [gaussKL_eq_integral _ _ _ (hv _)]
  rw [queryMean_eq theta htheta, queryMean_eq lam hlam]
  exact (energy_eq_sum_gaussKL w (fun e => (v e : ℝ)) theta lam).symm

/-- The existing strict information game is now over actual compression-bad worlds. -/
theorem strict_value_is_actual (M : ℝ) (w : Cell r → ℝ) :
    trueValueStrict M w = sInf (energy w (pairVar M) (thetaC r) ''
      {lam : Cell r → ℝ | ActualBadA 0 lam ∧ lam ∈ Centred r}) := by
  rw [actual_strict_alternative_eq]
  unfold trueValueStrict
  rw [Set.image_eq_range]
  rfl

#print axioms actualLossA_eq
#print axioms actualLossB_eq
#print axioms actual_strict_alternative_eq
#print axioms queryMean_eq
#print axioms actual_observation_information
#print axioms strict_value_is_actual
end CIGAMF.P13.PaperAActualDecisionBridge
