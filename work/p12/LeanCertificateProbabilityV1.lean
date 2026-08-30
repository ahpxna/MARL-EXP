import Mathlib
import «LeanPairwiseMasterV4»
import «LeanFunctionalRankingV6»

/-! Exact probability lifting for deterministic certificates.

No concentration inequality is assumed or proved here.  The only statistical
input is an externally established upper bound on the complement of the
simultaneous score-coverage event. -/

namespace CIGAMF.V7.CertificateProbability

open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.Pairwise
open MeasureTheory

theorem CERTP1_failure_measure_le_bad_event
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (good failure : Set Ω) (α : ENNReal)
    (hsub : failure ⊆ goodᶜ) (hbad : μ goodᶜ ≤ α) :
    μ failure ≤ α := by
  exact le_trans (measure_mono hsub) hbad

def ScoreCoverageEvent
    {Ω ι : Type*} (C : ι → ℝ)
    (Chat e : Ω → ι → ℝ) : Set Ω :=
  {ω | scoreCovered C (Chat ω) (e ω)}

def FalseCertificateEvent
    {Ω : Type*} (certificateSound : Ω → Prop) : Set Ω :=
  {ω | ¬ certificateSound ω}

theorem CERTP2_deterministic_soundness_on_good_event
    {Ω ι : Type*}
    (C : ι → ℝ) (Chat e : Ω → ι → ℝ)
    (certificateSound : Ω → Prop)
    (hsound : ∀ ω, ω ∈ ScoreCoverageEvent C Chat e → certificateSound ω) :
    FalseCertificateEvent certificateSound ⊆
      (ScoreCoverageEvent C Chat e)ᶜ := by
  intro ω hfalse hgood
  exact hfalse (hsound ω hgood)

theorem CERTP3_high_probability_certificate
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (C : ι → ℝ)
    (Chat e : Ω → ι → ℝ)
    (certificateSound : Ω → Prop) (α : ENNReal)
    (hsound : ∀ ω, ω ∈ ScoreCoverageEvent C Chat e → certificateSound ω)
    (hcoverage : μ (ScoreCoverageEvent C Chat e)ᶜ ≤ α) :
    μ (FalseCertificateEvent certificateSound) ≤ α := by
  exact CERTP1_failure_measure_le_bad_event μ
    (ScoreCoverageEvent C Chat e)
    (FalseCertificateEvent certificateSound) α
    (CERTP2_deterministic_soundness_on_good_event C Chat e certificateSound hsound)
    hcoverage

def OperationalMasterSound
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι]
    (f : ι → Ω → ℝ) (L : Finset ι → ℝ)
    (Chat e : ι → ℝ)
    (selected optimum : Finset ι) (k : ℕ) (eta : ℝ) : Prop :=
  L selected - L optimum ≤
    operationalGamma Chat e (canonicalTopK (upperScore Chat e) k) selected +
      zetaDefFinite f k / 2 + 2 * eta

theorem CERTP4_master_sound_on_score_coverage
    {Ξ Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι]
    (f : ι → Ω → ℝ) (L : Finset ι → ℝ)
    (Chat e : Ξ → ι → ℝ)
    (trueTop selected optimum : Finset ι)
    (k : ℕ) (eta : ℝ)
    (hTop : IsTopKByScore (componentSpan f) trueTop k)
    (hSelectedCard : selected.card = k) (hOptCard : optimum.card = k)
    (hDownstreamUniform : ∀ S : Finset ι, S.card = k →
      |L S - selectedRadius f S| ≤ eta) :
    ∀ ξ, ξ ∈ ScoreCoverageEvent (componentSpan f) Chat e →
      OperationalMasterSound f L (Chat ξ) (e ξ) selected optimum k eta := by
  intro ξ hcoverage
  exact FULLY_INSTANTIATED_OPERATIONAL_MASTER f (Chat ξ) (e ξ) L
    trueTop selected optimum k eta hcoverage hTop hSelectedCard hOptCard
    hDownstreamUniform

theorem CERTP5_high_probability_operational_master
    {Ξ Ω ι : Type*} [MeasurableSpace Ξ]
    [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure Ξ)
    (f : ι → Ω → ℝ) (L : Finset ι → ℝ)
    (Chat e : Ξ → ι → ℝ)
    (trueTop selected optimum : Finset ι)
    (k : ℕ) (eta : ℝ) (α : ENNReal)
    (hTop : IsTopKByScore (componentSpan f) trueTop k)
    (hSelectedCard : selected.card = k) (hOptCard : optimum.card = k)
    (hDownstreamUniform : ∀ S : Finset ι, S.card = k →
      |L S - selectedRadius f S| ≤ eta)
    (hcoverage : μ (ScoreCoverageEvent (componentSpan f) Chat e)ᶜ ≤ α) :
    μ (FalseCertificateEvent (fun ξ =>
      OperationalMasterSound f L (Chat ξ) (e ξ) selected optimum k eta)) ≤ α := by
  exact CERTP3_high_probability_certificate μ (componentSpan f) Chat e
    (fun ξ => OperationalMasterSound f L (Chat ξ) (e ξ)
      selected optimum k eta) α
    (CERTP4_master_sound_on_score_coverage f L Chat e trueTop selected optimum
      k eta hTop hSelectedCard hOptCard hDownstreamUniform)
    hcoverage

end CIGAMF.V7.CertificateProbability
