import «LeanD6GaussianQueryDominanceV1»
import «LeanD6UniqueOptimumV1»
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! Actual Gaussian likelihood confidence sets and geometric decisions. This
closes the deterministic/event bridge for the implemented mixture stop. The
Ville bound for the actual mixture process, termination, and Gamma rate are
separate obligations and are not assumptions disguised as conclusions. -/
namespace CIGAMF.P13.D6StoppingGeometryBridge
open scoped BigOperators
open Finset MeasureTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6UniqueOptimum
open CIGAMF.P13.D6Geometry CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

/-- Gaussian log likelihood up to the same observation-only constant for all
worlds. Each row is an actual query and its observed noisy value. -/
def logLikelihood (A : Finset (I n)) (j : I n) (mu : ℝ)
    (record : List (Measurement n × ℝ)) : ℝ :=
  -((record.map fun row => (row.2-actualMean A j mu row.1)^2).sum)/2

def likelihoodValues (A : Finset (I n)) (j : I n)
    (record : List (Measurement n × ℝ)) : Set ℝ :=
  {v | ∃ mu : ℝ,0 ≤ mu ∧ mu ≤ 1 ∧ v=logLikelihood A j mu record}

def profile (A : Finset (I n)) (j : I n) (record : List (Measurement n × ℝ)) : ℝ :=
  sSup (likelihoodValues A j record)

lemma likelihood_nonpositive (A : Finset (I n)) (j : I n) (mu : ℝ)
    (record : List (Measurement n × ℝ)) : logLikelihood A j mu record ≤ 0 := by
  have hsum : 0 ≤ (record.map fun row => (row.2-actualMean A j mu row.1)^2).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hx
    positivity
  unfold logLikelihood
  linarith

theorem true_likelihood_le_profile (A : Finset (I n)) (j : I n) (mu : ℝ)
    (record : List (Measurement n × ℝ)) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) :
    logLikelihood A j mu record ≤ profile A j record := by
  apply le_csSup
  · refine ⟨0,?_⟩
    rintro v ⟨nu,hn,hn1,rfl⟩
    exact likelihood_nonpositive A j nu record
  · exact ⟨mu,hmu,hmu1,rfl⟩

def confidence (candidates : Finset (Finset (I n))) (j : I n)
    (record : List (Measurement n × ℝ)) (threshold : ℝ) : Finset (Finset (I n)) :=
  candidates.filter (fun A => threshold ≤ profile A j record)

/-- A unique surviving label equals the truth whenever the actual true-world
likelihood lies above the rejection threshold. -/
theorem singleton_stop_recovers_label (candidates : Finset (Finset (I n)))
    (A answer : Finset (I n)) (j : I n) (record : List (Measurement n × ℝ))
    (threshold mu : ℝ) (hA : A ∈ candidates) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcover : threshold ≤ logLikelihood A j mu record)
    (hstop : confidence candidates j record threshold={answer}) : answer=A := by
  have hm : A ∈ confidence candidates j record threshold := by
    exact mem_filter.mpr ⟨hA,le_trans hcover (true_likelihood_le_profile A j mu record hmu hmu1)⟩
  rw [hstop,mem_singleton] at hm
  exact hm.symm

def GeometricOptimal (A S : Finset (I n)) (j : I n) (mu : ℝ) : Prop :=
  ∀ T : Finset (I n),T.card=A.card →
    selectedRadius (restrictedProjection (world A j mu) (productResponse corner (world A j mu)))
      (liftedSelection S) ≤
    selectedRadius (restrictedProjection (world A j mu) (productResponse corner (world A j mu)))
      (liftedSelection T)

/-- No abstract reward surrogate: the returned complement optimizes the
literal support geometry already constructed for every D6 width. -/
theorem singleton_stop_geometric (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A answer : Finset (I (2*r+1))) (hA : A ∈ worlds r j)
    (record : List (Measurement (2*r+1) × ℝ)) (threshold mu : ℝ)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hcover : threshold ≤ logLikelihood A j mu record)
    (hstop : confidence (worlds r j) j record threshold={answer}) :
    GeometricOptimal A answerᶜ j mu := by
  have he := singleton_stop_recovers_label (worlds r j) A answer j record threshold mu hA hmu hmu1 hcover hstop
  subst answer
  have hp := world_parameters r j hr hA
  exact (geometric_optimal_iff A Aᶜ j hp.1 mu hmu hmu1 hp.2.2.1 hp.2.2.1 hp.2.2.2).mpr rfl

/-- Arbitrary finite stopping decisions are covered by an anytime likelihood
crossing event. `none` represents a run that has not stopped; it is never
counted as a correct geometric answer. No stopping-time assumption is needed
for this pointwise inclusion. -/
theorem wrong_stop_implies_mixture_crossing {Ω : Type*}
    (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r) (A : Finset (I (2*r+1)))
    (hA : A ∈ worlds r j) (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (record : ℕ → Ω → List (Measurement (2*r+1) × ℝ))
    (logMix : ℕ → Ω → ℝ) (logDelta : ℝ)
    (tau : Ω → Option ℕ) (answer : ℕ → Ω → Finset (I (2*r+1)))
    (hstop : ∀ omega t,tau omega=some t →
      confidence (worlds r j) j (record t omega) (logDelta+logMix t omega)={answer t omega}) :
    {omega | ∃ t,tau omega=some t ∧ ¬GeometricOptimal A (answer t omega)ᶜ j mu} ⊆
      {omega | ∃ t,-logDelta < logMix t omega-logLikelihood A j mu (record t omega)} := by
  rintro omega ⟨t,ht,hbad⟩
  refine ⟨t,?_⟩
  by_contra h
  have hc : logDelta+logMix t omega ≤ logLikelihood A j mu (record t omega) := by
    have := le_of_not_gt h
    linarith
  exact hbad (singleton_stop_geometric r j hr A (answer t omega) hA (record t omega)
    (logDelta+logMix t omega) mu hmu hmu1 hc (hstop omega t ht))

/-- Exact probability transfer. The RHS is the actual likelihood-mixture
crossing probability; bounding it by delta requires the martingale proof. -/
theorem geometric_error_le_mixture_crossing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (A : Finset (I (2*r+1))) (hA : A ∈ worlds r j)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (record : ℕ → Ω → List (Measurement (2*r+1) × ℝ))
    (logMix : ℕ → Ω → ℝ) (logDelta : ℝ)
    (tau : Ω → Option ℕ) (answer : ℕ → Ω → Finset (I (2*r+1)))
    (hstop : ∀ omega t,tau omega=some t →
      confidence (worlds r j) j (record t omega) (logDelta+logMix t omega)={answer t omega}) :
    P {omega | ∃ t,tau omega=some t ∧ ¬GeometricOptimal A (answer t omega)ᶜ j mu} ≤
      P {omega | ∃ t,-logDelta < logMix t omega-logLikelihood A j mu (record t omega)} :=
  measure_mono (wrong_stop_implies_mixture_crossing r j hr A hA mu hmu hmu1 record logMix logDelta tau answer hstop)

#print axioms true_likelihood_le_profile
#print axioms singleton_stop_recovers_label
#print axioms singleton_stop_geometric
#print axioms wrong_stop_implies_mixture_crossing
#print axioms geometric_error_le_mixture_crossing
end
end CIGAMF.P13.D6StoppingGeometryBridge
