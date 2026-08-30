import Mathlib

/-!
# CIG--AMF unified chains v2

Finite deterministic algebra only. This source does not assert causal
identification, learned-model calibration, solver status, or MARL prevalence.
All theorem hypotheses are explicit. The Boolean action domain retains the
essential distinction between action-dependent and product/fixed references.
-/

namespace CIGAMFUnifiedV2

section Oscillation

def osc2 (f : Bool → ℝ) : ℝ := |f true - f false|

def response2 (primitive complement : Bool → ℝ) : Bool → ℝ :=
  fun a => primitive a + complement a

def gaugeError2 (estimate truth : Bool → ℝ) : ℝ :=
  osc2 (fun a => estimate a - truth a) / 2

theorem osc2_nonneg (f : Bool → ℝ) : 0 ≤ osc2 f := by
  exact abs_nonneg _

/- The finite two-action instance of `|osc(f+g)-osc(f)| ≤ osc(g)`. -/
theorem osc2_add_deviation_le (f g : Bool → ℝ) :
    |osc2 (fun a => f a + g a) - osc2 f| ≤ osc2 g := by
  rw [show osc2 (fun a => f a + g a) =
      |(f true - f false) + (g true - g false)| by
        simp [osc2]; ring,
      osc2, osc2]
  convert abs_abs_sub_abs_le (f true - f false) (g true - g false) using 1 <;> ring

/- General conditional-reference bridge on a finite binary action domain.
`complement` is the conditional expectation of all non-j components. -/
theorem reference_contamination_span_bound
    (primitive complement : Bool → ℝ) :
    |osc2 (response2 primitive complement) - osc2 primitive| ≤ osc2 complement := by
  simpa [response2] using osc2_add_deviation_le primitive complement

/- Product/fixed forcing has a complement expectation constant in the
intervened action. -/
theorem product_reference_span_exact
    (primitive complement : Bool → ℝ)
    (hconstant : complement true = complement false) :
    osc2 (response2 primitive complement) = osc2 primitive := by
  have hz : osc2 complement = 0 := by simp [osc2, hconstant]
  have h := reference_contamination_span_bound primitive complement
  rw [hz] at h
  exact abs_eq_zero.mp h

/- Oscillation is invariant under the additive-component gauge. -/
theorem gauge_error_shift_invariant
    (estimate truth : Bool → ℝ) (c : ℝ) :
    gaugeError2 (fun a => estimate a + c) truth = gaugeError2 estimate truth := by
  simp [gaugeError2, osc2]
  congr 2
  ring

/- The quotient/gauge metric bounds radius perturbation for one omitted
binary primitive component. -/
theorem fixed_subset_radius_gauge_stability
    (estimate truth : Bool → ℝ) :
    |osc2 estimate / 2 - osc2 truth / 2| ≤ gaugeError2 estimate truth := by
  have h := osc2_add_deviation_le truth (fun a => estimate a - truth a)
  have heq : (fun a => truth a + (estimate a - truth a)) = estimate := by
    funext a
    ring
  rw [heq] at h
  rw [gaugeError2]
  nlinarith [abs_nonneg (osc2 estimate - osc2 truth)]

/- Deterministic response-function Lipschitz bound. -/
theorem span_supnorm_lipschitz
    (estimate truth : Bool → ℝ) (eps : ℝ)
    (htrue : |estimate true - truth true| ≤ eps)
    (hfalse : |estimate false - truth false| ≤ eps) :
    |osc2 estimate - osc2 truth| ≤ 2 * eps := by
  have h := osc2_add_deviation_le truth (fun a => estimate a - truth a)
  have heq : (fun a => truth a + (estimate a - truth a)) = estimate := by
    funext a
    ring
  rw [heq] at h
  have hd : |(estimate true - truth true) - (estimate false - truth false)| ≤ 2 * eps := by
    rw [abs_sub]
    calc
      |(estimate true - truth true) + -(estimate false - truth false)| ≤
          |estimate true - truth true| + |-(estimate false - truth false)| := abs_add _ _
      _ = |estimate true - truth true| + |estimate false - truth false| := by rw [abs_neg]
      _ ≤ eps + eps := add_le_add htrue hfalse
      _ = 2 * eps := by ring
  simpa [osc2] using h.trans (by simpa [osc2] using hd)

end Oscillation

section DeficitCertificates

/- The exact deficit identity after extrema have been reduced to their
attained aggregate values. -/
def deficit (componentSpan supportOsc : ℝ) : ℝ := componentSpan - supportOsc
def ePlus (sumMax supportMax : ℝ) : ℝ := sumMax - supportMax
def eMinus (supportMin sumMin : ℝ) : ℝ := supportMin - sumMin

theorem deficit_identity
    (sumMax sumMin supportMax supportMin : ℝ) :
    deficit (sumMax - sumMin) (supportMax - supportMin) =
      ePlus sumMax supportMax + eMinus supportMin sumMin := by
  simp [deficit, ePlus, eMinus]
  ring

/- A modular Top-C minimizer plus a nonnegative one-sided support deficit
gives the improved half-zeta constant. -/
theorem one_sided_zeta_half
    {X : Type*} (modular deficitFn : X → ℝ) (zeta : ℝ) (top optimum : X)
    (hmod : modular top ≤ modular optimum)
    (hnonneg : ∀ x, 0 ≤ deficitFn x)
    (hupper : ∀ x, deficitFn x ≤ zeta) :
    (modular top - deficitFn top) / 2 ≤
      (modular optimum - deficitFn optimum) / 2 + zeta / 2 := by
  have htop := hupper top
  have hopt := hnonneg optimum
  linarith

/- `E` is a subset-independent defect upper bound; no claim is made that it
is cheap to compute. -/
theorem global_subset_independent_certificate
    {X : Type*} (modular deficitFn : X → ℝ) (E : ℝ) (top optimum : X)
    (hmod : modular top ≤ modular optimum)
    (hnonneg : ∀ x, 0 ≤ deficitFn x)
    (hE : ∀ x, deficitFn x ≤ E) :
    (modular top - deficitFn top) / 2 -
      (modular optimum - deficitFn optimum) / 2 ≤ E / 2 := by
  have h := one_sided_zeta_half modular deficitFn E top optimum hmod hnonneg hE
  linarith

/- Solver correctness is outside Lean. Given a verified lower bound, this
certificate is pure order algebra. -/
theorem lp_lower_bound_certificate
    (candidate optimum lowerBound : ℝ) (hLB : lowerBound ≤ optimum) :
    candidate - optimum ≤ candidate - lowerBound := by
  linarith

end DeficitCertificates

section SupportUncertainty

/- Exact radius on a Boolean support: a singleton has radius zero; both
actions have half their response span. -/
def radiusBoolSupport (support : Finset Bool) (f : Bool → ℝ) : ℝ :=
  if true ∈ support ∧ false ∈ support then osc2 f / 2 else 0

theorem radiusBoolSupport_nonneg (support : Finset Bool) (f : Bool → ℝ) :
    0 ≤ radiusBoolSupport support f := by
  by_cases h : true ∈ support ∧ false ∈ support
  · simp [radiusBoolSupport, h, osc2_nonneg]
  · simp [radiusBoolSupport, h]

theorem support_radius_monotone
    (inner outer : Finset Bool) (f : Bool → ℝ) (hsubset : inner ⊆ outer) :
    radiusBoolSupport inner f ≤ radiusBoolSupport outer f := by
  by_cases hi : true ∈ inner ∧ false ∈ inner
  · have ho : true ∈ outer ∧ false ∈ outer := ⟨hsubset hi.1, hsubset hi.2⟩
    simp [radiusBoolSupport, hi, ho]
  · by_cases ho : true ∈ outer ∧ false ∈ outer
    · simp [radiusBoolSupport, hi, ho, radiusBoolSupport_nonneg]
    · simp [radiusBoolSupport, hi, ho]

/- The Omega-/Omega+ regret bracket after an inner-support optimizer (or
valid inner LP lower bound) supplied `innerLower`. -/
theorem support_bracket_regret
    (trueRadius selectedOuterRadius innerLower trueOptimalRadius : ℝ)
    (hupper : trueRadius ≤ selectedOuterRadius)
    (hlower : innerLower ≤ trueOptimalRadius) :
    trueRadius - trueOptimalRadius ≤ selectedOuterRadius - innerLower := by
  linarith

/- Projected-span brackets are the same monotonicity statement for one binary
coordinate. -/
theorem projected_span_bracket
    (inner outer : Finset Bool) (f : Bool → ℝ) (hsubset : inner ⊆ outer) :
    2 * radiusBoolSupport inner f ≤ 2 * radiusBoolSupport outer f := by
  nlinarith [support_radius_monotone inner outer f hsubset]

end SupportUncertainty

section Counterexamples

/- Feasible forcing a₂=a₁ can erase a primitive span. -/
def primitiveWitness (a : Bool) : ℝ := if a then 1 else 0
def forcedComplementWitness (a : Bool) : ℝ := -primitiveWitness a

theorem feasible_reference_contamination_witness :
    osc2 primitiveWitness = 1 ∧
    osc2 (response2 primitiveWitness forcedComplementWitness) = 0 := by
  norm_num [osc2, primitiveWitness, forcedComplementWitness, response2]

end Counterexamples

end CIGAMFUnifiedV2
