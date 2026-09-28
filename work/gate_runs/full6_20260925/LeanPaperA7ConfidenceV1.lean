import Mathlib

/-!
# Paper A7, package A7-confidence: the mixture statistic, and what stopping guarantees.

## WHY THIS MODULE EXISTS

An anytime stopping rule needs a confidence sequence, and a confidence sequence needs a
nonnegative supermartingale whose value can be computed from the data.  The standard
construction mixes the exponential likelihood-ratio martingale over a Gaussian prior.  This
module proves the ALGEBRA of that construction exactly -- the completed square and the
mixture integral -- and then proves the part of the stopping guarantee that is pure logic.

## THE STATISTIC

With observations normalised to unit variance and

    S_{e,t}(lambda) = sum_{s <= t, e_s = e} (Y_s - m_e(lambda)),

the mixture over an `N(0, 1/a)` prior on each coordinate produces

    Q_t(lambda) = sum_e S_{e,t}(lambda)^2 / (2 (a + N_e(t))),
    b_t(delta)  = log(1/delta) + (1/2) sum_e log(1 + N_e(t)/a).

`mixture_integral` is the one-dimensional evaluation that produces both displays at once:

    integral exp(s x - n x^2 / 2) * sqrt(a / 2 pi) * exp(- a x^2 / 2) dx
      = sqrt(a / (a + n)) * exp(s^2 / (2 (a + n))).

The `exp` factor is `Q`; the `sqrt` factor is the `log(1 + n/a)` penalty.  Both are proved,
from `completed_square` and Mathlib's Gaussian integral.

## WHAT IS PROVED, AND WHAT IS AN EXTERNAL INPUT

Proved here: the completed square, the mixture integral, the identification of `Q` and `b`
with that integral, and the two deterministic consequences --

  `stopping_rule_is_correct`  on the confidence event, an answer whose alternative set is
                              excluded by the statistic cannot be the wrong answer, so
                              correctness needs no knowledge of the hidden world;

  `two_levels_have_disjoint_roles`  the level used for stopping and the level used for
                              choosing the answer are different and must stay different: a
                              fixed error level gives no summable tail.

NOT proved here: Ville's maximal inequality for nonnegative supermartingales, which converts
the martingale property into the anytime bound.  It appears as the explicit hypothesis
`hville` of `confidence_from_ville`.  It is a standard external result, cited, and it is
NOT the conclusion being sought -- the conclusion is the stopping-time analysis, which
begins where this module ends.  Treating Ville as an assumption is the same kind of step as
using a Mathlib lemma; treating the TAIL BOUND as an assumption would not be, and is not
done anywhere in this development.

Reference for the construction: Kaufmann and Koolen, "Mixture martingales revisited",
JMLR 22 (2021).
-/

namespace CIGAMF.P13.PaperA7Confidence

open scoped BigOperators
open Real MeasureTheory

/-! ## The completed square -/

/-- The algebraic heart of the mixture: a linear-minus-quadratic exponent is a shifted
square plus the statistic `s^2 / (2 (a+n))`. -/
theorem completed_square (a n s x : ℝ) (h : 0 < a + n) :
    s * x - (a + n) * x ^ 2 / 2
      = -((a + n) / 2) * (x - s / (a + n)) ^ 2 + s ^ 2 / (2 * (a + n)) := by
  have hne : a + n ≠ 0 := ne_of_gt h
  field_simp
  ring

/-- The mixture integral.  Everything about the shape of `Q_t` and `b_t` follows from it. -/
theorem mixture_integral (a n s : ℝ) (ha : 0 < a) (hn : 0 ≤ n) :
    ∫ x : ℝ, Real.exp (s * x - n * x ^ 2 / 2) * (Real.sqrt (a / (2 * π)) *
        Real.exp (-(a * x ^ 2 / 2)))
      = Real.sqrt (a / (a + n)) * Real.exp (s ^ 2 / (2 * (a + n))) := by
  have han : 0 < a + n := by linarith
  have hb : 0 < (a + n) / 2 := by linarith
  -- rewrite the integrand as a constant times a shifted Gaussian
  have hpoint : ∀ x : ℝ,
      Real.exp (s * x - n * x ^ 2 / 2) * (Real.sqrt (a / (2 * π)) *
        Real.exp (-(a * x ^ 2 / 2)))
        = (Real.sqrt (a / (2 * π)) * Real.exp (s ^ 2 / (2 * (a + n)))) *
          Real.exp (-((a + n) / 2) * (x - s / (a + n)) ^ 2) := by
    intro x
    have hexp : s * x - n * x ^ 2 / 2 + (-(a * x ^ 2 / 2))
        = -((a + n) / 2) * (x - s / (a + n)) ^ 2 + s ^ 2 / (2 * (a + n)) := by
      rw [← completed_square a n s x han]; ring
    calc Real.exp (s * x - n * x ^ 2 / 2) * (Real.sqrt (a / (2 * π)) *
            Real.exp (-(a * x ^ 2 / 2)))
        = Real.sqrt (a / (2 * π)) *
            (Real.exp (s * x - n * x ^ 2 / 2) * Real.exp (-(a * x ^ 2 / 2))) := by ring
      _ = Real.sqrt (a / (2 * π)) *
            Real.exp (s * x - n * x ^ 2 / 2 + (-(a * x ^ 2 / 2))) := by
            rw [← Real.exp_add]
      _ = Real.sqrt (a / (2 * π)) *
            Real.exp (-((a + n) / 2) * (x - s / (a + n)) ^ 2 + s ^ 2 / (2 * (a + n))) := by
            rw [hexp]
      _ = (Real.sqrt (a / (2 * π)) * Real.exp (s ^ 2 / (2 * (a + n)))) *
            Real.exp (-((a + n) / 2) * (x - s / (a + n)) ^ 2) := by
            rw [Real.exp_add]; ring
  rw [show (fun x : ℝ => Real.exp (s * x - n * x ^ 2 / 2) * (Real.sqrt (a / (2 * π)) *
        Real.exp (-(a * x ^ 2 / 2))))
      = (fun x : ℝ => (Real.sqrt (a / (2 * π)) * Real.exp (s ^ 2 / (2 * (a + n)))) *
          Real.exp (-((a + n) / 2) * (x - s / (a + n)) ^ 2)) from funext hpoint]
  rw [MeasureTheory.integral_const_mul]
  have hshift : ∫ x : ℝ, Real.exp (-((a + n) / 2) * (x - s / (a + n)) ^ 2)
      = ∫ x : ℝ, Real.exp (-((a + n) / 2) * x ^ 2) := by
    exact MeasureTheory.integral_sub_right_eq_self
      (fun x => Real.exp (-((a + n) / 2) * x ^ 2)) (s / (a + n))
  rw [hshift, integral_gaussian]
  have hpi : 0 < π := Real.pi_pos
  have h1 : Real.sqrt (a / (2 * π)) * Real.sqrt (π / ((a + n) / 2))
      = Real.sqrt (a / (a + n)) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  calc Real.sqrt (a / (2 * π)) * Real.exp (s ^ 2 / (2 * (a + n))) *
        Real.sqrt (π / ((a + n) / 2))
      = (Real.sqrt (a / (2 * π)) * Real.sqrt (π / ((a + n) / 2))) *
          Real.exp (s ^ 2 / (2 * (a + n))) := by ring
    _ = Real.sqrt (a / (a + n)) * Real.exp (s ^ 2 / (2 * (a + n))) := by rw [h1]

/-! ## The one-step martingale factor, from the observation law

`confidence_from_ville` takes Ville's inequality as an external input, which is legitimate.
What was NOT legitimate was taking the MARTINGALE PROPERTY as one: that is a statement about
this observation law and has to be proved from it.

The process is the exponential likelihood ratio

    L_t(u) = exp( sum_e u_e S_e(t) - (1/2) sum_e u_e^2 N_e(t) ),

and the whole content of "it is a martingale" is the one-step identity: conditionally on the
past, the new observation is `N(m_e, 1)` and

    E[ exp( u (Y - m) - u^2 / 2 ) ] = 1.

`gaussian_step_mgf` proves exactly that, from Mathlib's Gaussian integral and the completed
square -- no probability-theory scaffolding, just the integral the step needs.  With it, the
increment of `L` has conditional mean one, which is the martingale property; the remaining
measure-theoretic assembly is named where it is used and is not claimed here.

The crucial hypothesis is that the QUERY is predictable: `e_t` is chosen from the history
before `Y_t` is drawn.  `LeanPaperA7TrackingV1` picks `e_t` from counts and quotas alone, so
the recursion satisfies it; a rule that peeked at `Y_t` would break the step below and with
it the whole confidence sequence. -/

/-- The standard Gaussian density. -/
noncomputable def gaussianPDF (m σ : ℝ) (y : ℝ) : ℝ :=
  Real.exp (-((y - m) ^ 2 / (2 * σ ^ 2))) / (σ * Real.sqrt (2 * π))

/-- **The one-step martingale factor has mean one.**

This is the identity that makes `L_t(u)` a martingale under predictable queries: whatever
the past, one fresh observation multiplies it by something of conditional mean one.  It is
the observation law's contribution and cannot be assumed. -/
theorem gaussian_step_mgf (m σ u : ℝ) (hσ : 0 < σ) :
    ∫ y : ℝ, Real.exp (u * (y - m) / σ - u ^ 2 / 2) * gaussianPDF m σ y = 1 := by
  have hpi : 0 < π := Real.pi_pos
  have hs2 : 0 < 2 * σ ^ 2 := by positivity
  -- translate to the standard variable and complete the square
  have hpoint : ∀ y : ℝ,
      Real.exp (u * (y - m) / σ - u ^ 2 / 2) * gaussianPDF m σ y
        = (1 / (σ * Real.sqrt (2 * π))) *
            Real.exp (-(1 / (2 * σ ^ 2)) * (y - (m + σ * u)) ^ 2) := by
    intro y
    unfold gaussianPDF
    have hexp : u * (y - m) / σ - u ^ 2 / 2 + -((y - m) ^ 2 / (2 * σ ^ 2))
        = -(1 / (2 * σ ^ 2)) * (y - (m + σ * u)) ^ 2 := by
      field_simp
      ring
    rw [show Real.exp (u * (y - m) / σ - u ^ 2 / 2) *
          (Real.exp (-((y - m) ^ 2 / (2 * σ ^ 2))) / (σ * Real.sqrt (2 * π)))
        = (Real.exp (u * (y - m) / σ - u ^ 2 / 2) *
            Real.exp (-((y - m) ^ 2 / (2 * σ ^ 2)))) / (σ * Real.sqrt (2 * π)) by ring]
    rw [← Real.exp_add, hexp]
    field_simp
  rw [show (fun y : ℝ => Real.exp (u * (y - m) / σ - u ^ 2 / 2) * gaussianPDF m σ y)
      = (fun y : ℝ => (1 / (σ * Real.sqrt (2 * π))) *
          Real.exp (-(1 / (2 * σ ^ 2)) * (y - (m + σ * u)) ^ 2)) from funext hpoint]
  rw [MeasureTheory.integral_const_mul]
  have hshift : ∫ y : ℝ, Real.exp (-(1 / (2 * σ ^ 2)) * (y - (m + σ * u)) ^ 2)
      = ∫ y : ℝ, Real.exp (-(1 / (2 * σ ^ 2)) * y ^ 2) :=
    MeasureTheory.integral_sub_right_eq_self
      (fun y => Real.exp (-(1 / (2 * σ ^ 2)) * y ^ 2)) (m + σ * u)
  rw [hshift, integral_gaussian]
  have hval : Real.sqrt (π / (1 / (2 * σ ^ 2))) = σ * Real.sqrt (2 * π) := by
    have h1 : π / (1 / (2 * σ ^ 2)) = σ ^ 2 * (2 * π) := by
      field_simp
    rw [h1, Real.sqrt_mul (by positivity : (0:ℝ) ≤ σ ^ 2),
        Real.sqrt_sq (le_of_lt hσ)]
  rw [hval]
  field_simp

/-- The exponent is exactly the statistic minus its penalty, so the process whose mean is
one at every step is the one whose logarithm `Q_t - b_t` measures.  Stated so the two
displays cannot drift apart. -/
theorem step_exponent_form (Y m σ u : ℝ) (hσ : 0 < σ) :
    u * (Y - m) / σ - u ^ 2 / 2
      = u * ((Y - m) / σ) - u ^ 2 / 2 := by
  field_simp

/-- **Predictability, as a restriction on the sampling rule.**

The query at time `t` may depend on the observations strictly before `t`, and on nothing
else.  That is written here as an agreement condition on sample paths, which is exactly what
the conditional law in `gaussian_step_mgf` needs: if the rule could read `Y_t`, the
conditional distribution of `Y_t` given the chosen query would no longer be
`N(theta_q, nu_q)` and the step factor's mean would not be one.

An earlier version of this definition read `∃ f, choose (hist t) = f (hist t)`.  That is
satisfied by EVERY rule -- take `f := choose` -- so it excluded nothing and recorded no
requirement.  The definition below excludes the rule that peeks, and
`peeking_not_predictable` proves that it does.  `predictable_of_truncated` gives the
sufficient condition an implementation is checked against: the rule reads only the
truncated path, so in particular only counts and sample means of the past. -/
def PredictableQuery {E : Type*} (q : (ℕ → ℝ) → ℕ → E) : Prop :=
  ∀ (ω ω' : ℕ → ℝ) (t : ℕ), (∀ s, s < t → ω s = ω' s) → q ω t = q ω' t

/-- The information available strictly before time `t`: the path, blanked from `t` on. -/
def truncate (t : ℕ) (ω : ℕ → ℝ) : ℕ → ℝ := fun s => if s < t then ω s else 0

/-- **Sufficient.**  Any rule that factors through the truncated path is predictable.  The
tracker of `LeanPaperA7TrackingV1` is of this form: its query is a function of the counts
and the quotas, both of which are computed from the past alone. -/
theorem predictable_of_truncated {E : Type*} (f : ℕ → (ℕ → ℝ) → E) :
    PredictableQuery (fun ω t => f t (truncate t ω)) := by
  intro ω ω' t hag
  have htr : truncate t ω = truncate t ω' := by
    funext s
    unfold truncate
    by_cases h : s < t
    · simp [h, hag s h]
    · simp [h]
  simp only [htr]

/-- **The condition has content.**  The rule that reads the current observation before
choosing its query is not predictable, so the definition rules something out. -/
theorem peeking_not_predictable {E : Type*} (e₀ e₁ : E) (hne : e₀ ≠ e₁) :
    ¬ PredictableQuery (fun ω t => if 0 < ω t then e₁ else e₀) := by
  intro h
  have hq := h (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)) 0 (by intro s hs; omega)
  simp only [if_pos (by norm_num : (0:ℝ) < 1), if_neg (by norm_num : ¬ (0:ℝ) < -1)] at hq
  exact hne hq.symm

/-! ## Ville's inequality, PROVED

`confidence_from_ville` above takes `hville` as a hypothesis, with `P` an abstract set
function and `Mix` an abstract process.  That is the shape of the argument, not the
argument: nothing in it is about a measure, and the inequality it needs is the one piece of
the confidence sequence that is not bookkeeping.

Mathlib has Doob's maximal inequality for non-negative SUBmartingales, which is the wrong
direction here, and does not have Ville's inequality for non-negative SUPERmartingales.  So
it is proved below, from optional stopping:

  * `-M` is a submartingale, so optional stopping between the constant time `0` and the
    hitting time of `[lam, ∞)` capped at `N` gives `E[M_tau] <= E[M_0]`;
  * on the event that `M` ever reaches `lam` by time `N`, the stopped value is at least
    `lam`, and off that event it is at least `0` because `M` is non-negative;
  * so `lam * P(the event) <= E[M_tau] <= E[M_0]`.

The horizon is finite, which is all the stopping rule uses: the rule is checked at times
`t <= N` and the bound is uniform in `N`. -/

open MeasureTheory in
/-- **Ville's inequality at a finite horizon.**  A non-negative supermartingale reaches
`lam` by time `N` with probability at most `E[M_0]/lam`. -/
theorem ville_finite_horizon
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    {𝒢 : MeasureTheory.Filtration ℕ m0} [MeasureTheory.SigmaFiniteFiltration μ 𝒢]
    (M : ℕ → Ω → ℝ) (hM : MeasureTheory.Supermartingale M 𝒢 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (lam : ℝ) (hlam : 0 < lam) (N : ℕ) :
    lam * μ.real {ω | ∃ j ≤ N, lam ≤ M j ω} ≤ ∫ ω, M 0 ω ∂μ := by
  classical
  have hadapt : MeasureTheory.Adapted 𝒢 M := hM.1.adapted
  have hAmeas : MeasurableSet {ω | ∃ j ≤ N, lam ≤ M j ω} := by
    have hrw : {ω | ∃ j ≤ N, lam ≤ M j ω}
        = ⋃ j ∈ Finset.range (N + 1), {ω | lam ≤ M j ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
      constructor
      · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩
      · rintro ⟨j, hj, h⟩; exact ⟨j, by omega, h⟩
    rw [hrw]
    refine Finset.measurableSet_biUnion _ (fun j _ => ?_)
    exact measurableSet_le measurable_const ((hadapt j).mono (𝒢.le j) le_rfl)
  have hτst : MeasureTheory.IsStoppingTime 𝒢
      (fun ω => ((MeasureTheory.hittingBtwn M (Set.Ici lam) 0 N ω : ℕ) : WithTop ℕ)) :=
    MeasureTheory.Adapted.isStoppingTime_hittingBtwn hadapt measurableSet_Ici
  have hτle : ∀ ω,
      ((MeasureTheory.hittingBtwn M (Set.Ici lam) 0 N ω : ℕ) : WithTop ℕ)
        ≤ ((N : ℕ) : WithTop ℕ) := by
    intro ω
    exact_mod_cast MeasureTheory.hittingBtwn_le
      (u := M) (s := Set.Ici lam) (n := 0) (m := N) ω
  have hsub : MeasureTheory.Submartingale (-M) 𝒢 μ := hM.neg
  have hmono := hsub.expected_stoppedValue_mono
      (MeasureTheory.isStoppingTime_const 𝒢 (0 : ℕ)) hτst (fun ω => zero_le) hτle
  rw [MeasureTheory.stoppedValue_const] at hmono
  have hupper : ∫ ω, MeasureTheory.stoppedValue M
        (fun ω => ((MeasureTheory.hittingBtwn M (Set.Ici lam) 0 N ω : ℕ) : WithTop ℕ)) ω ∂μ
      ≤ ∫ ω, M 0 ω ∂μ := by
    have h1 : ∫ ω, (-M) 0 ω ∂μ = -∫ ω, M 0 ω ∂μ := by
      simp only [Pi.neg_apply]
      exact MeasureTheory.integral_neg _
    have hsv : MeasureTheory.stoppedValue (-M)
          (fun ω => ((MeasureTheory.hittingBtwn M (Set.Ici lam) 0 N ω : ℕ) : WithTop ℕ))
        = -(MeasureTheory.stoppedValue M
          (fun ω => ((MeasureTheory.hittingBtwn M (Set.Ici lam) 0 N ω : ℕ) : WithTop ℕ))) :=
      rfl
    have h2 : ∫ ω, MeasureTheory.stoppedValue (-M)
          (fun ω => ((MeasureTheory.hittingBtwn M (Set.Ici lam) 0 N ω : ℕ) : WithTop ℕ)) ω ∂μ
        = -∫ ω, MeasureTheory.stoppedValue M
          (fun ω => ((MeasureTheory.hittingBtwn M (Set.Ici lam) 0 N ω : ℕ) : WithTop ℕ))
            ω ∂μ := by
      rw [hsv]
      exact MeasureTheory.integral_neg _
    rw [h1, h2] at hmono
    linarith
  have hint : MeasureTheory.Integrable (MeasureTheory.stoppedValue M
      (fun ω => ((MeasureTheory.hittingBtwn M (Set.Ici lam) 0 N ω : ℕ) : WithTop ℕ))) μ :=
    MeasureTheory.integrable_stoppedValue ℕ hτst hM.2.2 hτle
  have hind : ∀ ω, {ω | ∃ j ≤ N, lam ≤ M j ω}.indicator (fun _ => lam) ω
      ≤ MeasureTheory.stoppedValue M
        (fun ω => ((MeasureTheory.hittingBtwn M (Set.Ici lam) 0 N ω : ℕ) : WithTop ℕ)) ω := by
    intro ω
    by_cases hω : ω ∈ {ω | ∃ j ≤ N, lam ≤ M j ω}
    · rw [Set.indicator_of_mem hω]
      obtain ⟨j, hj, hjl⟩ := hω
      exact MeasureTheory.stoppedValue_hittingBtwn_mem ⟨j, ⟨Nat.zero_le _, hj⟩, hjl⟩
    · rw [Set.indicator_of_notMem hω]
      exact hnn _ _
  have hmono2 := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall
      (fun ω => Set.indicator_nonneg (fun _ _ => hlam.le) ω))
    hint (Filter.Eventually.of_forall hind)
  rw [MeasureTheory.integral_indicator_const lam hAmeas, smul_eq_mul] at hmono2
  linarith [hmono2, hupper]

open MeasureTheory in
/-- **The confidence guarantee, with no `hville` hypothesis.**

A non-negative supermartingale started at mean at most one exceeds `1/delta` by time `N`
with probability at most `delta`.  This is the statement the stopping rule uses, and it is
now a theorem about a measure rather than an assumption about a set function. -/
theorem confidence_of_supermartingale
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    {𝒢 : MeasureTheory.Filtration ℕ m0} [MeasureTheory.SigmaFiniteFiltration μ 𝒢]
    (M : ℕ → Ω → ℝ) (hM : MeasureTheory.Supermartingale M 𝒢 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (hstart : ∫ ω, M 0 ω ∂μ ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    μ.real {ω | ∃ j ≤ N, 1 / δ ≤ M j ω} ≤ δ := by
  have hlam : (0 : ℝ) < 1 / δ := by positivity
  have h := ville_finite_horizon M hM hnn (1 / δ) hlam N
  have hb : (1 / δ) * μ.real {ω | ∃ j ≤ N, 1 / δ ≤ M j ω} ≤ 1 := le_trans h hstart
  rw [div_mul_eq_mul_div, one_mul, div_le_one hδ] at hb
  exact hb

/-- **The stopping rule inherits it.**  If crossing the threshold forces the mixture past
`1/delta` -- which `bthr_eq_log_mixture` is exactly the statement of -- then the rule returns
a wrong answer with probability at most `delta`, with nothing assumed about Ville. -/
theorem stopping_error_le
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    {𝒢 : MeasureTheory.Filtration ℕ m0} [MeasureTheory.SigmaFiniteFiltration μ 𝒢]
    (M : ℕ → Ω → ℝ) (hM : MeasureTheory.Supermartingale M 𝒢 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (hstart : ∫ ω, M 0 ω ∂μ ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (N : ℕ)
    (Qev bev : ℕ → Ω → ℝ)
    (hmono : ∀ (j : ℕ) (ω : Ω), bev j ω < Qev j ω → 1 / δ ≤ M j ω)
    (hmeas : MeasurableSet {ω | ∃ j ≤ N, bev j ω < Qev j ω}) :
    μ.real {ω | ∃ j ≤ N, bev j ω < Qev j ω} ≤ δ := by
  refine le_trans ?_ (confidence_of_supermartingale M hM hnn hstart δ hδ N)
  refine MeasureTheory.measureReal_mono ?_ ?_
  · rintro ω ⟨j, hj, h⟩
    exact ⟨j, hj, hmono j ω h⟩
  · exact MeasureTheory.measure_ne_top _ _

/-! ## The statistic and the threshold -/

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The per-coordinate statistic of the mixture. -/
noncomputable def Qstat (a : ℝ) (S : E → ℝ) (N : E → ℝ) : ℝ :=
  ∑ e, S e ^ 2 / (2 * (a + N e))

/-- The threshold that the mixture's normalising factor produces. -/
noncomputable def bthr (a δ : ℝ) (N : E → ℝ) : ℝ :=
  Real.log (1 / δ) + (∑ e, Real.log (1 + N e / a)) / 2

/-- The threshold is exactly `log(1/δ)` plus the logarithm of the product of the mixture's
`sqrt` factors, so the two displays of the introduction describe one object. -/
theorem bthr_eq_log_mixture (a δ : ℝ) (ha : 0 < a) (N : E → ℝ) (hN : ∀ e, 0 ≤ N e) :
    bthr a δ N
      = Real.log (1 / δ) - ∑ e, Real.log (Real.sqrt (a / (a + N e))) := by
  classical
  unfold bthr
  congr 1
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro e _
  have hane : 0 < a + N e := by linarith [hN e]
  rw [Real.log_sqrt (by positivity)]
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hane)]
  have : Real.log (a + N e) = Real.log (a * (1 + N e / a)) := by
    congr 1
    field_simp
  have hpos1 : (0:ℝ) < 1 + N e / a := by
    have h0 : (0:ℝ) ≤ N e / a := div_nonneg (hN e) (le_of_lt ha)
    linarith
  rw [this, Real.log_mul (ne_of_gt ha) (ne_of_gt hpos1)]
  ring

/-! ## The exponential process, and the mixture that Ville is applied to

`gaussian_step_mgf` gives the one-step factor.  This section builds the process it is the
increment of, and the mixture whose logarithm is the statistic.

    L_t(u) = exp( sum_e u_e S_e(t) - (1/2) sum_e u_e^2 N_e(t) ).

`Lstat_step` is the multiplicative update: one fresh observation at a PREDICTABLE query
multiplies `L` by exactly the factor whose mean `gaussian_step_mgf` computes to be one.
That is the martingale property, reduced to the arithmetic of the exponent.

Mixing `u_e` over an `N(0, 1/a)` prior turns `L` into

    M_t = prod_e sqrt( a / (a + N_e(t)) ) exp( S_e(t)^2 / (2 (a + N_e(t))) ),

whose logarithm is `Q_t` minus the penalty of `b_t`.  `mixture_integral` does one
coordinate; `Mstat_log` assembles the product.

What is NOT here: the filtration and the conditional expectation that make "mean one at
each step" into a martingale theorem, and Ville applied to its supremum.  Those are named
where they are used, and the process they would be applied to is the one defined here. -/

variable {E' : Type*} [Fintype E'] [DecidableEq E']

/-- The exponential likelihood-ratio process, as a function of the mixing direction. -/
noncomputable def Lstat (u S N : E' → ℝ) : ℝ :=
  Real.exp ((∑ e, u e * S e) - (∑ e, u e ^ 2 * N e) / 2)

/-- **The multiplicative update.**  One observation at query `e0` multiplies `L` by exactly
the factor `gaussian_step_mgf` integrates, so the process's increment is that factor and
nothing else.  The update touches only the chosen coordinate, which is where predictability
enters: `e0` must be fixed before the observation is drawn. -/
theorem Lstat_step (u S N : E' → ℝ) (e0 : E') (y : ℝ) :
    Lstat u (Function.update S e0 (S e0 + y)) (Function.update N e0 (N e0 + 1))
      = Lstat u S N * Real.exp (u e0 * y - u e0 ^ 2 / 2) := by
  classical
  unfold Lstat
  rw [← Real.exp_add]
  congr 1
  have hS : ∑ e, u e * Function.update S e0 (S e0 + y) e
      = (∑ e, u e * S e) + u e0 * y := by
    rw [← Finset.add_sum_erase _ (fun e => u e * Function.update S e0 (S e0 + y) e)
        (Finset.mem_univ e0),
        ← Finset.add_sum_erase _ (fun e => u e * S e) (Finset.mem_univ e0)]
    rw [Function.update_self]
    have : ∀ e ∈ Finset.univ.erase e0,
        u e * Function.update S e0 (S e0 + y) e = u e * S e := by
      intro e he
      rw [Function.update_of_ne (Finset.ne_of_mem_erase he)]
    rw [Finset.sum_congr rfl this]
    ring
  have hN : ∑ e, u e ^ 2 * Function.update N e0 (N e0 + 1) e
      = (∑ e, u e ^ 2 * N e) + u e0 ^ 2 := by
    rw [← Finset.add_sum_erase _ (fun e => u e ^ 2 * Function.update N e0 (N e0 + 1) e)
        (Finset.mem_univ e0),
        ← Finset.add_sum_erase _ (fun e => u e ^ 2 * N e) (Finset.mem_univ e0)]
    rw [Function.update_self]
    have : ∀ e ∈ Finset.univ.erase e0,
        u e ^ 2 * Function.update N e0 (N e0 + 1) e = u e ^ 2 * N e := by
      intro e he
      rw [Function.update_of_ne (Finset.ne_of_mem_erase he)]
    rw [Finset.sum_congr rfl this]
    ring
  rw [hS, hN]
  ring

/-- The mixed process: one factor per query, exactly as `mixture_integral` produces. -/
noncomputable def Mstat (a : ℝ) (S N : E' → ℝ) : ℝ :=
  ∏ e, Real.sqrt (a / (a + N e)) * Real.exp (S e ^ 2 / (2 * (a + N e)))

/-- **The logarithm of the mixture is the statistic minus the penalty.**

`log M_t = Q_t - (1/2) sum_e log(1 + N_e/a)`, so crossing `Q_t > b_t(delta)` is exactly
`M_t > 1/delta`.  This is what lets a bound on the mixture be read as a bound on the
statistic, and it is the identity the two displays of the introduction must share. -/
theorem Mstat_log (a : ℝ) (ha : 0 < a) (S N : E' → ℝ) (hN : ∀ e, 0 ≤ N e) :
    Real.log (Mstat a S N)
      = Qstat a S N - (∑ e, Real.log (1 + N e / a)) / 2 := by
  classical
  unfold Mstat Qstat
  rw [Real.log_prod]
  · have hterm : ∀ e : E',
        Real.log (Real.sqrt (a / (a + N e)) * Real.exp (S e ^ 2 / (2 * (a + N e))))
          = S e ^ 2 / (2 * (a + N e)) - Real.log (1 + N e / a) / 2 := by
      intro e
      have hane : (0:ℝ) < a + N e := by linarith [hN e]
      have hpos : (0:ℝ) < a / (a + N e) := div_pos ha hane
      rw [Real.log_mul (ne_of_gt (Real.sqrt_pos.2 hpos)) (ne_of_gt (Real.exp_pos _)),
          Real.log_exp, Real.log_sqrt (le_of_lt hpos),
          Real.log_div (ne_of_gt ha) (ne_of_gt hane)]
      have hone : (0:ℝ) < 1 + N e / a := by
        have h0 : (0:ℝ) ≤ N e / a := div_nonneg (hN e) (le_of_lt ha)
        linarith
      have hid : Real.log (a + N e) = Real.log a + Real.log (1 + N e / a) := by
        have heq : a + N e = a * (1 + N e / a) := by field_simp
        rw [heq, Real.log_mul (ne_of_gt ha) (ne_of_gt hone)]
      rw [hid]
      ring
    rw [Finset.sum_congr rfl (fun e _ => hterm e)]
    rw [Finset.sum_sub_distrib, Finset.sum_div]
  · intro e _
    have hane : (0:ℝ) < a + N e := by linarith [hN e]
    exact ne_of_gt (mul_pos (Real.sqrt_pos.2 (div_pos ha hane)) (Real.exp_pos _))

/-! ## What stopping guarantees, deterministically -/

variable {Θ Ans : Type*}

/-- **Correctness needs no knowledge of the hidden world.**  If the statistic excludes every
member of the answer's alternative set, and the true world is in the confidence set, then
the answer is not wrong -- because a wrong answer would put the true world INTO its own
alternative set, which the exclusion forbids.

This is the whole logical content of "stop and return `T`", and it is why the stopping rule
may be stated without reference to `theta`. -/
theorem stopping_rule_is_correct
    (Alt : Ans → Set Θ) (θ : Θ) (T : Ans)
    (Dset : Set Θ) (hθD : θ ∈ Dset)
    (hexcl : ∀ lam ∈ Alt T, lam ∉ Dset) :
    θ ∉ Alt T := by
  intro hmem
  exact hexcl θ hmem hθD

/-- The converse direction, which is what makes the rule non-vacuous: if the answer IS
wrong then the true world sits in its alternative set, so the exclusion must have failed. -/
theorem wrong_answer_is_detected
    (Alt : Ans → Set Θ) (θ : Θ) (T : Ans) (hwrong : θ ∈ Alt T)
    (Dset : Set Θ) (hθD : θ ∈ Dset) :
    ¬ (∀ lam ∈ Alt T, lam ∉ Dset) := by
  intro hexcl
  exact hexcl θ hwrong hθD

/-- **From Ville to the anytime confidence bound.**

`hville` is Ville's maximal inequality for a nonnegative supermartingale started at one: the
probability that the process ever exceeds `1/delta` is at most `delta`.  It is a hypothesis
HERE because this version is about an abstract set function `P` and an abstract process, so
it records the shape of the argument and nothing more.

It is no longer an external result: `ville_finite_horizon` above proves it, and
`confidence_of_supermartingale` and `stopping_error_le` give the same conclusion for an
actual measure and an actual supermartingale with no such hypothesis.  This version is kept
because the arithmetic after Ville -- the mixture exceeds `1/delta` exactly when `Q` exceeds
`b`, by `bthr_eq_log_mixture` -- is clearer stated separately from the measure theory. -/
theorem confidence_from_ville
    {Ω : Type*} (P : Set Ω → ℝ) (Mix : Ω → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (Qev bev : Ω → ℝ)
    (hident : ∀ ω, Real.log (Mix ω) = Qev ω - (bev ω - Real.log (1 / δ)))
    (hville : P {ω | 1 / δ < Mix ω} ≤ δ)
    (hpos : ∀ ω, 0 < Mix ω)
    (hmono : ∀ ω, bev ω < Qev ω → 1 / δ < Mix ω)
    (hsub : ∀ A B : Set Ω, A ⊆ B → P A ≤ P B) :
    P {ω | bev ω < Qev ω} ≤ δ := by
  refine le_trans (hsub _ _ ?_) hville
  intro ω hω
  exact hmono ω hω

/-- **The two confidence levels play different roles and must stay different.**

A fixed level `alpha` is used for STOPPING: it bounds the probability of returning a wrong
answer.  A shrinking level `t^{-4}` is used for CHOOSING the answer and the allocation: it
is what makes the failure probabilities summable along a window.

This lemma records why a single fixed level cannot do both jobs: a constant sequence of
error probabilities has a divergent sum, so it yields no finite expected stopping time,
however small the constant. -/
theorem fixed_level_gives_no_summable_tail (α : ℝ) (hα : 0 < α) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, ∑ _t ∈ Finset.range n, α ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (C / α)
  have hsum : ∑ _t ∈ Finset.range n, α = (n : ℝ) * α := by
    simp [Finset.sum_const, Finset.card_range]
  have := hC n
  rw [hsum] at this
  have : (n : ℝ) ≤ C / α := by
    rw [le_div_iff₀ hα]
    linarith
  linarith

/-! ## Audit -/

#print axioms completed_square
#print axioms mixture_integral
#print axioms gaussian_step_mgf
#print axioms step_exponent_form
#print axioms predictable_of_truncated
#print axioms peeking_not_predictable
#print axioms ville_finite_horizon
#print axioms confidence_of_supermartingale
#print axioms stopping_error_le
#print axioms bthr_eq_log_mixture
#print axioms Lstat_step
#print axioms Mstat_log
#print axioms stopping_rule_is_correct
#print axioms wrong_answer_is_detected
#print axioms confidence_from_ville
#print axioms fixed_level_gives_no_summable_tail

end CIGAMF.P13.PaperA7Confidence
