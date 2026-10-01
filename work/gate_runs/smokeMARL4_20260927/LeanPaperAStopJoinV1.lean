import «LeanPaperAAdaptMartV1»

/-!
# Paper A7: joining the closed-form process to the implementation's own rule

The fifth obligation of `LeanPaperAMartingaleV1`: the process proved a martingale must be
the object the code actually thresholds, and the threshold crossing must be the event Ville
bounds.

Three steps, and none of them is a redefinition.

* `Mval_eq_Mstat` --- the process of `LeanPaperAAdaptMartV1` IS `Mstat`, the implementation's
  mixture, with the counts cast to reals.  This is an identity, not a naming convention.
* `threshold_crossing` --- crossing `Q_t > b_t(delta)` forces `M_t >= 1/delta`.  The penalty
  `(1/2) sum_e log(1 + N_e/a)` sits on both sides and cancels, which is exactly why the
  threshold carries it rather than a bound on it.
* `closed_form_error_bound` --- assembling the one-step conditional equalities into a
  Mathlib `Martingale`, hence a supermartingale, and feeding it to `stopping_error_le`.

What is still NOT proved here: that the implementation's `q_t`, `N_e(t)` and `S_e(t)` are the
`qf`, `Nf`, `Sf` of the model.  That identification is a statement about the code, not about
the mathematics, and it is the only thing between this module and a rate attached to the
running algorithm.
-/

namespace CIGAMF.P13.PaperAStopJoin

open MeasureTheory
open CIGAMF.P13.PaperA7Confidence
open CIGAMF.P13.PaperAMartingale
open CIGAMF.P13.PaperAAdaptMart

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E]
  [MeasurableSingletonClass E]
variable {β : Type*} [MeasurableSpace β]

/-- **The process is the implementation's mixture.** -/
theorem Mval_eq_Mstat (a : ℝ) (Nf : β → E → ℕ) (Sf : β → E → ℝ) (x : β) :
    Mval a Nf Sf x = Mstat a (Sf x) (fun e => (Nf x e : ℝ)) := rfl

/-- **Crossing the implementation's threshold forces the mixture past `1/delta`.**  The
penalty cancels; that is the content. -/
theorem threshold_crossing (a δ : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (S N : E → ℝ) (hN : ∀ e, 0 ≤ N e)
    (hcross : bthr a δ N < Qstat a S N) :
    1 / δ ≤ Mstat a S N := by
  have hMpos : 0 < Mstat a S N := by
    unfold Mstat
    refine Finset.prod_pos (fun e _ => ?_)
    have hane : (0 : ℝ) < a + N e := by linarith [hN e]
    exact mul_pos (Real.sqrt_pos.mpr (div_pos ha hane)) (Real.exp_pos _)
  have hlog := Mstat_log a ha S N hN
  unfold bthr at hcross
  have hstep : Real.log (1 / δ) < Real.log (Mstat a S N) := by
    rw [hlog]
    unfold Qstat at hcross
    unfold Qstat
    linarith
  have hδinv : (0 : ℝ) < 1 / δ := by positivity
  exact le_of_lt ((Real.log_lt_log_iff hδinv hMpos).mp hstep)

/-- **The error bound at the implementation's rule.**  The one-step conditional equalities
become a martingale, the martingale a supermartingale, and the crossing event is contained
in the event Ville bounds. -/
theorem closed_form_error_bound
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ m0} [SigmaFiniteFiltration μ 𝒢]
    (a δ : ℝ) (ha : 0 < a) (hδ : 0 < δ)
    (Ncount : ℕ → Ω → E → ℝ) (Ssum : ℕ → Ω → E → ℝ)
    (hNnn : ∀ t ω e, 0 ≤ Ncount t ω e)
    (M : ℕ → Ω → ℝ) (hM : ∀ t ω, M t ω = Mstat a (Ssum t ω) (Ncount t ω))
    (hadapt : StronglyAdapted 𝒢 M) (hint : ∀ t, Integrable (M t) μ)
    (hstep : ∀ t, μ[M (t + 1) | 𝒢 t] =ᵐ[μ] M t)
    (hstart : ∫ ω, M 0 ω ∂μ ≤ 1) (T : ℕ)
    (hmeas : MeasurableSet {ω | ∃ j ≤ T,
      bthr a δ (Ncount j ω) < Qstat a (Ssum j ω) (Ncount j ω)}) :
    μ.real {ω | ∃ j ≤ T,
      bthr a δ (Ncount j ω) < Qstat a (Ssum j ω) (Ncount j ω)} ≤ δ := by
  have hmart : Martingale M 𝒢 μ := martingale_nat hadapt hint (fun t => (hstep t).symm)
  have hnn : ∀ t ω, 0 ≤ M t ω := by
    intro t ω
    rw [hM t ω]
    unfold Mstat
    refine Finset.prod_nonneg (fun e _ => ?_)
    have hane : (0 : ℝ) < a + Ncount t ω e := by linarith [hNnn t ω e]
    exact le_of_lt (mul_pos (Real.sqrt_pos.mpr (div_pos ha hane)) (Real.exp_pos _))
  refine stopping_error_le M hmart.supermartingale hnn hstart δ hδ T
    (fun j ω => Qstat a (Ssum j ω) (Ncount j ω))
    (fun j ω => bthr a δ (Ncount j ω)) (fun j ω hcross => ?_) hmeas
  rw [hM j ω]
  exact threshold_crossing a δ ha hδ (Ssum j ω) (Ncount j ω) (fun e => hNnn j ω e) hcross

/-! ## Audit -/

#print axioms Mval_eq_Mstat
#print axioms threshold_crossing
#print axioms closed_form_error_bound

end CIGAMF.P13.PaperAStopJoin
