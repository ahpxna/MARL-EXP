import Mathlib

/-!
# A freezing lemma, and the conditional one-step identity it licenses

`LeanPaperAMartingaleV1` proves the one-step Gaussian identity

    E[ f_{n+1}(s + Z) ] = f_n(s),      Z ~ N(0,1),

for FIXED `n` and `s`.  The martingale property of the closed-form process needs it at a
RANDOM past: `n = N_e(t)` and `s = S_e(t)` are `F_t`-measurable, and the next innovation is
independent of `F_t`.  Substituting a random argument into an identity about fixed
arguments is not automatic, and the wrong way to do it --- arguing that `S_e` given `N_e` is
Gaussian --- is FALSE under adaptive sampling, since the stopping of the count depends on
the observations.

The right statement is the freezing lemma: for `X` measurable and `Y` independent of `X`,

    E[ f(X, Y) | sigma(X) ]  =  (x -> integral of f(x, .) against the law of Y)  at  x = X.

Mathlib has no such lemma, but it has the pieces: independence makes the joint law a
product, a product is a composition with a constant kernel, and `condDistrib` is
characterised by that composition.  So the conditional distribution of `Y` given `X` is the
constant kernel at `Y`'s law, and `condExp_prod_ae_eq_integral_condDistrib'` finishes.

`condExp_freeze_apply` is the form the martingale step uses: the inner integral is evaluated
by the fixed-argument identity, pointwise in the frozen variable.
-/

namespace CIGAMF.P13.PaperAFreeze

open MeasureTheory ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {μ : Measure α} [IsFiniteMeasure μ]

/-- **Independence makes the conditional distribution constant.** -/
theorem condDistrib_const_of_indepFun
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (X : α → β) (Y : α → Ω) (hX : Measurable X) (hY : Measurable Y)
    [IsFiniteMeasure (μ.map Y)]
    (hindep : IndepFun X Y μ) :
    ⇑(condDistrib Y X μ) =ᵐ[μ.map X] ⇑(Kernel.const β (μ.map Y)) := by
  refine condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hX hY ?_
  have hprod : Measure.map (fun a => (X a, Y a)) μ = (μ.map X).prod (μ.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hindep
  rw [hprod, Measure.compProd_const]

/-- **The freezing lemma.**  Conditioning on `X` freezes `X` and integrates `Y` out against
its own law. -/
theorem condExp_freeze
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (X : α → β) (Y : α → Ω) (hX : Measurable X) (hY : Measurable Y)
    [IsFiniteMeasure (μ.map Y)]
    (hindep : IndepFun X Y μ)
    (f : β × Ω → ℝ) (hf : Integrable f (μ.map (fun a => (X a, Y a)))) :
    μ[fun a => f (X a, Y a) | MeasurableSpace.comap X mβ]
      =ᵐ[μ] fun a => ∫ y, f (X a, y) ∂(μ.map Y) := by
  have h1 := condExp_prod_ae_eq_integral_condDistrib' (μ := μ) (X := X) (Y := Y) (f := f)
    hX hY.aemeasurable hf
  refine h1.trans ?_
  have h2 := condDistrib_const_of_indepFun (μ := μ) X Y hX hY hindep
  have h3 : ∀ᵐ a ∂μ, (condDistrib Y X μ) (X a) = (Kernel.const β (μ.map Y)) (X a) :=
    ae_of_ae_map hX.aemeasurable h2
  filter_upwards [h3] with a ha
  rw [ha]
  rfl

/-- **The freezing lemma, with the inner integral already evaluated.**  This is the form a
one-step identity is substituted into: `hval` is the identity at FIXED arguments, and the
conclusion is the same identity at the random past. -/
theorem condExp_freeze_apply
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (X : α → β) (Y : α → Ω) (hX : Measurable X) (hY : Measurable Y)
    [IsFiniteMeasure (μ.map Y)]
    (hindep : IndepFun X Y μ)
    (f : β × Ω → ℝ) (hf : Integrable f (μ.map (fun a => (X a, Y a))))
    (g : β → ℝ) (hval : ∀ b : β, ∫ y, f (b, y) ∂(μ.map Y) = g b) :
    μ[fun a => f (X a, Y a) | MeasurableSpace.comap X mβ]
      =ᵐ[μ] fun a => g (X a) := by
  refine (condExp_freeze X Y hX hY hindep f hf).trans ?_
  filter_upwards with a
  exact hval (X a)

/-! ## Audit -/

#print axioms condDistrib_const_of_indepFun
#print axioms condExp_freeze
#print axioms condExp_freeze_apply

end CIGAMF.P13.PaperAFreeze
