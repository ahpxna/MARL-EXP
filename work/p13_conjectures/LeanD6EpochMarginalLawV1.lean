import Mathlib

/-! # Step 1: the epoch-`s` marginal IS the one-epoch law

The one-epoch theorem `actual_unknown_label_explicit_bound` is stated on
`(vectorPath ...).prod (observations ...)`.  To sum it over epochs one must know
what law epoch `s` sees inside a multi-epoch run.  The usual answer is a
conditional one -- a tower property on a filtration -- but this design does not
need it, and the reason is the earlier optimality result: the cyclic design `G`
is FIXED and A-free, so the law of the epoch-`s` observations does not depend on
what happened in epochs `0..s-1`.  History enters only through the decoder, and
`epochLoss` already charges a wrong decode.

So the multi-epoch law is one shared component (the discovery path, reused by
every epoch -- `epochSamples r0 s = r0*(s+1)` are nested prefixes of the SAME
sample) and one fresh component per epoch, and reading off epoch `s` is measure
preserving onto exactly the one-epoch product.  That is this module.

`epoch_weighted_lintegral` is the form the composition consumes: the expectation
of a length-weighted finite sum over epochs equals the weighted sum of the
one-epoch expectations, with no conditioning anywhere.

Scope: the index type is a `Fintype`, so this is a FINITE horizon of epochs --
`Fin E` -- which is all the `O(log T)` statement needs.  An infinite horizon
would need `Kernel.traj` and `traj_comp_partialTraj` instead; that is a
different module and is not claimed here.  Nothing here is D6-specific: the D6
instantiation, which must supply `IsProbabilityMeasure (observations ...)` from
`actual_design_law_exists`, is a separate step and is NOT done in this file.
-/
namespace CIGAMF.P13.D6EpochMarginalLaw
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
noncomputable section

variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {β : ι → Type*} [∀ i, MeasurableSpace (β i)]

/-- One shared component plus one fresh component per epoch. -/
def multiEpoch (mu : Measure α) (nu : (i : ι) → Measure (β i)) :
    Measure (α × (∀ i, β i)) := mu.prod (Measure.pi nu)

/-- Reading off the shared component together with epoch `i`'s own component. -/
def epochProj (i : ι) : α × (∀ j, β j) → α × β i := Prod.map id (Function.eval i)

lemma measurable_epochProj (i : ι) : Measurable (epochProj (α := α) (β := β) i) :=
  measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)

/-- The epoch-`i` marginal of the multi-epoch law is the one-epoch law. -/
theorem epoch_projection (mu : Measure α) [IsProbabilityMeasure mu]
    (nu : (i : ι) → Measure (β i)) [∀ i, IsProbabilityMeasure (nu i)] (i : ι) :
    MeasurePreserving (epochProj (α := α) (β := β) i) (multiEpoch mu nu) (mu.prod (nu i)) :=
  (MeasurePreserving.id mu).prod (measurePreserving_eval nu i)

/-- Consequently a one-epoch integrand may be integrated against the one-epoch
law, inside a multi-epoch run. -/
theorem epoch_lintegral (mu : Measure α) [IsProbabilityMeasure mu]
    (nu : (i : ι) → Measure (β i)) [∀ i, IsProbabilityMeasure (nu i)] (i : ι)
    {g : α × β i → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x,g (epochProj i x) ∂multiEpoch mu nu = ∫⁻ y,g y ∂(mu.prod (nu i)) :=
  (epoch_projection mu nu i).lintegral_comp hg

/-- The bridge the composition consumes: a length-weighted finite sum over
epochs has expectation equal to the weighted sum of one-epoch expectations. -/
theorem epoch_weighted_lintegral (mu : Measure α) [IsProbabilityMeasure mu]
    (nu : (i : ι) → Measure (β i)) [∀ i, IsProbabilityMeasure (nu i)]
    (w : ι → ℝ≥0∞) (g : (i : ι) → α × β i → ℝ≥0∞) (hg : ∀ i,Measurable (g i))
    (s : Finset ι) :
    ∫⁻ x,∑ i ∈ s,w i*g i (epochProj i x) ∂multiEpoch mu nu
      = ∑ i ∈ s,w i*∫⁻ y,g i y ∂(mu.prod (nu i)) := by
  rw [lintegral_finsetSum s (fun i _ => (show Measurable (fun x => w i*g i (epochProj i x)) from
    measurable_const.mul ((hg i).comp (measurable_epochProj i))))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [lintegral_const_mul (w i) (show Measurable (fun x => g i (epochProj i x)) from
    (hg i).comp (measurable_epochProj i)),
    epoch_lintegral mu nu i (hg i)]

/-- Monotone form: per-epoch bounds compose without any further hypothesis. -/
theorem epoch_weighted_le (mu : Measure α) [IsProbabilityMeasure mu]
    (nu : (i : ι) → Measure (β i)) [∀ i, IsProbabilityMeasure (nu i)]
    (w : ι → ℝ≥0∞) (g : (i : ι) → α × β i → ℝ≥0∞) (hg : ∀ i,Measurable (g i))
    (s : Finset ι) (bound : ι → ℝ≥0∞)
    (hb : ∀ i ∈ s,∫⁻ y,g i y ∂(mu.prod (nu i)) ≤ bound i) :
    ∫⁻ x,∑ i ∈ s,w i*g i (epochProj i x) ∂multiEpoch mu nu ≤ ∑ i ∈ s,w i*bound i := by
  rw [epoch_weighted_lintegral mu nu w g hg s]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hb i hi) (show 0 ≤ w i from zero_le))

#print axioms measurable_epochProj
#print axioms epoch_projection
#print axioms epoch_lintegral
#print axioms epoch_weighted_lintegral
#print axioms epoch_weighted_le
end
end CIGAMF.P13.D6EpochMarginalLaw
