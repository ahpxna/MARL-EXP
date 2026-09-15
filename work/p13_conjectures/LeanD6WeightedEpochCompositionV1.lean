import «LeanD6EpochMarginalLawV1»

/-! # Step 2: the length-weighted composition, and why it is `O(log T)`

`LeanD6MultiEpochCompositionV1` summed per-epoch bounds WITHOUT weights, under a
budget split, and found an `E^2` penalty minimised by the equal split.  That is a
correct theorem about the wrong functional for this design.  The corpus itself
says which functional is right: `LeanD6RepeatedDiscoveryV1.badEpochWork` is
`∑' s, indicator(bad at s) * 2^s`, weighted by the epoch's allocation length,
and `allocation_epoch_lengths` in `d6_revalidation_epochs.json` doubles --
18432, 36864, 73728, ... over twelve epochs.

Under doubling allocation `L s = L0*2^s` and a per-epoch bound
`est/L s + V*4^(-s)`, the weighted total telescopes:

  `∑_{s<E} L s * (est/L s + V*4^(-s)) = E*est + L0*V*∑_{s<E} 2^s*4^(-s)`

and `2^s*4^(-s) = 2^(-s)` sums to at most `2`.  So the total is
`E*est + 2*L0*V`: **linear in the number of epochs**, and since the total
allocation is `L0*(2^E - 1)`, linear in `E` is logarithmic in the budget.  The
revalidation schedule is what makes the second half a convergent series rather
than a growing one -- the same `2^s` against `4^(-s)` cancellation that
`expected_bad_epoch_work` already uses.

Scope.  These are inequalities about sums of bounds.  They become a statement
about a run only when composed with `LeanD6EpochMarginalLawV1.epoch_weighted_le`
(which supplies the per-epoch expectations with no conditioning) and with a D6
instantiation supplying `IsProbabilityMeasure` for the per-epoch observation
laws.  That instantiation is not in this file.  Nothing here proves a matching
lower bound, so `O(log T)` is an upper bound on this algorithm, not a rate for
the problem.
-/
namespace CIGAMF.P13.D6WeightedEpochComposition
open scoped BigOperators ENNReal
open Finset MeasureTheory
noncomputable section

/-- The cancellation that makes the revalidation series converge.  Same step as
in `expected_bad_epoch_work`. -/
lemma two_mul_quarter_pow (s : ℕ) : (2:ℝ≥0∞)^s*(4⁻¹:ℝ≥0∞)^s = (2⁻¹:ℝ≥0∞)^s := by
  have he : (2:ℝ≥0∞)*4⁻¹=2⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  rw [← mul_pow,he]

/-- Core composition: a per-epoch bound of the shape `est + c*2^(-s)` sums, over
`E` epochs, to `E*est + 2*c`.  The first summand is what grows with the epoch
count; the second is a convergent series and is paid once. -/
theorem weighted_epoch_total {u : ℕ → ℝ≥0∞} (est c : ℝ≥0∞) (E : ℕ)
    (hu : ∀ s,u s ≤ est+c*(2⁻¹:ℝ≥0∞)^s) :
    ∑ s ∈ Finset.range E,u s ≤ (E:ℝ≥0∞)*est+2*c := by
  calc ∑ s ∈ Finset.range E,u s
      ≤ ∑ s ∈ Finset.range E,(est+c*(2⁻¹:ℝ≥0∞)^s) := Finset.sum_le_sum (fun s _ => hu s)
    _ = (E:ℝ≥0∞)*est+c*∑ s ∈ Finset.range E,(2⁻¹:ℝ≥0∞)^s := by
        rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
          ← Finset.mul_sum]
    _ ≤ (E:ℝ≥0∞)*est+c*∑' s : ℕ,(2⁻¹:ℝ≥0∞)^s := by
        gcongr
        exact ENNReal.sum_le_tsum _
    _ = (E:ℝ≥0∞)*est+2*c := by rw [ENNReal.tsum_geometric_two]; ring

/-- Doubling form.  `hu` is exactly the one-epoch bound multiplied by the
epoch's own length: the estimation half loses its `1/L` and becomes the constant
`est`, the label half keeps `L0*V` and picks up `2^s*4^(-s) = 2^(-s)`. -/
theorem doubling_epoch_total {u : ℕ → ℝ≥0∞} (est V L0 : ℝ≥0∞) (E : ℕ)
    (hu : ∀ s,u s ≤ est+L0*V*((2:ℝ≥0∞)^s*(4⁻¹:ℝ≥0∞)^s)) :
    ∑ s ∈ Finset.range E,u s ≤ (E:ℝ≥0∞)*est+2*(L0*V) := by
  refine weighted_epoch_total est (L0*V) E (fun s => ?_)
  rw [← two_mul_quarter_pow s]
  exact hu s

/-- The total allocation actually spent by `E` doubling epochs.  With
`L0*(2^E-1)` rounds bought, a bound linear in `E` is logarithmic in the spend. -/
lemma doubling_budget (L0 E : ℕ) : ∑ s ∈ Finset.range E,L0*2^s = L0*(2^E-1) := by
  induction E with
  | zero => simp
  | succ n ih =>
    have h1 : 1 ≤ 2^n := Nat.one_le_two_pow
    rw [Finset.sum_range_succ,ih,pow_succ]
    cases' Nat.eq_zero_or_pos L0 with h h
    · simp [h]
    · have h2 : L0*(2^n-1)+L0*2^n = L0*(2^n*2-1) := by
        have : 2^n*2-1 = (2^n-1)+2^n := by omega
        rw [this,Nat.mul_add]
      exact h2

/-- Sanity: with a single epoch the composition is the one-epoch bound again,
so the `E` factor is not an artefact of the bookkeeping. -/
theorem one_epoch_consistent {u : ℕ → ℝ≥0∞} (est c : ℝ≥0∞)
    (hu : ∀ s,u s ≤ est+c*(2⁻¹:ℝ≥0∞)^s) :
    ∑ s ∈ Finset.range 1,u s ≤ est+c := by
  have h := hu 0
  simpa using h

#print axioms two_mul_quarter_pow
#print axioms weighted_epoch_total
#print axioms doubling_epoch_total
#print axioms doubling_budget
#print axioms one_epoch_consistent
end
end CIGAMF.P13.D6WeightedEpochComposition
