import «LeanD6ActualMultiEpochRiskV1»

/-! # Both benchmark conventions for the acquisition half

`D6ActualMultiEpochRisk.acquisitionCost` counts every query the algorithm
issues: `4*d*r0*E` to discover `A`, and `d * ∑ s, L s` to run the cyclic design
while deployed.  Whether the second term is *regret* is not a fact about the
algorithm; it is a fact about what the comparator is assumed to pay.  The two
natural comparators are settled here, so no result downstream has to choose.

* `benchmarkMeasuring`: an oracle that already knows `A` and deploys the SAME
  cyclic design.  It pays `d * ∑ s, L s` as well, so that term cancels exactly
  and the regret is the discovery cost alone, `4*d*r0*E`, linear in the epoch
  count.
* `benchmarkFree`: an oracle that measures nothing.  Then the whole acquisition
  cost is regret, and under a doubling schedule it is at least `d*L0*(2^E - 1)`,
  which is the horizon itself.

Both are exact identities in `ℕ`; neither is an estimate.  The separation
theorem is the honest form of the `O(log T)` question: the same algorithm is
logarithmic against one comparator and linear in the horizon against the other.
-/
namespace CIGAMF.P13.D6AcquisitionBenchmark
open scoped BigOperators
open Finset
open CIGAMF.P13.D6ActualMultiEpochRisk
noncomputable section

/-- Comparator that knows `A` and still deploys the cyclic design: it pays the
per-step measurement cost but no discovery cost. -/
def benchmarkMeasuring (d E : ℕ) (L : Fin E → ℕ) : ℕ := d*∑ s,L s

/-- Comparator that pays nothing to measure. -/
def benchmarkFree : ℕ := 0

/-- Against a comparator that also measures, the deployment term cancels
exactly and the acquisition regret is the discovery cost alone. -/
theorem acquisition_regret_measuring (d r0 E : ℕ) (L : Fin E → ℕ) :
    acquisitionCost d r0 E L-benchmarkMeasuring d E L=4*d*r0*E := by
  unfold acquisitionCost benchmarkMeasuring
  exact Nat.add_sub_cancel _ _

/-- Against a comparator that measures nothing, the whole acquisition cost is
regret. -/
theorem acquisition_regret_free (d r0 E : ℕ) (L : Fin E → ℕ) :
    acquisitionCost d r0 E L-benchmarkFree=4*d*r0*E+d*∑ s,L s := by
  unfold acquisitionCost benchmarkFree
  exact Nat.sub_zero _

/-- Doubling schedule, free comparator: the closed form. -/
theorem doubling_regret_free (d r0 L0 E : ℕ) :
    acquisitionCost d r0 E (fun s => L0*2^s.val)-benchmarkFree=
      4*d*r0*E+d*L0*(2^E-1) := by
  rw [acquisition_regret_free d r0 E (fun s => L0*2^s.val),
    Fin.sum_univ_eq_sum_range (fun s => L0*2^s) E]
  exact doubling_acquisition_cost d r0 L0 E

/-- Doubling schedule, measuring comparator: linear in the epoch count, with no
dependence on `L0` at all. -/
theorem doubling_regret_measuring (d r0 L0 E : ℕ) :
    acquisitionCost d r0 E (fun s => L0*2^s.val)-
      benchmarkMeasuring d E (fun s => L0*2^s.val)=4*d*r0*E :=
  acquisition_regret_measuring d r0 E _

/-- The horizon served by a doubling schedule of `E` epochs. -/
def horizon (L0 E : ℕ) : ℕ := L0*(2^E-1)

/-- **The separation.**  One algorithm, two comparators: against the measuring
comparator the acquisition regret is `4*d*r0*E`, free of `L0` and hence of the
horizon; against the free comparator it is at least `d * horizon L0 E`.  Neither
number is more correct than the other, and a paper must say which it reports. -/
theorem benchmark_separation (d r0 L0 E : ℕ) :
    acquisitionCost d r0 E (fun s => L0*2^s.val)-
        benchmarkMeasuring d E (fun s => L0*2^s.val)=4*d*r0*E ∧
    d*horizon L0 E ≤ acquisitionCost d r0 E (fun s => L0*2^s.val)-benchmarkFree := by
  refine ⟨doubling_regret_measuring d r0 L0 E,?_⟩
  rw [doubling_regret_free d r0 L0 E]
  unfold horizon
  rw [← mul_assoc]
  exact Nat.le_add_left _ _

/-- The measuring-comparator regret does not depend on the schedule at all: any
two schedules over the same epoch count give the same acquisition regret.  This
is what makes `O(E)` a statement about discovery rather than about deployment. -/
theorem measuring_regret_schedule_free (d r0 E : ℕ) (L L' : Fin E → ℕ) :
    acquisitionCost d r0 E L-benchmarkMeasuring d E L=
      acquisitionCost d r0 E L'-benchmarkMeasuring d E L' := by
  rw [acquisition_regret_measuring,acquisition_regret_measuring]

#print axioms acquisition_regret_measuring
#print axioms acquisition_regret_free
#print axioms doubling_regret_free
#print axioms doubling_regret_measuring
#print axioms benchmark_separation
#print axioms measuring_regret_schedule_free
end
end CIGAMF.P13.D6AcquisitionBenchmark
