import Mathlib

/-!
# Two facts the experiments rely on: the six-cell rule's level, and the relay packet layout

## WHAT IS PROVED
* `intersection_union_test` — for any family of tests, each of size at most `α` on its own null set, the test that
  rejects when ALL of them reject has size at most `α` at every parameter in the UNION of the null sets, with no
  multiplicity adjustment (Berger 1982).  This is the six-cell rule of the pre-specified relay test: the claim "all six
  effects are negative" fails exactly on the union of the six one-cell nulls.
* `iut_witness` — the hypotheses hold in a two-test instance on a point mass, so the statement is not vacuous.
* `relay_layout_bits` — the relay packet (own 17-bit summary plus 21 bits for each of the other `m - 1` agents) needs
  `17 + 21 (m - 1)` bits; it fits a 25-byte (200-bit) packet iff `m ≤ 9`, and uses 185 bits at `m = 9`.

## WHAT THIS DOES NOT ESTABLISH
- That the bootstrap intervals of the paper have their nominal one-sided level (a statistical approximation).
-/

namespace CIGAMF.P13.MarlStatLayout

open MeasureTheory

/-- **Intersection–union test.** -/
theorem intersection_union_test {Ω Θ ι : Type*} [MeasurableSpace Ω] (μ : Θ → Measure Ω) (null : ι → Set Θ)
    (Rej : ι → Set Ω) (α : ENNReal) (hsize : ∀ i, ∀ θ ∈ null i, μ θ (Rej i) ≤ α) :
    ∀ θ ∈ ⋃ i, null i, μ θ (⋂ i, Rej i) ≤ α := by
  intro θ hθ
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hθ
  exact (measure_mono (Set.iInter_subset Rej i)).trans (hsize i θ hi)

/-- A two-test instance meets the hypotheses: both tests reject on `{1}`, which a point mass at `0` gives measure `0`. -/
theorem iut_witness :
    ∀ θ ∈ ⋃ _i : Fin 2, (Set.univ : Set Unit), (Measure.dirac (0 : ℝ)) (⋂ _i : Fin 2, ({1} : Set ℝ)) ≤ 0 :=
  intersection_union_test (fun _ : Unit => Measure.dirac (0 : ℝ)) (fun _ => Set.univ) (fun _ => ({1} : Set ℝ)) 0
    (fun _ _ _ => by
      rw [Measure.dirac_apply' _ (measurableSet_singleton 1)]
      simp)

/-- **The relay packet layout.** -/
theorem relay_layout_bits (m : ℕ) (hm : 1 ≤ m) : 17 + 21 * (m - 1) ≤ 200 ↔ m ≤ 9 := by
  omega

theorem relay_layout_nine : 17 + 21 * (9 - 1) = 185 := by norm_num

end CIGAMF.P13.MarlStatLayout

#print axioms CIGAMF.P13.MarlStatLayout.intersection_union_test
#print axioms CIGAMF.P13.MarlStatLayout.iut_witness
#print axioms CIGAMF.P13.MarlStatLayout.relay_layout_bits
#print axioms CIGAMF.P13.MarlStatLayout.relay_layout_nine
