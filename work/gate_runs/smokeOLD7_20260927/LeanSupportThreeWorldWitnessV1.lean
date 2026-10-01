import «LeanSupportGeometryV4»
import «LeanFunctionalRankingV6»

/-!
# Three worlds: every pair admits a common zero-regret decision, all three do not

`LeanSupportFibreSufficiencyV1` proves that pairwise separation does not suffice
for a fibre-safe decision, but it does so against `toyRegret`, an abstract
regret on `Finset (Fin 2) → Fin 3`.  Nothing there says the obstruction occurs
in the actual support-radius model.

This module realises the same obstruction inside the real geometry: the regret
of keeping relation `j` is `selectedRadius`, i.e. half the oscillation of the
sum of the omitted relations, exactly the quantity the rest of the corpus uses.

Construction (three relations, two support points per world).  Each world has
support `{anchor, tip w}` with `anchor = (0,0,0)`, and component `j` reads
coordinate `j`:

  tip 0 = ( 1,  1, -1)      radii when keeping 0,1,2 :  (0, 0, 1)
  tip 1 = (-1,  1,  1)                                  (1, 0, 0)
  tip 2 = ( 1, -1,  1)                                  (0, 1, 0)

so the zero-regret decisions are `{0,1}`, `{1,2}`, `{0,2}`.  Every pair of
worlds shares one; the three share none.

No `decide` over reals, no `native_decide`.  The two `decide` calls are on
`Finset (Fin 3)`, three elements.
-/

namespace CIGAMF.P13.SupportThreeWorldWitness

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V6.FunctionalRanking

noncomputable section

/-- The non-anchor support point of each world. -/
def tip (w j : Fin 3) : ℝ :=
  if w.val = 0 then (if j.val = 2 then -1 else 1)
  else if w.val = 1 then (if j.val = 0 then -1 else 1)
  else (if j.val = 1 then -1 else 1)

/-- World `w`: support point `0` is the anchor, point `1` is `tip w`. -/
def worldF (w : Fin 3) (j : Fin 3) (a : Fin 2) : ℝ :=
  if a = 0 then 0 else tip w j

/-- The omitted-mass at the anchor is zero, in every world. -/
theorem sumComponent_anchor (w : Fin 3) (T : Finset (Fin 3)) :
    sumComponent T (worldF w) 0 = 0 := by
  unfold sumComponent worldF
  simp

/-- The omitted-mass at the tip is the sum of the omitted coordinates. -/
theorem sumComponent_tip (w : Fin 3) (T : Finset (Fin 3)) :
    sumComponent T (worldF w) 1 = ∑ l ∈ T, tip w l := by
  unfold sumComponent worldF
  refine Finset.sum_congr rfl ?_
  intro l _
  norm_num

/-- **The regret of keeping relation `j` in world `w`**, in the actual
support-radius model: half the absolute omitted sum. -/
theorem radius_formula (w j : Fin 3) :
    selectedRadius (worldF w) {j} = |∑ l ∈ ({j}ᶜ : Finset (Fin 3)), tip w l| / 2 := by
  unfold selectedRadius supportOsc osc
  rw [maxVal_fin2, minVal_fin2, sumComponent_anchor, sumComponent_tip]
  rcases le_total (0 : ℝ) (∑ l ∈ ({j}ᶜ : Finset (Fin 3)), tip w l) with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, min_eq_right h, abs_of_nonpos h]; ring

/-- The omitted sums, one literal per (world, kept relation). -/
theorem omitted_sum (w j : Fin 3) :
    ∑ l ∈ ({j}ᶜ : Finset (Fin 3)), tip w l = (∑ l : Fin 3, tip w l) - tip w j := by
  have h : ({j}ᶜ : Finset (Fin 3)) = Finset.univ.erase j := by
    ext l; simp [Finset.mem_erase, eq_comm]
  rw [h, Finset.sum_erase_eq_sub (Finset.mem_univ j)]

/-! ## The nine radii -/

theorem radius_0_0 : selectedRadius (worldF 0) {0} = 0 := by
  rw [radius_formula, omitted_sum]
  simp only [Fin.sum_univ_three]
  change |((1 : ℝ) + (1) + (-1)) - (1)| / 2 = 0
  norm_num
theorem radius_0_1 : selectedRadius (worldF 0) {1} = 0 := by
  rw [radius_formula, omitted_sum]
  simp only [Fin.sum_univ_three]
  change |((1 : ℝ) + (1) + (-1)) - (1)| / 2 = 0
  norm_num
theorem radius_0_2 : selectedRadius (worldF 0) {2} = 1 := by
  rw [radius_formula, omitted_sum]
  simp only [Fin.sum_univ_three]
  change |((1 : ℝ) + (1) + (-1)) - (-1)| / 2 = 1
  norm_num
theorem radius_1_0 : selectedRadius (worldF 1) {0} = 1 := by
  rw [radius_formula, omitted_sum]
  simp only [Fin.sum_univ_three]
  change |((-1 : ℝ) + (1) + (1)) - (-1)| / 2 = 1
  norm_num
theorem radius_1_1 : selectedRadius (worldF 1) {1} = 0 := by
  rw [radius_formula, omitted_sum]
  simp only [Fin.sum_univ_three]
  change |((-1 : ℝ) + (1) + (1)) - (1)| / 2 = 0
  norm_num
theorem radius_1_2 : selectedRadius (worldF 1) {2} = 0 := by
  rw [radius_formula, omitted_sum]
  simp only [Fin.sum_univ_three]
  change |((-1 : ℝ) + (1) + (1)) - (1)| / 2 = 0
  norm_num
theorem radius_2_0 : selectedRadius (worldF 2) {0} = 0 := by
  rw [radius_formula, omitted_sum]
  simp only [Fin.sum_univ_three]
  change |((1 : ℝ) + (-1) + (1)) - (1)| / 2 = 0
  norm_num
theorem radius_2_1 : selectedRadius (worldF 2) {1} = 1 := by
  rw [radius_formula, omitted_sum]
  simp only [Fin.sum_univ_three]
  change |((1 : ℝ) + (-1) + (1)) - (-1)| / 2 = 1
  norm_num
theorem radius_2_2 : selectedRadius (worldF 2) {2} = 0 := by
  rw [radius_formula, omitted_sum]
  simp only [Fin.sum_univ_three]
  change |((1 : ℝ) + (-1) + (1)) - (1)| / 2 = 0
  norm_num

/-! ## Zero-regret decisions -/

/-- Decisions with zero regret in each world. -/
def zeroRegret : Fin 3 → Finset (Fin 3)
  | 0 => {0, 1}
  | 1 => {1, 2}
  | 2 => {0, 2}

/-- `zeroRegret` is exactly the zero set of the actual `selectedRadius`. -/
theorem zeroRegret_spec (w j : Fin 3) :
    j ∈ zeroRegret w ↔ selectedRadius (worldF w) {j} = 0 := by
  fin_cases w <;> fin_cases j <;>
    simp [zeroRegret, radius_0_0, radius_0_1, radius_0_2, radius_1_0, radius_1_1,
      radius_1_2, radius_2_0, radius_2_1, radius_2_2]

/-- **Every pair of worlds admits a common zero-regret decision.** -/
theorem pairwise_common_decision (w w' : Fin 3) :
    (zeroRegret w ∩ zeroRegret w').Nonempty := by
  revert w w'; decide

/-- **The three worlds together admit none.** -/
theorem no_common_decision :
    zeroRegret 0 ∩ zeroRegret 1 ∩ zeroRegret 2 = ∅ := by decide

/-- **The obstruction, stated on the actual support geometry.**  Pairwise
agreement on a zero-regret decision does not give one decision safe across the
whole fibre: no `j` has zero `selectedRadius` in all three worlds, yet any two
of the worlds share such a `j`. -/
theorem pairwise_not_sufficient_in_support_model :
    (∀ w w' : Fin 3, ∃ j, selectedRadius (worldF w) {j} = 0 ∧
        selectedRadius (worldF w') {j} = 0) ∧
      ¬ ∃ j, ∀ w : Fin 3, selectedRadius (worldF w) {j} = 0 := by
  constructor
  · intro w w'
    obtain ⟨j, hj⟩ := pairwise_common_decision w w'
    rw [Finset.mem_inter] at hj
    exact ⟨j, (zeroRegret_spec w j).mp hj.1, (zeroRegret_spec w' j).mp hj.2⟩
  · rintro ⟨j, hj⟩
    have h0 := (zeroRegret_spec 0 j).mpr (hj 0)
    have h1 := (zeroRegret_spec 1 j).mpr (hj 1)
    have h2 := (zeroRegret_spec 2 j).mpr (hj 2)
    have : j ∈ zeroRegret 0 ∩ zeroRegret 1 ∩ zeroRegret 2 := by
      simp only [Finset.mem_inter]; exact ⟨⟨h0, h1⟩, h2⟩
    rw [no_common_decision] at this
    simpa using this

#print axioms radius_formula
#print axioms zeroRegret_spec
#print axioms pairwise_common_decision
#print axioms no_common_decision
#print axioms pairwise_not_sufficient_in_support_model

end
end CIGAMF.P13.SupportThreeWorldWitness
