import «LeanPaperACentredModelV1»

/-!
# Paper A: the alternative set is exactly a finite union of polyhedra

The oracle solves the inner problem region by region.  For that to be an oracle for the
COMPRESSION problem, the decomposition has to be an **equality** with the set of worlds at
which the retained answer is actually wrong — both inclusions, and derived from the loss
rather than posited.  `LeanPaperACentredModelV1` supplies the missing half: retaining `A` is
`eps`-unsafe exactly when `range(lam_B) > range(lam_A) + 2 eps`.  From there the
decomposition is two short steps.

* **The range condition is an existential over pairs of arm-`B` cells.**  Forward: take the
  cells realising arm `B`'s maximum and minimum.  Backward: any pair's gap is below the
  range, so a pair that already exceeds forces the range to exceed.
* **Each pair's condition is a polyhedron cut out by two LINEAR inequalities**, because
  `|x| < y` is `x < y` together with `-x < y`.  The absolute value is where an earlier
  numerical cover of this set went wrong: treating the two inequalities as alternatives
  rather than as simultaneous constraints admits the true world itself.

Together: `Unsafe(eps) = union over (p,q) of a polyhedron`, an equality, from the loss.
-/

namespace CIGAMF.P13.PaperARegion

open Finset
open CIGAMF.P13.PaperARPair
open CIGAMF.P13.PaperACentred
open CIGAMF.P13.PaperACentredModel

variable {r : ℕ}

/-- **The range condition is an existential over pairs of arm-`B` cells.** -/
theorem range_gap_iff_exists_pair (lam : Cell r → ℝ) (c : ℝ) :
    c < rangeB lam ↔ ∃ p ∈ BCells r, ∃ q ∈ BCells r, c < lam p - lam q := by
  classical
  constructor
  · intro h
    obtain ⟨p, hp, hpv⟩ := Finset.exists_mem_eq_sup' (BCells_nonempty r) lam
    obtain ⟨q, hq, hqv⟩ := Finset.exists_mem_eq_inf' (BCells_nonempty r) lam
    refine ⟨p, hp, q, hq, ?_⟩
    have : rangeB lam = lam p - lam q := by unfold rangeB; rw [hpv, hqv]
    linarith [h, this.le, this.ge]
  · rintro ⟨p, hp, q, hq, h⟩
    have hle : lam p - lam q ≤ rangeB lam := by
      unfold rangeB
      have h1 : lam p ≤ (BCells r).sup' (BCells_nonempty r) lam := Finset.le_sup' lam hp
      have h2 : (BCells r).inf' (BCells_nonempty r) lam ≤ lam q := Finset.inf'_le lam hq
      linarith
    linarith

/-- **Each pair's condition is a polyhedron**: two linear inequalities, simultaneously.
The absolute value in `rangeA` is exactly what makes them simultaneous rather than
alternative. -/
theorem pair_region_linear (lam : Cell r → ℝ) (p q : Cell r) (ε : ℝ) :
    rangeA lam + 2 * ε < lam p - lam q ↔
      (lam (Sum.inl 1) - lam (Sum.inl 0) + 2 * ε < lam p - lam q
        ∧ lam (Sum.inl 0) - lam (Sum.inl 1) + 2 * ε < lam p - lam q) := by
  unfold rangeA
  constructor
  · intro h
    have habs : |lam (Sum.inl 1) - lam (Sum.inl 0)| < lam p - lam q - 2 * ε := by linarith
    rw [abs_lt] at habs
    exact ⟨by linarith [habs.2], by linarith [habs.1]⟩
  · rintro ⟨h1, h2⟩
    have habs : |lam (Sum.inl 1) - lam (Sum.inl 0)| < lam p - lam q - 2 * ε := by
      rw [abs_lt]
      exact ⟨by linarith, by linarith⟩
    linarith [habs]

/-- **The decomposition, as an equality with the unsafe set.**  Not a cover found by search:
both inclusions, and the left-hand side is the compression loss condition. -/
theorem unsafe_iff_union_of_polyhedra (ε : ℝ) (lam : Cell r → ℝ) (hc : lam ∈ Centred r) :
    UnsafeA ε lam ↔
      ∃ p ∈ BCells r, ∃ q ∈ BCells r,
        (lam (Sum.inl 1) - lam (Sum.inl 0) + 2 * ε < lam p - lam q
          ∧ lam (Sum.inl 0) - lam (Sum.inl 1) + 2 * ε < lam p - lam q) := by
  rw [unsafeA_iff_range_gap ε lam hc]
  constructor
  · intro h
    obtain ⟨p, hp, q, hq, hpq⟩ :=
      (range_gap_iff_exists_pair lam (rangeA lam + 2 * ε)).mp (by linarith)
    exact ⟨p, hp, q, hq, (pair_region_linear lam p q ε).mp hpq⟩
  · rintro ⟨p, hp, q, hq, hlin⟩
    have hpq := (pair_region_linear lam p q ε).mpr hlin
    have := (range_gap_iff_exists_pair lam (rangeA lam + 2 * ε)).mpr ⟨p, hp, q, hq, hpq⟩
    linarith

/-- **The decomposition is non-vacuous**: at zero tolerance a pair shift by `d > 1/2` lands
in the polyhedron for its own pair, so no region is being carried empty. -/
theorem polyhedron_nonvacuous (r : ℕ) (hr : 0 < r) (j : Fin r) (δ : ℝ) (hδ : 0 < δ) :
    (pairShift (thetaC r) j (1 / 2 + δ) (Sum.inl 1)
        - pairShift (thetaC r) j (1 / 2 + δ) (Sum.inl 0) + 2 * 0
      < pairShift (thetaC r) j (1 / 2 + δ) (Sum.inr (j, true))
        - pairShift (thetaC r) j (1 / 2 + δ) (Sum.inr (j, false)))
    ∧ (pairShift (thetaC r) j (1 / 2 + δ) (Sum.inl 0)
        - pairShift (thetaC r) j (1 / 2 + δ) (Sum.inl 1) + 2 * 0
      < pairShift (thetaC r) j (1 / 2 + δ) (Sum.inr (j, true))
        - pairShift (thetaC r) j (1 / 2 + δ) (Sum.inr (j, false))) := by
  have ht : pairShift (thetaC r) j (1 / 2 + δ) (Sum.inr (j, true)) = 1 / 2 + δ :=
    pairShiftC_value_true j (1 / 2 + δ)
  have hf : pairShift (thetaC r) j (1 / 2 + δ) (Sum.inr (j, false)) = -(1 / 2 + δ) :=
    pairShiftC_value_false j (1 / 2 + δ)
  have h0 : pairShift (thetaC r) j (1 / 2 + δ) (Sum.inl 0) = thetaC r (Sum.inl 0) :=
    pairShiftC_anchor j (1 / 2 + δ) 0
  have h1 : pairShift (thetaC r) j (1 / 2 + δ) (Sum.inl 1) = thetaC r (Sum.inl 1) :=
    pairShiftC_anchor j (1 / 2 + δ) 1
  rw [ht, hf, h0, h1, thetaC_0, thetaC_1]
  constructor <;> linarith

/-! ## Audit -/

#print axioms range_gap_iff_exists_pair
#print axioms pair_region_linear
#print axioms unsafe_iff_union_of_polyhedra
#print axioms polyhedron_nonvacuous

end CIGAMF.P13.PaperARegion
