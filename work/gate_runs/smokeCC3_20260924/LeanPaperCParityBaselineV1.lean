import «LeanPaperCStabilityEndgameV1»

/-!
# Paper C: the parity half of `FamilyBaselineIdentification`

`LeanPaperCStabilityEndgameV1` states `FamilyBaselineIdentification` as an OPEN join and
`family_regret_identification` consumes it: until something instantiates it, the statement
"the algebraic family regret IS the physical regret" is a conditional.

The obligation is an EQUALITY, `trueBaseline (gFamily m) k = k mod 2`, so it has two halves
and they are not of the same difficulty:

* the LOWER half -- no cardinality-`k` subset does better than `k mod 2` -- is proved here,
  unconditionally, for every `m` and every `k`.  It rests on one fact and nothing else:
  every weight of `g_m` is an ODD integer, so a sum of `k` of them is an integer congruent to
  `k` mod 2, and an odd integer cannot be zero.  The `-3` and `+3` heavy ends are odd too,
  which is why no case split on them is needed;
* the UPPER half -- ATTAINMENT, a cardinality-`k` subset whose absolute sum IS `k mod 2` --
  is a construction over four regimes (`m` even/odd against `k` even/odd) plus the separate
  budget `k = m-1`, and it is NOT proved here and NOT assumed here.  It is constructed in
  `LeanPaperCBaselineAttainV1` for every `m >= 3`.

`familyBaselineIdentification_of_attainment` records exactly what is left.  It is a
REDUCTION, not an instance: it consumes attainment, which is strictly weaker than the
identification it produces, and it is not cited by anything as though the obligation were
discharged.  The remaining construction is the one the endgame file describes: for odd `m`
the budget `k = m-1` is even and must omit a `-1` item, because the zero-total argument that
serves the even case is unavailable there.
-/

namespace CIGAMF.P13.PaperCParityBaseline

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCFrontier CIGAMF.P13.PaperCStabilityEndgame

/-! ## 1. The family is integral, and odd -/

/-- The family's weights as INTEGERS.  The real `gN` is exactly this cast -- the shape of the
definition is copied, not re-chosen, so `gN_eq_gZ` is a case split and not a claim. -/
def gZ (m j : ℕ) : ℤ :=
  if j = 0 then -3 else if j = m - 1 then 3 else if j ≤ (m - 1) / 2 then -1 else 1

theorem gN_eq_gZ (m j : ℕ) : gN m j = ((gZ m j : ℤ) : ℝ) := by
  unfold gN gZ
  split_ifs <;> norm_num

theorem gFamily_eq_gZ (m : ℕ) (i : Fin m) : gFamily m i = ((gZ m (i : ℕ) : ℤ) : ℝ) :=
  gN_eq_gZ m (i : ℕ)

/-- **Every weight is odd.**  This is the entire content of the parity baseline.  All four
values `-3, -1, 1, 3` are odd, so the heavy ends need no separate treatment. -/
theorem gZ_odd (m j : ℕ) : gZ m j % 2 = 1 := by
  unfold gZ
  split_ifs <;> first | norm_num | decide | rfl

/-- **A sum of `k` odd integers is congruent to `k`.** -/
theorem sum_gZ_parity (m : ℕ) (S : Finset (Fin m)) :
    (∑ i ∈ S, gZ m (i : ℕ)) % 2 = (S.card : ℤ) % 2 := by
  classical
  refine Finset.induction_on S (by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
  have hodd := gZ_odd m (a : ℕ)
  push_cast
  omega

/-! ## 2. The lower half, at every subset -/

/-- **An odd-sized subset cannot sum to zero**, so its absolute sum is at least one; an
even-sized one gets the trivial bound.  Together: `|sum| >= |S| mod 2`. -/
theorem parity_le_abs_sum (m : ℕ) (S : Finset (Fin m)) :
    ((S.card % 2 : ℕ) : ℝ) ≤ |∑ i ∈ S, gFamily m i| := by
  classical
  have hcast : ∑ i ∈ S, gFamily m i = ((∑ i ∈ S, gZ m (i : ℕ) : ℤ) : ℝ) := by
    push_cast
    exact Finset.sum_congr rfl fun i _ => gFamily_eq_gZ m i
  rcases Nat.even_or_odd S.card with he | ho
  · have hz : S.card % 2 = 0 := Nat.even_iff.mp he
    rw [hz]
    simpa using abs_nonneg (∑ i ∈ S, gFamily m i)
  · have hpar : S.card % 2 = 1 := Nat.odd_iff.mp ho
    have hne : (∑ i ∈ S, gZ m (i : ℕ)) ≠ 0 := by
      intro hc
      have hpz := sum_gZ_parity m S
      rw [hc] at hpz
      omega
    have hone : (1 : ℤ) ≤ |∑ i ∈ S, gZ m (i : ℕ)| := Int.one_le_abs hne
    rw [hpar, hcast, ← Int.cast_abs]
    exact_mod_cast hone

/-- **The lower half at the baseline itself.**  Unconditional, every `m`, every `k`. -/
theorem parity_le_trueBaseline (m : ℕ) (k : Fin (m + 1)) :
    ((k.val % 2 : ℕ) : ℝ) ≤ trueBaseline (gFamily m) k := by
  classical
  unfold trueBaseline baseline
  refine le_inf' _ _ (fun S hS => ?_)
  have hcard : S.card = k.val := by
    simpa using (Finset.mem_filter.mp hS).2
  rw [← hcard]
  exact parity_le_abs_sum m S

/-! ## 3. What is left

The statement below is a REDUCTION and NOT an instance of `FamilyBaselineIdentification`.
Nothing in the corpus cites it as though the obligation were discharged; its hypothesis
`hatt` is the explicit remaining construction. -/

/-- **The obligation reduces to ATTAINMENT alone.**  Given, for each interior budget, one
cardinality-`k` subset whose absolute sum IS the parity, the identification follows -- the
other inequality is `parity_le_trueBaseline` and needs nothing. -/
theorem familyBaselineIdentification_of_attainment (m : ℕ)
    (hatt : ∀ k : Fin (m + 1), 1 ≤ k.val → k.val < m →
      ∃ S : Finset (Fin m), S.card = k.val ∧
        |∑ i ∈ S, gFamily m i| = ((k.val % 2 : ℕ) : ℝ)) :
    FamilyBaselineIdentification m := by
  classical
  intro k hk hkm
  refine le_antisymm ?_ (parity_le_trueBaseline m k)
  obtain ⟨S, hcard, hval⟩ := hatt k hk hkm
  unfold trueBaseline baseline
  rw [← hval]
  exact inf'_le _ (by simp [hcard])

/-! ## Audit -/

#print axioms gN_eq_gZ
#print axioms gZ_odd
#print axioms sum_gZ_parity
#print axioms parity_le_abs_sum
#print axioms parity_le_trueBaseline
#print axioms familyBaselineIdentification_of_attainment

end CIGAMF.P13.PaperCParityBaseline
