import «LeanPaperCEndpointV1»

/-!
# Paper C: the EVEN total-excess inequality

`odd_total_excess` (`LeanPaperCRankingV1`) gives `2 <= totalExcess` for a family summing to
`-1`.  There is no even counterpart, and that gap is exactly what makes
`EvenEndpointData.rankSum` an open field: `rankSum` asks for

    2 / denom m  <=  sum over budgets of  regret (gFamily m) sigma (denom m) k,

and `total_eq_sum_regret` already identifies the right side with
`totalExcess (rankOf (gFamily m) sigma) / denom m`.  So `rankSum` IS the statement
`2 <= totalExcess (rankOf (gFamily m) sigma)` for every relabelling, and this module proves
it.  That reduces `EvenEndpointData` from three obligations to one: the endpoint law itself.

Two things had to be generalised from the odd proof rather than reused:

* `jump_forces_excess` is stated for a `+3` step.  The family has a `-3` end too, and after a
  relabelling either heavy item can sit anywhere, so the straddling argument is redone for a
  jump of absolute size three.  The triangle inequality does not care about the sign.
* the last-budget case differs.  For an odd family the total is `-1`, so the prefix before
  the last item is `-1 - pi(m-1)`; for an even family it is `0 - pi(m-1)`, and `m-1` is ODD
  when `m` is even, so the baseline there is `1` and not `0`.  Reusing the odd computation
  would give the wrong baseline.

Every excess is a nonnegative EVEN integer -- for even `k` it is `|S_k|` with `S_k` even, for
odd `k` it is `|S_k| - 1` with `|S_k|` odd -- so "some excess is positive" already gives two.
The proof below does not need that observation, but it is why the constant is `2` and not
something smaller.
-/

namespace CIGAMF.P13.PaperCEvenTotal

open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCFamily

variable {m : ℕ}

/-- **A jump of absolute size three forces excess two across the two budgets that straddle
it.**  `jump_forces_excess` covers the `+3` step only; the `-3` end of the family needs the
same step and the triangle inequality is indifferent to the sign. -/
theorem jump_abs_forces_excess (π : Ranking m) (k : ℕ) (hk : k < m)
    (hjump : |π ⟨k, hk⟩| = 3) : 2 ≤ excess π k + excess π (k + 1) := by
  have hstep : prefixSum π (k + 1) = prefixSum π k + π ⟨k, hk⟩ := prefixSum_succ π k hk
  have h2 : |prefixSum π (k + 1) - prefixSum π k| = 3 := by
    rw [hstep]
    simpa using hjump
  have h5 : |prefixSum π (k + 1) - prefixSum π k|
      ≤ |prefixSum π (k + 1)| + |prefixSum π k| := abs_sub _ _
  rw [h2] at h5
  have hbase : ((k % 2 : ℕ) : ℝ) + (((k + 1) % 2 : ℕ) : ℝ) = 1 := by
    rcases Nat.even_or_odd k with he | ho
    · have h0 : k % 2 = 0 := Nat.even_iff.mp he
      have h1 : (k + 1) % 2 = 1 := by omega
      rw [h0, h1]; norm_num
    · have h0 : k % 2 = 1 := Nat.odd_iff.mp ho
      have h1 : (k + 1) % 2 = 0 := by omega
      rw [h0, h1]; norm_num
  unfold excess
  linarith

/-- **(L2), the EVEN total-excess inequality.**  A family whose weights sum to zero and which
carries a heavy item anywhere has total excess at least two over the budgets `1, ..., m-1`. -/
theorem even_total_excess (hm : 2 < m) (hmo : m % 2 = 0) (π : Ranking m)
    (hfam : IsEvenFamily π) (j : ℕ) (hj : j < m) (hj3 : |π ⟨j, hj⟩| = 3) :
    2 ≤ totalExcess π := by
  have hw := hfam.weight
  have hB1 : ({1} : Finset ℕ) ⊆ Finset.Ico 1 m := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico]
    omega
  have hBlast : ({m - 1} : Finset ℕ) ⊆ Finset.Ico 1 m := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico]
    omega
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  -- the heavy item is FIRST: budget one already carries excess two
  · refine totalExcess_ge_of_subset π hw {1} hB1 _ ?_
    rw [Finset.sum_singleton]
    have hex1 : excess π 1 = |π ⟨0, by omega⟩| - 1 := by
      unfold excess
      rw [prefixSum_one (by omega) π]
      norm_num
    have hid : (⟨0, by omega⟩ : Fin m) = ⟨j, hj⟩ := by
      apply Fin.ext
      show (0 : ℕ) = j
      omega
    rw [hex1, hid, hj3]
    norm_num
  · rcases Nat.lt_or_ge (j + 1) m with hjlt | hjge
    -- INTERIOR: the straddling pair lies inside the budget range
    · have hBp : ({j, j + 1} : Finset ℕ) ⊆ Finset.Ico 1 m := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_Ico]
        omega
      refine totalExcess_ge_of_subset π hw {j, j + 1} hBp _ ?_
      rw [Finset.sum_insert (by simp), Finset.sum_singleton]
      exact jump_abs_forces_excess π j hj hj3
    -- LAST: the total is ZERO, so the prefix before the last item is minus that item, and
    -- `m-1` is ODD because `m` is even, so the baseline there is one
    · refine totalExcess_ge_of_subset π hw {m - 1} hBlast _ ?_
      rw [Finset.sum_singleton]
      have hpre : prefixSum π (m - 1) = -π ⟨m - 1, by omega⟩ := by
        rw [prefixSum_pred (by omega) π, hfam.total]
        ring
      have hpar : (m - 1) % 2 = 1 := by omega
      have hid : (⟨m - 1, by omega⟩ : Fin m) = ⟨j, hj⟩ := by
        apply Fin.ext
        show m - 1 = j
        omega
      unfold excess
      rw [hpre, abs_neg, hid, hj3, hpar]
      norm_num

/-! ## The heavy witness the family always supplies -/

/-- `gFamily`'s last item is the `+3`. -/
theorem gFamily_last_three (m : ℕ) (hm : 3 ≤ m) :
    gFamily m ⟨m - 1, by omega⟩ = 3 := by
  simp [gFamily, gN, show m - 1 ≠ 0 from by omega]

/-- **Every relabelling keeps a heavy item**, so `even_total_excess` applies to
`rankOf (gFamily m) σ` for every `σ` -- which is what `rankSum` quantifies over. -/
theorem rankOf_has_heavy (m : ℕ) (hm : 3 ≤ m) (σ : Equiv.Perm (Fin m)) :
    ∃ j : ℕ, ∃ hj : j < m, |rankOf (gFamily m) σ ⟨j, hj⟩| = 3 := by
  refine ⟨(σ.symm ⟨m - 1, by omega⟩ : Fin m), (σ.symm ⟨m - 1, by omega⟩ : Fin m).isLt, ?_⟩
  have hfin : (⟨(σ.symm ⟨m - 1, by omega⟩ : Fin m),
      (σ.symm ⟨m - 1, by omega⟩ : Fin m).isLt⟩ : Fin m)
      = σ.symm ⟨m - 1, by omega⟩ := Fin.ext rfl
  rw [hfin]
  show |gFamily m (σ (σ.symm ⟨m - 1, by omega⟩))| = 3
  rw [Equiv.apply_symm_apply, gFamily_last_three m hm]
  norm_num

/-! ## Audit -/

#print axioms jump_abs_forces_excess
#print axioms even_total_excess
#print axioms gFamily_last_three
#print axioms rankOf_has_heavy

end CIGAMF.P13.PaperCEvenTotal
