import «LeanPaperCEndgameV1»

/-!
# Paper C: choosing the budget AFTER the draw -- the ex-post value, and the factor `m - 1`

The objective of Paper C fixes the budget before the ranking is drawn: `max_k E_P[r_k]`
(`objective`, `LeanPaperCEndgameV1`).  If the budget is chosen after the draw, the regret is
`E_P[max_k r_k]` (`pathObjective`).  On the family `g_m`, at every size `m >= 3`:

* `exists_defect` -- **every ordering has an interior budget with excess at least `2`**.  The
  family holds a `+3` and a `-3`; one of them is not in the last position, and the step it
  makes cannot fit between two budgets of excess `0`, whose prefix sums have absolute value at
  most `1`.  The excess is even (`prefixSum_parity`), so it is `>= 2`.
* `worstBudget_even`, `worstBudget_odd` -- one ordering attains `2` exactly: the flat even
  ranking (`flatToFamily`, excess `2` at every budget) and the odd base ranking
  (`oddToFamily`, prefix sums in `{0, 3, -1}`).
* `pathValue_eq` -- **the ex-post value is `2/(m+4)`**, the infimum over all ranking laws.
* `path_over_free` -- **`pathValue / freeValue = m - 1`**.
* `objective_le_pathObjective` -- for every law, the ex-ante objective is at most the ex-post
  one, so choosing the budget after the draw can only cost more.

No band is imposed here: this is the free case.  The banded ex-post problem is not treated, and
the two linear factors of Paper C (band and timing) are NOT multiplied: the combined problem is
not solved.
-/

namespace CIGAMF.P13.PaperCExPost

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCEven
open CIGAMF.P13.PaperCOdd
open CIGAMF.P13.PaperCEvenWitnessJoin (flatToFamily flatToFamily_apply)
open CIGAMF.P13.PaperCOddWitnessJoin (oddToFamily oddToFamily_apply)

/-! ## 1. The objects -/

/-- The worst budget of one ordering: what an adversary choosing the budget after the draw
charges. -/
noncomputable def worstBudget (m : ℕ) (hm : 2 ≤ m) (σ : Perm m) : ℝ :=
  (budgets m).sup' (budgets_nonempty m hm) (fun k => regret (gFamily m) σ (denom m) k)

/-- The ex-post objective: the expected worst budget. -/
noncomputable def pathObjective (m : ℕ) (hm : 2 ≤ m) (P : Perm m → ℝ) : ℝ :=
  ∑ σ, P σ * worstBudget m hm σ

/-- A ranking law on all permutations. -/
def IsLaw {m : ℕ} (P : Perm m → ℝ) : Prop := (∀ σ, 0 ≤ P σ) ∧ ∑ σ, P σ = 1

/-- The ex-post value: the infimum over all ranking laws. -/
noncomputable def pathValue (m : ℕ) (hm : 2 ≤ m) : ℝ :=
  sInf ((fun P => pathObjective m hm P) '' {P | IsLaw P})

theorem mem_budgets (m k : ℕ) : k ∈ budgets m ↔ 1 ≤ k ∧ k ≤ m - 1 := by
  simp [budgets]

theorem denom_pos (m : ℕ) : 0 < denom m := by unfold denom; positivity

/-! ## 2. Every ordering pays at least `2` at some interior budget -/

/-- **A budget of excess below `2` has a prefix sum of absolute value at most `1`.** -/
theorem abs_le_one_of_excess_lt {m : ℕ} (π : Ranking m)
    (hw : ∀ i, π i = -3 ∨ π i = -1 ∨ π i = 1 ∨ π i = 3)
    (k : ℕ) (hk : k ≤ m) (h : excess π k < 2) : |prefixSum π k| ≤ 1 := by
  obtain ⟨j, hj⟩ := prefixSum_parity π hw k hk
  unfold excess at h
  set b : ℕ := k % 2 with hbdef
  have hb1 : b ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt k two_pos)
  set z : ℤ := 2 * j + b with hz
  have hzR : prefixSum π k = (z : ℝ) := by rw [hj, hz]; push_cast; ring
  rw [hzR] at h ⊢
  have h' : |(z : ℝ)| < 2 + (b : ℝ) := by linarith
  have hzi : |z| < 2 + (b : ℤ) := by
    have : ((|z| : ℤ) : ℝ) < ((2 + (b : ℤ) : ℤ) : ℝ) := by push_cast; exact h'
    exact_mod_cast this
  have hzb := abs_lt.mp hzi
  have hz1 : -1 ≤ z ∧ z ≤ 1 := by omega
  have : |z| ≤ 1 := abs_le.mpr hz1
  have : ((|z| : ℤ) : ℝ) ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast this
  push_cast at this
  exact this

/-- **Every ordering of `g_m` has an interior budget with excess at least `2`.** -/
theorem exists_defect {m : ℕ} (hm : 3 ≤ m) (σ : Perm m) :
    ∃ k ∈ budgets m, 2 ≤ excess (rankOf (gFamily m) σ) k := by
  set π := rankOf (gFamily m) σ with hπ
  have hw : ∀ i, π i = -3 ∨ π i = -1 ∨ π i = 1 ∨ π i = 3 := fun i => gFamily_weights m (σ i)
  by_contra hno
  push_neg at hno
  have hsmall : ∀ k, k ≤ m - 1 → |prefixSum π k| ≤ 1 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [prefixSum_zero]; simp
    · exact abs_le_one_of_excess_lt π hw k (by omega)
        (hno k ((mem_budgets m k).mpr ⟨hk0, hk⟩))
  -- the two heavy items sit at different positions, so one of them is not last
  set p0 := σ.symm ⟨0, by omega⟩ with hp0
  set p1 := σ.symm ⟨m - 1, by omega⟩ with hp1
  have hg0 : gFamily m ⟨0, by omega⟩ = -3 := by rw [gFamily_apply]; simp [gN]
  have hg1 : gFamily m ⟨m - 1, by omega⟩ = 3 := by
    rw [gFamily_apply]; simp [gN, show m - 1 ≠ 0 by omega]
  have hne : (p0 : ℕ) ≠ (p1 : ℕ) := by
    intro h
    have h' : p0 = p1 := Fin.ext h
    have := σ.symm.injective h'
    have := congrArg Fin.val this
    simp at this
    omega
  have hbig : ∃ p : ℕ, ∃ hp : p < m - 1, |π ⟨p, by omega⟩| = 3 := by
    by_cases hlast : (p0 : ℕ) = m - 1
    · have hp1lt : (p1 : ℕ) < m - 1 := by have := p1.isLt; omega
      refine ⟨p1, hp1lt, ?_⟩
      have heq : (⟨(p1 : ℕ), by omega⟩ : Fin m) = p1 := Fin.ext rfl
      show |gFamily m (σ ⟨(p1 : ℕ), by omega⟩)| = 3
      rw [heq, hp1, Equiv.apply_symm_apply, hg1]
      norm_num
    · have hp0lt : (p0 : ℕ) < m - 1 := by have := p0.isLt; omega
      refine ⟨p0, hp0lt, ?_⟩
      have heq : (⟨(p0 : ℕ), by omega⟩ : Fin m) = p0 := Fin.ext rfl
      show |gFamily m (σ ⟨(p0 : ℕ), by omega⟩)| = 3
      rw [heq, hp0, Equiv.apply_symm_apply, hg0]
      norm_num
  obtain ⟨p, hp, h3⟩ := hbig
  have hstep := prefixSum_succ π p (by omega)
  have ha := abs_le.mp (hsmall p (by omega))
  have hb := abs_le.mp (hsmall (p + 1) (by omega))
  have hd : |prefixSum π (p + 1) - prefixSum π p| ≤ 2 :=
    abs_le.mpr ⟨by linarith [ha.1, ha.2, hb.1, hb.2], by linarith [ha.1, ha.2, hb.1, hb.2]⟩
  rw [hstep, add_sub_cancel_left, h3] at hd
  norm_num at hd

/-- **Every ordering's worst budget costs at least `2/(m+4)`.** -/
theorem worstBudget_ge {m : ℕ} (hm : 3 ≤ m) (σ : Perm m) :
    2 / denom m ≤ worstBudget m (by omega) σ := by
  obtain ⟨k, hk, h2⟩ := exists_defect hm σ
  refine le_trans ?_ (Finset.le_sup' (fun k => regret (gFamily m) σ (denom m) k) hk)
  show 2 / denom m ≤ excess (rankOf (gFamily m) σ) k / denom m
  exact div_le_div_of_nonneg_right h2 (denom_pos m).le

/-! ## 3. One ordering attains it -/

theorem worstBudget_le_of {m : ℕ} (hm : 2 ≤ m) (σ : Perm m)
    (h : ∀ k ∈ budgets m, excess (rankOf (gFamily m) σ) k ≤ 2) :
    worstBudget m hm σ ≤ 2 / denom m :=
  Finset.sup'_le _ _ fun k hk =>
    div_le_div_of_nonneg_right (h k hk) (denom_pos m).le

/-- **Even sizes: the flat ranking pays exactly `2` at every budget.** -/
theorem worstBudget_even {m : ℕ} (hm : Even m) (hm4 : 4 ≤ m) :
    worstBudget m (by omega) (flatToFamily m hm hm4) = 2 / denom m := by
  have hrank : rankOf (gFamily m) (flatToFamily m hm hm4) = flatEven m := by
    funext i
    exact flatToFamily_apply m hm hm4 i
  refine le_antisymm (worstBudget_le_of _ _ fun k hk => ?_) (worstBudget_ge (by omega) _)
  rw [hrank]
  obtain ⟨h1, h2⟩ := (mem_budgets m k).mp hk
  rw [flatEven_excess (by omega) k h1 h2]

/-- **Odd sizes: the base ranking's prefix sums take only the values `0, 3, -1`.** -/
theorem worstBudget_odd (s : ℕ) :
    worstBudget (2 * s + 3) (by omega) (oddToFamily s) = 2 / denom (2 * s + 3) := by
  set m := 2 * s + 3 with hmdef
  set π := rankOf (gFamily m) (oddToFamily s) with hπ
  have hrank : π = oddBase m := by
    funext i
    exact oddToFamily_apply s i
  have hw : ∀ i, π i = -3 ∨ π i = -1 ∨ π i = 1 ∨ π i = 3 :=
    fun i => gFamily_weights m (oddToFamily s i)
  refine le_antisymm (worstBudget_le_of _ _ fun k hk => ?_) (worstBudget_ge (by omega) _)
  obtain ⟨h1, h2⟩ := (mem_budgets m k).mp hk
  have hk : k ≤ m := by omega
  have h3 := oddPrefix_three_values m (by omega) k hk
  rw [← hrank] at h3
  obtain ⟨j, hj⟩ := prefixSum_parity π hw k hk
  unfold excess
  have hb1 : k % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt k two_pos)
  have hc0 : (0 : ℝ) ≤ ((k % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases h3 with h0 | h3 | hm1
  · rw [h0, abs_zero]; linarith
  · rw [h3]
    have hodd : k % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · exfalso
        rw [h3, h] at hj
        push_cast at hj
        have h2j : (2 * j : ℤ) = 3 := by
          have : ((2 * j : ℤ) : ℝ) = ((3 : ℤ) : ℝ) := by push_cast; linarith
          exact_mod_cast this
        omega
      · exact h
    rw [hodd]; norm_num
  · rw [hm1]; norm_num; linarith

/-! ## 4. The ex-post value, and the factor `m - 1` -/

theorem pathObjective_ge {m : ℕ} (hm : 3 ≤ m) (P : Perm m → ℝ) (hP : IsLaw P) :
    2 / denom m ≤ pathObjective m (by omega) P := by
  unfold pathObjective
  calc 2 / denom m = ∑ σ, P σ * (2 / denom m) := by rw [← Finset.sum_mul, hP.2, one_mul]
    _ ≤ ∑ σ, P σ * worstBudget m (by omega) σ :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (worstBudget_ge hm σ) (hP.1 σ)

/-- The law that draws one fixed ordering. -/
noncomputable def pointLaw {m : ℕ} (σ₀ : Perm m) : Perm m → ℝ :=
  fun σ => if σ = σ₀ then 1 else 0

theorem pointLaw_isLaw {m : ℕ} (σ₀ : Perm m) : IsLaw (pointLaw σ₀) := by
  refine ⟨fun σ => by unfold pointLaw; split_ifs <;> norm_num, ?_⟩
  unfold pointLaw
  rw [Finset.sum_ite_eq' Finset.univ σ₀ (fun _ => (1 : ℝ))]
  simp

theorem pathObjective_pointLaw {m : ℕ} (hm : 2 ≤ m) (σ₀ : Perm m) :
    pathObjective m hm (pointLaw σ₀) = worstBudget m hm σ₀ := by
  unfold pathObjective pointLaw
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ σ₀]
  simp

/-- **The ex-post value is `2/(m+4)`, at every size `m >= 3`.** -/
theorem pathValue_eq {m : ℕ} (hm : 3 ≤ m) : pathValue m (by omega) = 2 / denom m := by
  have hne : ((fun P => pathObjective m (by omega) P) '' {P | IsLaw P}).Nonempty :=
    ⟨_, ⟨pointLaw 1, pointLaw_isLaw 1, rfl⟩⟩
  have hlow : ∀ x ∈ ((fun P => pathObjective m (by omega) P) '' {P | IsLaw P}),
      2 / denom m ≤ x := by
    rintro x ⟨P, hP, rfl⟩
    exact pathObjective_ge hm P hP
  refine le_antisymm ?_ (le_csInf hne hlow)
  -- an ordering attaining `2/(m+4)`
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : Perm m, worstBudget m (by omega) σ₀ = 2 / denom m := by
    rcases Nat.even_or_odd m with he | ho
    · exact ⟨flatToFamily m he (by obtain ⟨t, ht⟩ := he; omega), worstBudget_even he _⟩
    · obtain ⟨t, ht⟩ := ho
      obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 3 := ⟨t - 1, by omega⟩
      exact ⟨oddToFamily s, worstBudget_odd s⟩
  refine le_trans (csInf_le ⟨2 / denom m, hlow⟩ ⟨pointLaw σ₀, pointLaw_isLaw σ₀, rfl⟩) ?_
  show pathObjective m (by omega) (pointLaw σ₀) ≤ 2 / denom m
  rw [pathObjective_pointLaw, hσ₀]

/-- **Choosing the budget after the draw costs a factor `m - 1` over the free ex-ante value.** -/
theorem path_over_free {m : ℕ} (hm : 3 ≤ m) :
    pathValue m (by omega) / freeValue m = (m : ℝ) - 1 := by
  rw [pathValue_eq hm]
  unfold freeValue
  have hD := (denom_pos m).ne'
  have hm1 : (m : ℝ) - 1 ≠ 0 := by
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  field_simp

/-- **Ex-ante never exceeds ex-post**, for every law. -/
theorem objective_le_pathObjective {m : ℕ} (hm : 2 ≤ m) (P : Perm m → ℝ) (hP : IsLaw P) :
    objective m hm P ≤ pathObjective m hm P := by
  unfold objective maxRegret pathObjective
  refine Finset.sup'_le _ _ fun k hk => ?_
  refine Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left ?_ (hP.1 σ)
  exact Finset.le_sup' (fun k => regret (gFamily m) σ (denom m) k) hk

#print axioms exists_defect
#print axioms worstBudget_even
#print axioms worstBudget_odd
#print axioms pathValue_eq
#print axioms path_over_free
#print axioms objective_le_pathObjective

end CIGAMF.P13.PaperCExPost
