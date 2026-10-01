import «LeanPaperCEndgameV1»

/-!
# Paper C: the relaxed-band lower bound, at the value

Paper C states, for odd `m`, `V_m(η) ≥ (m+3-(m+1)η)/(m(m+4))`.  Until this module the Lean
side of that statement was `relaxed_value_lower_bound` (`LeanUnifiedStructuralRelaxedV1`), an
inequality about a last-position probability vector on a separate item type with a POSITION
band.  Nothing joined it to `value`, whose band is the per-item RETAINED-PREFIX band at every
budget.  This module is the join, at the paper's own objects: `gFamily`, `regret`,
`FeasibleAt id`, `value`.

The argument uses the single budget `k = m-1`.

1. For an odd family the prefix of length `m-1` is `-1` minus the last item, and `m-1` is
   even, so the excess there is `|1 + w|` where `w` is the last weight (`excess_last`).
2. So `E r_{m-1} = (1/D) Σ_i π_i |1 + g_i|` with `π_i = Pr(σ(m-1) = i)`.
3. `π_i = 1 - Pr(i ∈ prefix_{m-1})`, so the band at `k = m-1` gives `|π_i - 1/m| ≤ η/m` on
   both sides.
4. For any centre `a`, `Σ π_i c_i ≥ (Σ c_i)/m - (η/m) Σ |c_i - a|`.  At `a = 2` the family
   gives `Σ c_i = m+3` and `Σ |c_i - 2| = m+1`.

No hypothesis about the game remains: the family, its weight counts, the feasible set and the
value are the paper's definitions.
-/

namespace CIGAMF.P13.PaperCRelaxedJoin

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCEndgame

/-! ## Sums over the family -/

/-- A range split at the sign change, for any pair of values. -/
theorem split_sum_fn (a b : ℕ) (u v : ℝ) :
    ∑ j ∈ Finset.range (a + b), (if j + 1 ≤ a then u else v) = (a : ℝ) * u + (b : ℝ) * v := by
  rw [Finset.sum_range_add]
  have hlow : ∀ j ∈ Finset.range a, (if j + 1 ≤ a then u else v) = u := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [if_pos (by omega)]
  have hhigh : ∀ j ∈ Finset.range b, (if a + j + 1 ≤ a then u else v) = v := by
    intro j _
    rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl hlow, Finset.sum_congr rfl hhigh,
    Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_range,
    nsmul_eq_mul, nsmul_eq_mul]

/-- **Any function of the weights, summed over `g_m`**: two heavy items, `p` light negatives,
`q` light positives. -/
theorem sum_fn_gFamily (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ) :
    ∑ i, f (gFamily (n + 2) i)
      = f (-3) + f 3 + (((n + 1) / 2 : ℕ) : ℝ) * f (-1)
        + ((n - (n + 1) / 2 : ℕ) : ℝ) * f 1 := by
  classical
  have hsum : ∑ i : Fin (n + 2), f (gFamily (n + 2) i)
      = ∑ j ∈ Finset.range (n + 2), f (gN (n + 2) j) := by
    simpa [gFamily_apply] using
      (Fin.sum_univ_eq_sum_range (fun j => f (gN (n + 2) j)) (n + 2))
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ']
  have hlast : gN (n + 2) (n + 1) = 3 := by
    unfold gN; rw [if_neg (by omega), if_pos (by omega)]
  have hfirst : gN (n + 2) 0 = -3 := by unfold gN; rw [if_pos rfl]
  have hmid : ∀ j ∈ Finset.range n,
      f (gN (n + 2) (j + 1)) = if j + 1 ≤ (n + 1) / 2 then f (-1) else f 1 := by
    intro j hj
    rw [Finset.mem_range] at hj
    unfold gN
    rw [if_neg (by omega), if_neg (by omega), show n + 2 - 1 = n + 1 from by omega]
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl hmid, hfirst, hlast]
  have hsplit := split_sum_fn ((n + 1) / 2) (n - (n + 1) / 2) (f (-1)) (f 1)
  rw [show (n + 1) / 2 + (n - (n + 1) / 2) = n from by omega] at hsplit
  rw [hsplit]
  ring

/-- The last-position loss coefficients at odd `m = 2s+3` add up to `m+3`. -/
theorem sum_coef (s : ℕ) :
    ∑ i, |1 + gFamily (2 * s + 3) i| = ((2 * s + 3 : ℕ) : ℝ) + 3 := by
  have h := sum_fn_gFamily (2 * s + 1) (by omega) (fun w => |1 + w|)
  rw [show 2 * s + 1 + 2 = 2 * s + 3 from by omega] at h
  rw [h, show (2 * s + 1 + 1) / 2 = s + 1 from by omega,
    show 2 * s + 1 - (s + 1) = s from by omega]
  norm_num
  ring

/-- Centred at `2`, their absolute deviations add up to `m+1`. -/
theorem sum_coef_dev (s : ℕ) :
    ∑ i, |(|1 + gFamily (2 * s + 3) i|) - 2| = ((2 * s + 3 : ℕ) : ℝ) + 1 := by
  have h := sum_fn_gFamily (2 * s + 1) (by omega) (fun w => |(|1 + w|) - 2|)
  rw [show 2 * s + 1 + 2 = 2 * s + 3 from by omega] at h
  rw [h, show (2 * s + 1 + 1) / 2 = s + 1 from by omega,
    show 2 * s + 1 - (s + 1) = s from by omega]
  norm_num
  ring

/-! ## The band as a linear lower bound -/

/-- **A two-sided band around `1/m` bounds any linear functional from below**, for any centre
`a`: `Σ π c ≥ (Σ c)/m - (η/m) Σ |c - a|`.  The centre is free because the deviations `π - 1/m`
sum to zero. -/
theorem band_linear_lower {ι : Type*} [Fintype ι] (π c : ι → ℝ) (mR η a : ℝ) (hmR : 0 < mR)
    (hcard : (Fintype.card ι : ℝ) = mR) (hsum : ∑ i, π i = 1)
    (hband : ∀ i, |π i - 1 / mR| ≤ η / mR) :
    (∑ i, c i) / mR - η / mR * ∑ i, |c i - a| ≤ ∑ i, π i * c i := by
  have key : ∀ i, -(η / mR * |c i - a|) ≤ (π i - 1 / mR) * (c i - a) := by
    intro i
    have h1 := neg_abs_le ((π i - 1 / mR) * (c i - a))
    rw [abs_mul] at h1
    have h2 : |π i - 1 / mR| * |c i - a| ≤ η / mR * |c i - a| :=
      mul_le_mul_of_nonneg_right (hband i) (abs_nonneg _)
    linarith
  have hlow := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => key i)
  have hneg : ∑ i, -(η / mR * |c i - a|) = -(η / mR * ∑ i, |c i - a|) := by
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
  have hexp : ∀ i, (π i - 1 / mR) * (c i - a) = π i * c i - a * π i - c i / mR + a / mR := by
    intro i; ring
  have hconst : ∑ _i : ι, a / mR = a := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hdecomp : ∑ i, (π i - 1 / mR) * (c i - a)
      = ∑ i, π i * c i - a * 1 - (∑ i, c i) / mR + a := by
    rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
      ← Finset.sum_div, hconst]
  rw [hneg, hdecomp] at hlow
  linarith

/-! ## Budget `m - 1` at an actual law -/

theorem rankOf_isOddFamily {m : ℕ} (g : Ranking m) (hg : IsOddFamily g)
    (σ : Equiv.Perm (Fin m)) : IsOddFamily (rankOf g σ) where
  weight := fun i => hg.weight (σ i)
  total := by
    show ∑ i, g (σ i) = -1
    rw [Equiv.sum_comp σ g]
    exact hg.total

/-- The regret at budget `m-1`, for odd `m`, is the last item's coefficient over `D`. -/
theorem regret_last (s : ℕ) (σ : Equiv.Perm (Fin (2 * s + 3))) :
    regret (gFamily (2 * s + 3)) σ (denom (2 * s + 3)) (2 * s + 3 - 1)
      = |1 + gFamily (2 * s + 3) (σ ⟨2 * s + 3 - 1, by omega⟩)| / denom (2 * s + 3) := by
  have hodd : IsOddFamily (gFamily (2 * s + 3)) := by
    have := gFamily_isOddFamily (2 * s + 1) (by omega) (by omega)
    rwa [show 2 * s + 1 + 2 = 2 * s + 3 from by omega] at this
  unfold regret
  rw [excess_last (by omega) (by omega) (rankOf (gFamily (2 * s + 3)) σ)
    (rankOf_isOddFamily _ hodd σ)]
  congr 1
  rw [show (-1 : ℝ) - rankOf (gFamily (2 * s + 3)) σ ⟨2 * s + 3 - 1, by omega⟩
      = -(1 + gFamily (2 * s + 3) (σ ⟨2 * s + 3 - 1, by omega⟩)) from by
        unfold rankOf; ring, abs_neg]

/-- The last-position law of `P`. -/
noncomputable def lastLaw {m : ℕ} (hm : 0 < m) (P : Equiv.Perm (Fin m) → ℝ) (i : Fin m) : ℝ :=
  ∑ σ, P σ * (if i = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0)

theorem lastLaw_sum {m : ℕ} (hm : 0 < m) (P : Equiv.Perm (Fin m) → ℝ) (hP : ∑ σ, P σ = 1) :
    ∑ i, lastLaw hm P i = 1 := by
  calc ∑ i, lastLaw hm P i = ∑ σ, P σ := by
        unfold lastLaw
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [← Finset.mul_sum]
        simp
    _ = 1 := hP

/-- **The retained-prefix band at `k = m-1` is a two-sided band on the last position.** -/
theorem lastLaw_band {m : ℕ} (hm : 0 < m) (P : Equiv.Perm (Fin m) → ℝ) (η : ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (i : Fin m) :
    |lastLaw hm P i - 1 / (m : ℝ)| ≤ η / (m : ℝ) := by
  have hb := hP.2.2 (m - 1) (by omega) i
  simp only [id_eq] at hb
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hlast : lastLaw hm P i = 1 - ∑ σ, P σ * inPrefixInd σ (m - 1) i := by
    unfold lastLaw
    rw [Finset.sum_congr rfl (fun σ _ => by rw [last_eq_one_sub_inPrefix hm σ i])]
    rw [show (∑ σ, P σ * (1 - inPrefixInd σ (m - 1) i))
        = ∑ σ, P σ - ∑ σ, P σ * inPrefixInd σ (m - 1) i from by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun σ _ => by ring),
      hP.2.1]
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hcast] at hb
  rw [hlast]
  have heq : 1 - ∑ σ, P σ * inPrefixInd σ (m - 1) i - 1 / (m : ℝ)
      = -((∑ σ, P σ * inPrefixInd σ (m - 1) i) - ((m : ℝ) - 1) / (m : ℝ)) := by
    field_simp; ring
  rw [heq, abs_neg]
  exact hb

/-- The expected regret at budget `m-1` is the last-position law against the coefficients. -/
theorem expect_last (s : ℕ) (P : Equiv.Perm (Fin (2 * s + 3)) → ℝ) :
    ∑ σ, P σ * regret (gFamily (2 * s + 3)) σ (denom (2 * s + 3)) (2 * s + 3 - 1)
      = (∑ i, lastLaw (by omega) P i * |1 + gFamily (2 * s + 3) i|) / denom (2 * s + 3) := by
  rw [Finset.sum_congr rfl (fun σ _ => by rw [regret_last s σ])]
  have hinner : ∀ σ : Equiv.Perm (Fin (2 * s + 3)),
      ∑ i, P σ * (if i = σ ⟨2 * s + 3 - 1, by omega⟩ then (1 : ℝ) else 0)
          * |1 + gFamily (2 * s + 3) i|
        = P σ * |1 + gFamily (2 * s + 3) (σ ⟨2 * s + 3 - 1, by omega⟩)| := by
    intro σ
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [show P σ * (if i = σ ⟨2 * s + 3 - 1, by omega⟩ then (1 : ℝ) else 0)
            * |1 + gFamily (2 * s + 3) i|
          = if i = σ ⟨2 * s + 3 - 1, by omega⟩
              then P σ * |1 + gFamily (2 * s + 3) i| else 0 from by
            split_ifs <;> ring])]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
  unfold lastLaw
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun σ _ => hinner σ), Finset.sum_div]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  ring

/-! ## The headline -/

/-- **The relaxed-band lower bound, at the value.**  For odd `m = 2s+3` and every `η ≥ 0`,
`V_m(η) ≥ (m+3-(m+1)η)/(m(m+4))`. -/
theorem relaxed_value (s : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    (((2 * s + 3 : ℕ) : ℝ) + 3 - (((2 * s + 3 : ℕ) : ℝ) + 1) * η)
        / (((2 * s + 3 : ℕ) : ℝ) * (((2 * s + 3 : ℕ) : ℝ) + 4))
      ≤ value (2 * s + 3) (by omega) η := by
  set m := 2 * s + 3 with hmdef
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hD : (0 : ℝ) < denom m := by unfold denom; linarith
  apply value_lower m (by omega) η _ hη
  intro P hP
  have hmem : m - 1 ∈ budgets m := by simp [budgets]; omega
  have hle : ∑ σ, P σ * regret (gFamily m) (id σ) (denom m) (m - 1)
      ≤ objective m (by omega) P :=
    Finset.le_sup' (fun k => ∑ σ, P σ * regret (gFamily m) (id σ) (denom m) k) hmem
  simp only [id_eq] at hle
  rw [expect_last s P] at hle
  have hlin := band_linear_lower (lastLaw hm0 P) (fun i => |1 + gFamily m i|) (m : ℝ) η 2 hmR
    (by simp) (lastLaw_sum hm0 P hP.2.1) (lastLaw_band hm0 P η hP)
  rw [sum_coef s, sum_coef_dev s] at hlin
  have hfrac : ((m : ℝ) + 3 - ((m : ℝ) + 1) * η) / ((m : ℝ) * ((m : ℝ) + 4))
      = (((m : ℝ) + 3) / (m : ℝ) - η / (m : ℝ) * ((m : ℝ) + 1)) / denom m := by
    unfold denom
    field_simp
    try ring
  rw [hfrac]
  calc (((m : ℝ) + 3) / (m : ℝ) - η / (m : ℝ) * ((m : ℝ) + 1)) / denom m
      ≤ (∑ i, lastLaw hm0 P i * |1 + gFamily m i|) / denom m :=
        div_le_div_of_nonneg_right hlin hD.le
    _ ≤ objective m (by omega) P := hle

/-- **The same, at any odd `m ≥ 3`.** -/
theorem relaxed_value_odd (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (η : ℝ) (hη : 0 ≤ η) :
    ((m : ℝ) + 3 - ((m : ℝ) + 1) * η) / ((m : ℝ) * ((m : ℝ) + 4))
      ≤ value m (by omega) η := by
  obtain ⟨s, rfl⟩ : ∃ s, m = 2 * s + 3 := ⟨(m - 3) / 2, by omega⟩
  exact relaxed_value s η hη

/-- **Linear in `m`**: at any `η ≤ η₀ < 1` the relaxed odd value is at least
`(1-η₀)/(m+4)`, against the free value `2/((m+4)(m-1))`. -/
theorem relaxed_value_linear (m : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (η η₀ : ℝ)
    (hη : 0 ≤ η) (hη₀ : η ≤ η₀) (hη₁ : η₀ < 1) :
    (1 - η₀) / ((m : ℝ) + 4) ≤ value m (by omega) η := by
  refine le_trans ?_ (relaxed_value_odd m hm hmo η hη)
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [div_le_div_iff₀ (by linarith) (by positivity)]
  have hin : 0 ≤ 3 + (m : ℝ) * η₀ - ((m : ℝ) + 1) * η := by nlinarith
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) + 4) hin]

end CIGAMF.P13.PaperCRelaxedJoin

#print axioms CIGAMF.P13.PaperCRelaxedJoin.relaxed_value
#print axioms CIGAMF.P13.PaperCRelaxedJoin.relaxed_value_odd
#print axioms CIGAMF.P13.PaperCRelaxedJoin.relaxed_value_linear
