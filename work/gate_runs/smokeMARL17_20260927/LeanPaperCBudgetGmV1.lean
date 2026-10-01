import «LeanPaperCBudgetFamiliesV1»

/-!
# Paper C: on `g_m`, knowing the budget in advance is worth nothing over a band range

`g_m = (-3, -1 × p, +1 × q, +3)`, `D = m + 4`, interior budgets `1, …, m-1`.

* `aware_even`: for even `m ≥ 4` and `0 ≤ η ≤ (m-2)/(2(m-1))`, the budget-aware value equals the
  universal value, `B(η) = U(η) = 4(1-η)/(mD)`.
  - Certificate: at budget one, removing a heavy item costs `2/D` more than the baseline and a
    light item costs nothing; the band gives each heavy item mass at least `(1-η)/m`.
* `aware_odd`: for odd `m ≥ 3` and `0 ≤ η ≤ 1 - 2/(m(m-1))`,
  `B(η) = U(η) = (m+3-(m+1)η)/(mD)`.
  - Certificate at budget `m-1`: the kept set misses one item `j` and costs `|-1-g_j|/D`, which is
    `2 - β_j` with `β = 2` on the light negatives, `-2` on `+3` and `0` elsewhere.
So on these ranges every policy that learns the budget before acting, and optimises each budget
separately under the same band, does no better than the best single ranking.
-/

namespace CIGAMF.P13.PaperCBudgetGm

open Finset
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCFrontier CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCBudgetAware CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCStabilityFamily
open CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCEndpointLaw CIGAMF.P13.PaperCOddFrontier
open CIGAMF.P13.PaperCBaselineAttain CIGAMF.P13.PaperCRelaxedJoin

/-- **Even `m`: the budget-one layer forces the universal value.** -/
theorem aware_even (m : ℕ) (hm : 4 ≤ m) (heven : Even m) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ etaStar m) :
    awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
        = 4 * (1 - η) / ((m : ℝ) * ((m : ℝ) + 4))
      ∧ trueValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
        = 4 * (1 - η) / ((m : ℝ) * ((m : ℝ) + 4)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hU : trueValue (gFamily (n + 2)) η (interiorK (n + 2)) (interiorK_nonempty (n + 2) (by omega))
      = 4 * (1 - η) / (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 4)) := by
    rw [trueValue_family (n + 2) (by omega) η, even_frontier_all (n + 2) hm heven η hη0]
    apply max_eq_right
    unfold freeValue denom
    unfold etaStar at hη
    push_cast at hη ⊢
    have hd : (0 : ℝ) < 2 * ((n : ℝ) + 2 - 1) := by linarith
    have h2 : 2 * η * ((n : ℝ) + 2 - 1) ≤ (n : ℝ) + 2 - 2 := by
      rw [le_div_iff₀ hd] at hη; linarith
    rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 2 + 4) (sub_nonneg.mpr h2)]
  refine ⟨le_antisymm ((aware_le_true _ η hη0 _ _).trans (le_of_eq hU)) ?_, hU⟩
  -- the lower side, at budget one
  set k1 : Fin (n + 2 + 1) := ⟨1, by omega⟩ with hk1
  have hk1K : k1 ∈ interiorK (n + 2) := by simp [interiorK, hk1] <;> omega
  have hD : 0 < normMass (gFamily (n + 2)) := by
    rw [CIGAMF.P13.PaperCBaselineAttain.normMass_gFamily (n + 2) (by omega)]; positivity
  have hbase : trueBaseline (gFamily (n + 2)) k1 = 1 := by
    rw [familyBaselineIdentification_holds (n + 2) (by omega) k1 (by simp [hk1])
      (by simp [hk1])]
    simp [hk1]
  have hlay := layer_ge_of_linear (gFamily (n + 2)) η k1 (sub_nonempty η hη0 k1) hD 0
    (fun i => |gFamily (n + 2) i| - 1) (by
      intro S hS
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hS
      rw [Finset.sum_singleton, Finset.sum_singleton, hbase]
      linarith)
  have hs1 : ∑ i, (|gFamily (n + 2) i| - 1) = 4 := by
    have := sum_fn_gFamily n (by omega) (fun x => |x| - 1)
    rw [this]; norm_num
  have hs2 : ∑ i, |(|gFamily (n + 2) i| - 1)| = 4 := by
    have := sum_fn_gFamily n (by omega) (fun x => |(|x| - 1)|)
    rw [this]; norm_num
  rw [hs1, hs2, CIGAMF.P13.PaperCBaselineAttain.normMass_gFamily (n + 2) (by omega)] at hlay
  refine le_trans (le_of_eq ?_) (hlay.trans
    (Finset.le_sup' (fun k => layerValue (gFamily (n + 2)) η k) hk1K))
  simp only [hk1]
  push_cast
  field_simp
  ring

/-- **Odd `m`: the budget-`(m-1)` layer forces the universal value.** -/
theorem aware_odd (m : ℕ) (hm : 3 ≤ m) (hodd : m % 2 = 1) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 - 2 / ((m : ℝ) * ((m : ℝ) - 1))) :
    awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
        = ((m : ℝ) + 3 - ((m : ℝ) + 1) * η) / ((m : ℝ) * ((m : ℝ) + 4))
      ∧ trueValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
        = ((m : ℝ) + 3 - ((m : ℝ) + 1) * η) / ((m : ℝ) * ((m : ℝ) + 4)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  push_cast at hη ⊢
  have hpos : 0 < ((n : ℝ) + 2) * ((n : ℝ) + 2 - 1) := by nlinarith
  have hη1 : η ≤ 1 := hη.trans (by
    have : 0 ≤ 2 / (((n : ℝ) + 2) * ((n : ℝ) + 2 - 1)) := div_nonneg (by norm_num) hpos.le
    linarith)
  have hη' : η * (((n : ℝ) + 2) * ((n : ℝ) + 2 - 1))
      ≤ ((n : ℝ) + 2) * ((n : ℝ) + 2 - 1) - 2 := by
    have := mul_le_mul_of_nonneg_right hη hpos.le
    rwa [sub_mul, one_mul, div_mul_cancel₀ _ hpos.ne'] at this
  have hU : trueValue (gFamily (n + 2)) η (interiorK (n + 2)) (interiorK_nonempty (n + 2) (by omega))
      = ((n : ℝ) + 2 + 3 - ((n : ℝ) + 2 + 1) * η) / (((n : ℝ) + 2) * ((n : ℝ) + 2 + 4)) := by
    rw [trueValue_family (n + 2) (by omega) η, odd_frontier (n + 2) hm hodd η hη0]
    push_cast
    apply max_eq_left
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ 1 - η)]
    unfold freeValue denom
    push_cast
    have h1 : (n : ℝ) + 2 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 + 4 ≠ 0 := by positivity
    have h3 : (n : ℝ) + 2 - 1 ≠ 0 := by linarith
    have eL : 2 / (((n : ℝ) + 2 + 4) * ((n : ℝ) + 2 - 1)) + (1 - η) / (((n : ℝ) + 2) * ((n : ℝ) + 2 + 4))
        = (2 * ((n : ℝ) + 2) + (1 - η) * ((n : ℝ) + 2 - 1))
          / (((n : ℝ) + 2) * ((n : ℝ) + 2 + 4) * ((n : ℝ) + 2 - 1)) := by
      field_simp
    have eR : ((n : ℝ) + 2 + 3 - ((n : ℝ) + 2 + 1) * η) / (((n : ℝ) + 2) * ((n : ℝ) + 2 + 4))
        = (((n : ℝ) + 2 + 3 - ((n : ℝ) + 2 + 1) * η) * ((n : ℝ) + 2 - 1))
          / (((n : ℝ) + 2) * ((n : ℝ) + 2 + 4) * ((n : ℝ) + 2 - 1)) := by
      field_simp
    rw [eL, eR]
    refine div_le_div_of_nonneg_right ?_
      (mul_pos (mul_pos (by positivity) (by positivity)) (by linarith)).le
    nlinarith [hη']
  refine ⟨le_antisymm ((aware_le_true _ η hη0 _ _).trans (le_of_eq hU)) ?_, hU⟩
  -- the lower side, at budget m - 1 = n + 1
  set km : Fin (n + 2 + 1) := ⟨n + 1, by omega⟩ with hkm
  have hkK : km ∈ interiorK (n + 2) := by simp [interiorK, hkm]
  have hD : 0 < normMass (gFamily (n + 2)) := by
    rw [CIGAMF.P13.PaperCBaselineAttain.normMass_gFamily (n + 2) (by omega)]; positivity
  have hbase : trueBaseline (gFamily (n + 2)) km = 0 := by
    rw [familyBaselineIdentification_holds (n + 2) (by omega) km (by simp [hkm])
      (by simp [hkm])]
    simp only [hkm]
    have : (n + 1) % 2 = 0 := by omega
    rw [this]; simp
  -- the family sums
  have hp : 2 * (((n + 1) / 2 : ℕ) : ℝ) = (n : ℝ) + 1 := by
    have : 2 * ((n + 1) / 2) = n + 1 := by omega
    exact_mod_cast this
  have hq : 2 * ((n - (n + 1) / 2 : ℕ) : ℝ) + 1 = (n : ℝ) := by
    have : 2 * (n - (n + 1) / 2) + 1 = n := by omega
    exact_mod_cast this
  set β : Fin (n + 2) → ℝ := fun i => 2 - |-1 - gFamily (n + 2) i| with hβ
  have hsβ : ∑ i, β i = (n : ℝ) - 1 := by
    have := sum_fn_gFamily n (by omega) (fun x => 2 - |-1 - x|)
    rw [hβ, this]; norm_num; linarith
  have hsβa : ∑ i, |β i| = (n : ℝ) + 3 := by
    have := sum_fn_gFamily n (by omega) (fun x => abs (2 - |-1 - x|))
    rw [hβ, this]; norm_num; linarith
  have hsg : ∑ i, gFamily (n + 2) i = -1 := by
    have := sum_fn_gFamily n (by omega) (fun x => x)
    rw [this]; linarith
  have hlay := layer_ge_of_linear (gFamily (n + 2)) η km (sub_nonempty η hη0 km) hD
    (3 - (n : ℝ)) β (by
      intro S hS
      have hc : Sᶜ.card = 1 := by
        rw [Finset.card_compl, hS, Fintype.card_fin]; simp [hkm]
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
      have hSj : S = {j}ᶜ := by rw [← hj, compl_compl]
      subst hSj
      have e1 := Finset.sum_add_sum_compl ({j} : Finset (Fin (n + 2))) β
      have e2 := Finset.sum_add_sum_compl ({j} : Finset (Fin (n + 2))) (gFamily (n + 2))
      rw [Finset.sum_singleton] at e1 e2
      have hsum_g : ∑ i ∈ ({j} : Finset (Fin (n + 2)))ᶜ, gFamily (n + 2) i
          = -1 - gFamily (n + 2) j := by linarith
      have hsum_b : ∑ i ∈ ({j} : Finset (Fin (n + 2)))ᶜ, β i = (n : ℝ) - 1 - β j := by
        linarith
      rw [hsum_g, hsum_b, hbase, hβ]
      simp only
      linarith)
  rw [hsβ, hsβa, CIGAMF.P13.PaperCBaselineAttain.normMass_gFamily (n + 2) (by omega)] at hlay
  refine le_trans (le_of_eq ?_) (hlay.trans
    (Finset.le_sup' (fun k => layerValue (gFamily (n + 2)) η k) hkK))
  simp only [hkm]
  push_cast
  field_simp
  ring

#print axioms aware_even
#print axioms aware_odd

end CIGAMF.P13.PaperCBudgetGm
