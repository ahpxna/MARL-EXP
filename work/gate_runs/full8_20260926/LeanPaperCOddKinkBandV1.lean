import «LeanPaperCOddKinkLawV1»

/-!
# Paper C: the odd frontier, part 3 -- the kink law's band

The kink law of `LeanPaperCOddKinkLawV1` is feasible at `eta_t = 1 - 2/(m(m-1))`, at every
`m = 2s+3` with `s >= 2`.  With `u = 1/(m^2(m-1))`, the class count of weight `w` in the
prefix of length `k` is `u X_w(k)`, and after scaling by `1/u` the band is the polynomial
inequality

    |X_w(k) - N_w k m (m-1)| <= N_w (m (m-1) - 2),

with `N_w` the class size.  The slot part is symmetrised by the two versions, so the heavy
classes see `[t < k] + [t+1 < k]` summed over slots and the light classes see what is left
of `k`; parity enters only through the three single components.  At `k = m-1` the `+3`,
`-1` and `+1` classes meet the band exactly, which is why this is the crossing point.
-/

namespace CIGAMF.P13.PaperCOddKinkBand

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCInstantiation CIGAMF.P13.PaperCFamily
open CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCPerm
open CIGAMF.P13.PaperCRelabelBandJoin CIGAMF.P13.PaperCFam13
open CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCOddBreakpointEndgame
open CIGAMF.P13.PaperCEndpointLaw CIGAMF.P13.PaperCRelaxedJoin CIGAMF.P13.PaperCOddKink
open CIGAMF.P13.PaperCOddKinkLaw

/-! ## 1. Scaling -/

theorem scale_band (X a b u : ℝ) (hu : 0 < u) (h : |X - a / u| ≤ b / u) :
    |u * X - a| ≤ b := by
  have hid : u * X - a = u * (X - a / u) := by field_simp
  rw [hid, abs_mul, abs_of_pos hu]
  calc u * |X - a / u| ≤ u * (b / u) := mul_le_mul_of_nonneg_left h hu.le
    _ = b := by field_simp

/-! ## 2. Slot sums -/

theorem sum_lt_ge (n k : ℕ) (hk : n ≤ k) :
    (∑ t ∈ range n, if t < k then (1 : ℝ) else 0) = (n : ℝ) := by
  rw [Finset.sum_congr rfl (fun t ht => by
    rw [if_pos (show t < k by have := Finset.mem_range.mp ht; omega)])]
  simp

/-- Heavy slot indicator, summed with the slot masses. -/
noncomputable def SH (s k : ℕ) : ℝ :=
  if k ≤ 2 * s + 1 then (mR s ^ 2 + 1) / 2 * (2 * (k : ℝ) - 1)
      - (mR s - 3) / 2 * (1 + (if 2 ≤ k then 1 else 0))
  else (mR s ^ 2 + 1) / 2 * (4 * (s : ℝ) + 2) - (mR s - 3)

theorem heavy_pair (t k : ℕ) :
    countIns t 3 k + countIns t (-3) k
      = (if t < k then (1 : ℝ) else 0) + (if t + 1 < k then (1 : ℝ) else 0) := by
  rw [countIns_three, countIns_neg_three]

theorem slot_heavy (s k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 2 * s + 2) :
    ∑ t : Fin (2 * s + 1), alpha s t / 2 * (countIns t 3 k + countIns t (-3) k) = SH s k := by
  rw [Fin.sum_univ_eq_sum_range
    (fun t : ℕ => alpha s t / 2 * (countIns t 3 k + countIns t (-3) k)) (2 * s + 1)]
  simp only [heavy_pair]
  rw [Finset.sum_range_succ']
  have hrest : ∀ t ∈ range (2 * s), alpha s (t + 1) / 2
      * ((if t + 1 < k then (1 : ℝ) else 0) + (if t + 1 + 1 < k then (1 : ℝ) else 0))
      = (mR s ^ 2 + 1) / 2
        * ((if t + 1 < k then (1 : ℝ) else 0) + (if t + 1 + 1 < k then (1 : ℝ) else 0)) := by
    intro t _; unfold alpha; rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl hrest, ← Finset.mul_sum, Finset.sum_add_distrib]
  -- the full sums over `range (2s+1)`, peeled at `0`
  have hA := sum_shift (2 * s) (fun b => if b < k then (1 : ℝ) else 0)
  have hB := sum_shift (2 * s) (fun b => if b + 1 < k then (1 : ℝ) else 0)
  rw [hA, hB]
  unfold alpha SH
  rw [if_pos rfl]
  by_cases hk2 : k ≤ 2 * s + 1
  · rw [if_pos hk2, sum_ind_lt (2 * s + 1) k hk2]
    have hB' : (∑ b ∈ range (2 * s + 1), if b + 1 < k then (1 : ℝ) else 0) = (k : ℝ) - 1 := by
      rw [Finset.sum_congr rfl (fun b _ => by
          rw [show (if b + 1 < k then (1 : ℝ) else 0) = if b < k - 1 then 1 else 0 from by
            by_cases h : b + 1 < k
            · rw [if_pos h, if_pos (by omega)]
            · rw [if_neg h, if_neg (by omega)]]),
        sum_ind_lt (2 * s + 1) (k - 1) (by omega), Nat.cast_sub hk1]
      simp
    rw [hB', if_pos (show 0 < k by omega)]
    by_cases h2 : 2 ≤ k
    · rw [if_pos (show 0 + 1 < k by omega), if_pos h2]; unfold mR; ring
    · rw [if_neg (show ¬ (0 + 1 < k) by omega), if_neg h2]; unfold mR; ring
  · rw [if_neg hk2, sum_lt_ge (2 * s + 1) k (by omega)]
    have hB' : (∑ b ∈ range (2 * s + 1), if b + 1 < k then (1 : ℝ) else 0)
        = ((2 * s + 1 : ℕ) : ℝ) := by
      rw [Finset.sum_congr rfl (fun b hb => by
        rw [if_pos (show b + 1 < k by have := Finset.mem_range.mp hb; omega)])]
      simp
    rw [hB', if_pos (show 0 < k by omega), if_pos (show 0 + 1 < k by omega)]
    unfold mR; push_cast; ring

/-- All four weights of an inserted ranking together count every position. -/
theorem countIns_four (t k : ℕ) :
    countIns t (-1) k + countIns t 1 k + countIns t 3 k + countIns t (-3) k = (k : ℝ) := by
  unfold countIns
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => by
    rcases insWeight_mem t i with h | h | h | h <;> rw [h] <;> norm_num :
    ∀ i ∈ range k, ((if insWeight t i = -1 then (1 : ℝ) else 0) + (if insWeight t i = 1 then 1 else 0)
      + (if insWeight t i = 3 then 1 else 0) + (if insWeight t i = -3 then 1 else 0)) = 1)]
  simp

theorem slot_light (s k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 2 * s + 2) :
    ∑ t : Fin (2 * s + 1), alpha s t / 2 * (countIns t (-1) k + countIns t (-(-1)) k)
      = (k : ℝ) / 2 * ((mR s - 2) * (mR s ^ 2 + 1) - (mR s - 3)) - SH s k := by
  rw [← slot_heavy s k hk1 hk, ← sum_alpha, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have h4 := countIns_four t k
  rw [show -(-1 : ℝ) = 1 by ring]
  have : countIns t (-1) k + countIns t 1 k = (k : ℝ) - countIns t 3 k - countIns t (-3) k := by
    linarith
  rw [this]
  ring

/-! ## 3. The band, weight by weight -/

/-- The crossing point. -/
noncomputable def etaT (s : ℕ) : ℝ := 1 - 2 / (mR s * (mR s - 1))

/-- **The scaled band.**  A polynomial inequality for the bracket `X` gives the band. -/
theorem band_of_X (s : ℕ) (X N K : ℝ)
    (h : |X - N * K * (mR s * (mR s - 1))| ≤ N * (mR s * (mR s - 1) - 2)) :
    |uM s * X - N * (K / mR s)| ≤ N * (etaT s / mR s) := by
  have hm := mR_pos s
  have hm0 : mR s ≠ 0 := by linarith
  have hm1 : mR s - 1 ≠ 0 := by linarith
  apply scale_band X _ _ (uM s) (uM_pos s)
  have e1 : N * (K / mR s) / uM s = N * K * (mR s * (mR s - 1)) := by
    unfold uM; field_simp
  have e2 : N * (etaT s / mR s) / uM s = N * (mR s * (mR s - 1) - 2) := by
    unfold uM etaT; field_simp; try ring
  rw [e1, e2]; exact h

theorem cI_last_three (s k : ℕ) : countIns (2 * s + 1) 3 k = if 2 * s + 1 < k then 1 else 0 :=
  countIns_three _ _

theorem cI_last_neg_three (s k : ℕ) (hk : k ≤ 2 * s + 2) : countIns (2 * s + 1) (-3) k = 0 := by
  rw [countIns_neg_three, if_neg (by omega)]

theorem cI_zero_three (k : ℕ) (hk : 1 ≤ k) : countIns 0 3 k = 1 := by
  rw [countIns_three, if_pos (by omega)]

theorem cI_zero_neg_three (k : ℕ) : countIns 0 (-3) k = if 1 < k then 1 else 0 := by
  rw [countIns_neg_three]

theorem cI_last_neg_one (s k : ℕ) (hk : k ≤ 2 * s + 2) :
    countIns (2 * s + 1) (-1) k = evensBelow k := by
  rw [countIns_neg_one]
  have h1 : ¬ (2 * s + 1 < k ∧ Even (2 * s + 1)) :=
    fun h => (Nat.not_even_iff_odd.mpr ⟨s, rfl⟩) h.2
  have h2 : ¬ (2 * s + 1 + 1 < k ∧ Even (2 * s + 1 + 1)) := fun h => by have := h.1; omega
  rw [if_neg h1, if_neg h2]; ring

theorem cI_last_one (s k : ℕ) (hk : k ≤ 2 * s + 2) :
    countIns (2 * s + 1) 1 k = oddsBelow k - (if 2 * s + 1 < k then 1 else 0) := by
  rw [countIns_one]
  have h2 : ¬ (2 * s + 1 + 1 < k ∧ ¬ Even (2 * s + 1 + 1)) := fun h => by have := h.1; omega
  rw [if_neg h2]
  by_cases h : 2 * s + 1 < k
  · rw [if_pos ⟨h, Nat.not_even_iff_odd.mpr ⟨s, rfl⟩⟩, if_pos h]; ring
  · rw [if_neg (fun h' => h h'.1), if_neg h]; ring

theorem cI_zero_neg_one (k : ℕ) (hk : 1 ≤ k) : countIns 0 (-1) k = evensBelow k - 1 := by
  rw [countIns_neg_one, if_pos ⟨by omega, ⟨0, rfl⟩⟩,
    if_neg (fun h => (Nat.not_even_iff_odd.mpr (⟨0, rfl⟩ : Odd (0 + 1))) h.2)]
  ring

theorem cI_zero_one (k : ℕ) : countIns 0 1 k = oddsBelow k - (if 1 < k then 1 else 0) := by
  rw [countIns_one, if_neg (fun h => h.2 ⟨0, rfl⟩)]
  by_cases h : 1 < k
  · rw [if_pos ⟨h, Nat.not_even_iff_odd.mpr (⟨0, rfl⟩ : Odd (0 + 1))⟩, if_pos h]; ring
  · rw [if_neg (fun h' => h h'.1), if_neg h]; ring

/-! ### `+3` -/

theorem band_three (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 2 * s + 2) :
    |prefixClassCount (gFamily (2 * s + 3)) (kperm s hs) (kq s) k 3 - 1 * ((k : ℝ) / mR s)|
      ≤ 1 * (etaT s / mR s) := by
  rw [pcc_split s hs k hk 3, show (-(3 : ℝ)) = -3 by ring, slot_heavy s k hk1 hk,
    cI_last_three]
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  apply band_of_X
  unfold SH mR
  by_cases hk2 : k ≤ 2 * s + 1
  · rw [if_pos hk2, if_neg (show ¬ (2 * s + 1 < k) by omega), cnt_r3W_below s k hk2,
      cnt_r1W_below s k hk2, cI_last_three, if_neg (show ¬ (2 * s + 1 < k) by omega),
      cI_zero_three k hk1]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkR2 : (k : ℝ) ≤ 2 * s + 1 := by exact_mod_cast hk2
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2]
      have hkR3 : (2 : ℝ) ≤ k := by exact_mod_cast h2
      rw [abs_le]; constructor <;> nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k - 2)
        (by linarith : (0 : ℝ) ≤ s + 2), mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * s + 1 - k)
        (by linarith : (0 : ℝ) ≤ s + 2)]
    · have hk1' : k = 1 := by omega
      subst hk1'
      rw [if_neg h2]
      rw [abs_le]; push_cast; constructor <;> nlinarith
  · have hk2' : k = 2 * s + 2 := by omega
    subst hk2'
    rw [if_neg hk2, if_pos (show 2 * s + 1 < 2 * s + 2 by omega), cnt_r3W_last, cnt_r1W_last,
      cI_last_three, if_neg (show ¬ (2 * s + 1 < 2 * s + 1) by omega),
      cI_zero_three (2 * s + 1) (by omega)]
    norm_num
    rw [abs_le]; push_cast; constructor <;> nlinarith

/-! ### `-3` -/

theorem band_neg_three (s : ℕ) (hs : 1 ≤ s) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 2 * s + 2) :
    |prefixClassCount (gFamily (2 * s + 3)) (kperm s hs) (kq s) k (-3) - 1 * ((k : ℝ) / mR s)|
      ≤ 1 * (etaT s / mR s) := by
  rw [pcc_split s hs k hk (-3), show (-(-3 : ℝ)) = 3 by ring]
  rw [Finset.sum_congr rfl (fun t _ => by rw [add_comm (countIns t (-3) k)]),
    slot_heavy s k hk1 hk, cI_last_neg_three s k hk]
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  apply band_of_X
  unfold SH mR
  by_cases hk2 : k ≤ 2 * s + 1
  · rw [if_pos hk2, cnt_r3W_below s k hk2, cnt_r1W_below s k hk2, cI_last_neg_three s k hk,
      cI_zero_neg_three]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkR2 : (k : ℝ) ≤ 2 * s + 1 := by exact_mod_cast hk2
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2, if_pos (show 1 < k by omega)]
      have hkR3 : (2 : ℝ) ≤ k := by exact_mod_cast h2
      rw [abs_le]; constructor <;> nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ k - 2)
        (by linarith : (0 : ℝ) ≤ s + 2), mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * s + 1 - k)
        (by linarith : (0 : ℝ) ≤ s + 2)]
    · have hk1' : k = 1 := by omega
      subst hk1'
      rw [if_neg h2, if_neg (show ¬ (1 < 1) by omega)]
      rw [abs_le]; push_cast; constructor <;> nlinarith
  · have hk2' : k = 2 * s + 2 := by omega
    subst hk2'
    rw [if_neg hk2, cnt_r3W_last, cnt_r1W_last, cI_last_neg_three s (2 * s + 1) (by omega),
      cI_zero_neg_three, if_pos (show 1 < 2 * s + 1 by omega)]
    norm_num
    rw [abs_le]; push_cast; constructor <;> nlinarith

/-! ### the light classes: parity values -/

theorem evens_one : evensBelow 1 = 1 := by
  have := evensBelow_two_succ 0; norm_num at this; exact this

theorem odds_one : oddsBelow 1 = 0 := by
  have := oddsBelow_two_succ 0; norm_num at this; exact this

theorem evens_last (s : ℕ) : evensBelow (2 * s + 2) = (s : ℝ) + 1 := by
  rw [show 2 * s + 2 = 2 * (s + 1) from by ring, evensBelow_two]; push_cast; ring

theorem odds_last (s : ℕ) : oddsBelow (2 * s + 2) = (s : ℝ) + 1 := by
  rw [show 2 * s + 2 = 2 * (s + 1) from by ring, oddsBelow_two]; push_cast; ring

/-! ### `-1` -/

theorem band_neg_one (s : ℕ) (hs : 2 ≤ s) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 2 * s + 2) :
    |prefixClassCount (gFamily (2 * s + 3)) (kperm s (by omega)) (kq s) k (-1)
        - ((s : ℝ) + 1) * ((k : ℝ) / mR s)| ≤ ((s : ℝ) + 1) * (etaT s / mR s) := by
  rw [pcc_split s (by omega) k hk (-1), slot_light s k hk1 hk, cI_last_neg_one s k hk]
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  apply band_of_X
  unfold SH mR
  by_cases hk2 : k ≤ 2 * s + 1
  · rw [if_pos hk2, cnt_r3W_below s k hk2, cnt_r1W_below s k hk2, cI_last_neg_one s k hk,
      cI_zero_neg_one k hk1]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2]
      rcases Nat.even_or_odd' k with ⟨j, hj | hj⟩
      · subst hj
        rw [evensBelow_two]
        have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
        have hj2 : (j : ℝ) ≤ s := by exact_mod_cast (show j ≤ s by omega)
        push_cast
        rw [abs_le]; constructor <;> nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ j - 1)
          (by positivity : (0 : ℝ) ≤ 2 * (s : ℝ) ^ 2 + 7 * s + 7),
          mul_nonneg (by linarith : (0 : ℝ) ≤ s - j)
          (by positivity : (0 : ℝ) ≤ 2 * (s : ℝ) ^ 2 + 7 * s + 7)]
      · subst hj
        rw [evensBelow_two_succ]
        have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
        have hj2 : (j : ℝ) ≤ s := by exact_mod_cast (show j ≤ s by omega)
        push_cast
        rw [abs_le]; constructor <;> nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ j - 1)
          (by positivity : (0 : ℝ) ≤ 2 * (s : ℝ) ^ 2 + 7 * s + 7),
          mul_nonneg (by linarith : (0 : ℝ) ≤ s - j)
          (by positivity : (0 : ℝ) ≤ 2 * (s : ℝ) ^ 2 + 7 * s + 7)]
    · have hk1' : k = 1 := by omega
      subst hk1'
      rw [if_neg h2, evens_one]
      rw [abs_le]; push_cast; constructor <;> nlinarith
  · have hk2' : k = 2 * s + 2 := by omega
    subst hk2'
    rw [if_neg hk2, cnt_r3W_last, cnt_r1W_last, cI_last_neg_one s (2 * s + 1) (by omega),
      cI_zero_neg_one (2 * s + 1) (by omega), evensBelow_two_succ, evens_last]
    norm_num
    rw [abs_le]; push_cast; constructor <;> nlinarith

/-! ### `+1` -/

theorem band_one (s : ℕ) (hs : 2 ≤ s) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 2 * s + 2) :
    |prefixClassCount (gFamily (2 * s + 3)) (kperm s (by omega)) (kq s) k 1
        - (s : ℝ) * ((k : ℝ) / mR s)| ≤ (s : ℝ) * (etaT s / mR s) := by
  rw [pcc_split s (by omega) k hk 1]
  rw [Finset.sum_congr rfl (fun t _ => by
      rw [show countIns t 1 k + countIns t (-1) k = countIns t (-1) k + countIns t (-(-1)) k from by
        rw [neg_neg, add_comm]]),
    slot_light s k hk1 hk, cI_last_one s k hk]
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hs4 : (4 : ℝ) ≤ (s : ℝ) ^ 2 := by nlinarith
  have he := evens_add_odds k
  apply band_of_X
  unfold SH mR
  by_cases hk2 : k ≤ 2 * s + 1
  · rw [if_pos hk2, if_neg (show ¬ (2 * s + 1 < k) by omega), cnt_r3W_below s k hk2,
      cnt_r1W_below s k hk2, cI_last_one s k hk, if_neg (show ¬ (2 * s + 1 < k) by omega),
      cI_zero_one]
    by_cases h2 : 2 ≤ k
    · rw [if_pos h2, if_pos (show 1 < k by omega)]
      rcases Nat.even_or_odd' k with ⟨j, hj | hj⟩
      · subst hj
        rw [oddsBelow_two]
        have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
        have hj2 : (j : ℝ) ≤ s := by exact_mod_cast (show j ≤ s by omega)
        push_cast
        rw [abs_le]; constructor <;> nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ j - 1)
          (by nlinarith : (0 : ℝ) ≤ 2 * (s : ℝ) ^ 2 + 3 * s - 1),
          mul_nonneg (by linarith : (0 : ℝ) ≤ s - j)
          (by nlinarith : (0 : ℝ) ≤ 2 * (s : ℝ) ^ 2 + 3 * s - 1)]
      · subst hj
        rw [oddsBelow_two_succ]
        have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (show 1 ≤ j by omega)
        have hj2 : (j : ℝ) ≤ s := by exact_mod_cast (show j ≤ s by omega)
        push_cast
        rw [abs_le]; constructor <;> nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ j - 1)
          (by nlinarith : (0 : ℝ) ≤ 2 * (s : ℝ) ^ 2 + 3 * s - 1),
          mul_nonneg (by linarith : (0 : ℝ) ≤ s - j)
          (by nlinarith : (0 : ℝ) ≤ 2 * (s : ℝ) ^ 2 + 3 * s - 1)]
    · have hk1' : k = 1 := by omega
      subst hk1'
      rw [if_neg h2, if_neg (show ¬ (1 < 1) by omega), odds_one]
      rw [abs_le]; push_cast; constructor <;> nlinarith
  · have hk2' : k = 2 * s + 2 := by omega
    subst hk2'
    rw [if_neg hk2, if_pos (show 2 * s + 1 < 2 * s + 2 by omega), cnt_r3W_last, cnt_r1W_last,
      cI_last_one s (2 * s + 1) (by omega), if_neg (show ¬ (2 * s + 1 < 2 * s + 1) by omega),
      cI_zero_one, if_pos (show 1 < 2 * s + 1 by omega), oddsBelow_two_succ, odds_last]
    norm_num
    rw [abs_le]; push_cast; constructor <;> nlinarith

end CIGAMF.P13.PaperCOddKinkBand

#print axioms CIGAMF.P13.PaperCOddKinkBand.band_three
#print axioms CIGAMF.P13.PaperCOddKinkBand.band_neg_three
#print axioms CIGAMF.P13.PaperCOddKinkBand.band_neg_one
#print axioms CIGAMF.P13.PaperCOddKinkBand.band_one
