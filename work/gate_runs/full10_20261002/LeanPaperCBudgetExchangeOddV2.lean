import «LeanPaperCBudgetExchangeOddV1»

/-!
# Paper C: one exchange reaches the budget-aware value of `g_m` for odd `m` (assembly)

`LeanPaperCBudgetExchangeOddV1` builds, for `m = 2h+3` with `h ≥ 1`, the committed law
`oddLaw` (band `0`) and the final sets `oddT` at the middle budgets `2 ≤ k ≤ m-2`: each is the
prefix edited by at most one exchange (`oddT_sdiff`), has size `k` (`oddT_card`) and has zero
regret (`oddT_cost`). This module adds the three missing pieces.

* `oddT_band`: the class-averaged final marginals lie within `etaOne h / m` of `k/m`, where
  `etaOne h = h(h+2)/(h+1)^2 = 1 - 1/(h+1)^2`. The band is on the scale `1/m`: the bound is
  `etaOne h / m`, not `etaOne h`. The deviation is exact per class:
  - odd `k`: `+(m-k)/(2(h+1)m)` on each heavy item, `-(m-k)/(2h(h+1)m)` on each `+1`,
    `-(m-k)/(2(h+1)^2 m)` on each `-1`;
  - even `k`: `+k/(2(h+1)m)` on each heavy item and each `+1`, `-k(h+2)/(2(h+1)^2 m)` on each
    `-1`; the largest, at `k = 2h`, is `etaOne h / m`.
* `end_budget`: at the budgets `1` and `m-1` a final set drawn independently from any subset
  law of the layer is reachable by one exchange, with that law's cost.
* `recourse_one_odd`: for odd `m ≥ 5` and every `η ≥ 0`, `V^{(1)}_{g_m}(η) = B_{g_m}(η)`.
  - For `η ≤ etaOne h` (which is `≤ η_t = 1 - 2/(m(m-1))`, `etaOne_le_etaT`), `B = U` already
    (`recourse_eq_aware_odd`).
  - For `η ≥ etaOne h` the plan commits to `oddLaw`, draws the end budgets independently from
    near-optimal subset laws, and edits the middle prefixes to `oddT` (cost `0`).
* `recourse_one_three`: the case `m = 3`, where both interior budgets are end budgets
  (`recourse_full`); `recourse_one_odd_all` joins the two for every odd `m ≥ 3`.
* `recourse_one_odd_satisfiable`: the hypotheses are met, on the plan branch, at `m = 5`, `η = 1`.
-/

namespace CIGAMF.P13.PaperCBudgetExchangeOddV2

open Finset
open CIGAMF.P13.PaperCRanking CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCRelabel
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCBudgetAware
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCLawPush CIGAMF.P13.PaperCEndpointLaw CIGAMF.P13.PaperCStabilityFamily
open CIGAMF.P13.PaperCBudgetSharp CIGAMF.P13.PaperCRelabelBandJoin
open CIGAMF.P13.PaperCBudgetExchangeOdd
open CIGAMF.P13.PaperCBudgetSym (class_card_m3 class_card_p3 class_card_m1 class_card_p1)

/-! ## 1. The band constant -/

/-- `etaOne h = h(h+2)/(h+1)^2 = 1 - 1/(h+1)^2`. -/
noncomputable def etaOne (h : ℕ) : ℝ := (h : ℝ) * ((h : ℝ) + 2) / ((h : ℝ) + 1) ^ 2

theorem etaOne_nonneg (h : ℕ) : 0 ≤ etaOne h := by unfold etaOne; positivity

theorem etaOne_le_one (h : ℕ) : etaOne h ≤ 1 := by
  unfold etaOne
  rw [div_le_one (by positivity)]
  nlinarith

/-- **The band constant is below the crossing point** `η_t = 1 - 2/(m(m-1))`, `m = 2h+3`. -/
theorem etaOne_le_etaT (h : ℕ) :
    etaOne h ≤ 1 - 2 / (((2 * h + 1 + 2 : ℕ) : ℝ) * (((2 * h + 1 + 2 : ℕ) : ℝ) - 1)) := by
  have hmR : ((2 * h + 1 + 2 : ℕ) : ℝ) = 2 * (h : ℝ) + 3 := by push_cast; ring
  have hA : (0 : ℝ) < (h : ℝ) + 1 := by positivity
  rw [hmR]
  have e1 : etaOne h = 1 - 1 / ((h : ℝ) + 1) ^ 2 := by
    unfold etaOne; field_simp; ring
  have e2 : (2 : ℝ) / ((2 * (h : ℝ) + 3) * ((2 * (h : ℝ) + 3) - 1))
      = 1 / ((2 * (h : ℝ) + 3) * ((h : ℝ) + 1)) := by
    rw [show (2 * (h : ℝ) + 3) - 1 = 2 * ((h : ℝ) + 1) by ring]
    field_simp
  rw [e1, e2]
  have : 1 / ((2 * (h : ℝ) + 3) * ((h : ℝ) + 1)) ≤ 1 / ((h : ℝ) + 1) ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  linarith

section Band

variable (h : ℕ)

/-! ## 2. The exchange correction, split by the position of the single -/

/-- The exchange-A part of the correction (single after the prefix). -/
noncomputable def cA (k s : ℕ) (b : Bool) (w : ℝ) : ℝ :=
  if k = 2 * s + 1 then
    -(if (if b then (-1 : ℝ) else 1) = w then 1 else 0)
      + (if (if b then (-1 : ℝ) else 1) * (-3) = w then 1 else 0)
  else 0

/-- The exchange-B part of the correction (single inside the prefix). -/
noncomputable def cB (k s : ℕ) (b : Bool) (w : ℝ) : ℝ :=
  if k % 2 = 0 ∧ (b = false ∨ k = 2 * s + 2) then
    -(if (-1 : ℝ) = w then 1 else 0) + (if ePat s b (k - 1) = w then 1 else 0)
  else 0

theorem corr_split (k s : ℕ) (b : Bool) (p : ℕ) (w : ℝ) :
    corr k s b p w = if p < k then cB k s b w else cA k s b w := by
  by_cases hp : p < k
  · rw [if_pos hp]
    have hA : ¬ exA k s p := by unfold exA; omega
    unfold corr cB
    rw [if_neg hA]
    by_cases hc : k % 2 = 0 ∧ (b = false ∨ k = 2 * s + 2)
    · have hB : exB k s b p := by unfold exB; exact ⟨hp, hc⟩
      rw [if_pos hB, if_pos hc]
    · have hB : ¬ exB k s b p := by unfold exB; exact fun hh => hc hh.2
      rw [if_neg hB, if_neg hc]
  · rw [if_neg hp]
    have hB : ¬ exB k s b p := by unfold exB; exact fun hh => hp hh.1
    unfold corr cA
    by_cases hc : k = 2 * s + 1
    · have hA : exA k s p := by unfold exA; exact ⟨by omega, hc⟩
      rw [if_pos hA, if_pos hc]
    · have hA : ¬ exA k s p := by unfold exA; exact fun hh => hc hh.2
      rw [if_neg hA, if_neg hB, if_neg hc]

/-- Summing the correction over the single's position. -/
theorem corr_psum (k s : ℕ) (hk : k ≤ 2 * h + 1 + 2) (b : Bool) (w : ℝ) :
    ∑ p : Fin (2 * h + 1 + 2), corr k s b p.val w
      = (k : ℝ) * cB k s b w + ((2 * h + 1 + 2 - k : ℕ) : ℝ) * cA k s b w := by
  simp_rw [corr_split]
  exact sum_pos_split h k hk _ _

/-- Summing exchange A over the slot. -/
theorem cA_ssum (k : ℕ) (hk : k ≤ 2 * h + 1) (b : Bool) (w : ℝ) :
    ∑ s : Fin (h + 1), cA k s.val b w
      = if k % 2 = 1 then
          -(if (if b then (-1 : ℝ) else 1) = w then 1 else 0)
            + (if (if b then (-1 : ℝ) else 1) * (-3) = w then 1 else 0)
        else 0 := by
  unfold cA
  exact CIGAMF.P13.PaperCBudgetExchange.slot_sum h k hk _

/-- Exactly one slot has its partner heavy item at `E`-index `k-1`, for even `k`. -/
theorem slot2_sum (k : ℕ) (hk2 : 2 ≤ k) (hk : k ≤ 2 * h + 2) (hev : k % 2 = 0) (c d : ℝ) :
    ∑ s : Fin (h + 1), (if k = 2 * s.val + 2 then c else d) = c + (h : ℝ) * d := by
  set s0 : Fin (h + 1) := ⟨(k - 2) / 2, by omega⟩ with hs0def
  have hs0 : s0.val = (k - 2) / 2 := rfl
  have e : ∀ s : Fin (h + 1), (if k = 2 * s.val + 2 then c else d)
      = d + (if k = 2 * s.val + 2 then c - d else 0) := by
    intro s; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun s _ => e s), Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.sum_eq_single s0]
  · rw [if_pos (by rw [hs0]; omega)]
    push_cast; ring
  · intro s _ hs
    rw [if_neg]
    intro h2; apply hs; exact Fin.ext (by rw [hs0]; omega)
  · intro h'; exact absurd (Finset.mem_univ _) h'

/-- The weight at `E`-index `k-1` in the unflipped pattern, `k` even. -/
theorem ePat_false_odd (s k : ℕ) (hk2 : 2 ≤ k) (hev : k % 2 = 0) :
    ePat s false (k - 1) = if k = 2 * s + 2 then -3 else 1 := by
  split_ifs with hks
  · rw [show k - 1 = 2 * s + 1 by omega, ePat_partner]; norm_num
  · rw [ePat_odd_light s (k - 1) (by omega) (by omega) false]; norm_num

theorem ePat_true_partner (s k : ℕ) (hks : k = 2 * s + 2) : ePat s true (k - 1) = 3 := by
  rw [show k - 1 = 2 * s + 1 by omega, ePat_partner]; norm_num

theorem cB_false_ssum (k : ℕ) (hk2 : 2 ≤ k) (hk : k ≤ 2 * h + 1) (w : ℝ) :
    ∑ s : Fin (h + 1), cB k s.val false w
      = if k % 2 = 0 then
          -((h : ℝ) + 1) * (if (-1 : ℝ) = w then 1 else 0) + (if (-3 : ℝ) = w then 1 else 0)
            + (h : ℝ) * (if (1 : ℝ) = w then 1 else 0)
        else 0 := by
  by_cases hev : k % 2 = 0
  · rw [if_pos hev]
    have e : ∀ s : Fin (h + 1), cB k s.val false w
        = -(if (-1 : ℝ) = w then 1 else 0)
          + (if k = 2 * s.val + 2 then (if (-3 : ℝ) = w then 1 else 0)
             else (if (1 : ℝ) = w then 1 else 0)) := by
      intro s
      unfold cB
      rw [if_pos ⟨hev, Or.inl rfl⟩, ePat_false_odd s.val k hk2 hev]
      by_cases hc : k = 2 * s.val + 2
      · rw [if_pos hc, if_pos hc]
      · rw [if_neg hc, if_neg hc]
    rw [Finset.sum_congr rfl (fun s _ => e s), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, slot2_sum h k hk2 (by omega) hev]
    push_cast; ring
  · rw [if_neg hev]
    refine Finset.sum_eq_zero fun s _ => ?_
    unfold cB
    rw [if_neg (fun hh => hev hh.1)]

theorem cB_true_ssum (k : ℕ) (hk2 : 2 ≤ k) (hk : k ≤ 2 * h + 1) (w : ℝ) :
    ∑ s : Fin (h + 1), cB k s.val true w
      = if k % 2 = 0 then -(if (-1 : ℝ) = w then 1 else 0) + (if (3 : ℝ) = w then 1 else 0)
        else 0 := by
  by_cases hev : k % 2 = 0
  · rw [if_pos hev]
    have e : ∀ s : Fin (h + 1), cB k s.val true w
        = if k = 2 * s.val + 2 then
            (-(if (-1 : ℝ) = w then 1 else 0) + (if (3 : ℝ) = w then 1 else 0)) else 0 := by
      intro s
      unfold cB
      by_cases hc : k = 2 * s.val + 2
      · rw [if_pos ⟨hev, Or.inr hc⟩, if_pos hc, ePat_true_partner s.val k hc]
      · have hn : ¬ (k % 2 = 0 ∧ (true = false ∨ k = 2 * s.val + 2)) := by
          rintro ⟨-, h1 | h1⟩
          · exact absurd h1 (by decide)
          · exact hc h1
        rw [if_neg hn, if_neg hc]
    rw [Finset.sum_congr rfl (fun s _ => e s), slot2_sum h k hk2 (by omega) hev]
    ring
  · rw [if_neg hev]
    refine Finset.sum_eq_zero fun s _ => ?_
    unfold cB
    rw [if_neg (fun hh => hev hh.1)]

/-- The summed correction, in closed form. -/
noncomputable def sigmaVal (k : ℕ) (w : ℝ) : ℝ :=
  if k % 2 = 1 then
    ((2 * h + 1 + 2 - k : ℕ) : ℝ) * (-(if (1 : ℝ) = w then 1 else 0)
      + (if (-3 : ℝ) = w then 1 else 0) - (if (-1 : ℝ) = w then 1 else 0)
      + (if (3 : ℝ) = w then 1 else 0))
  else (k : ℝ) * (-((h : ℝ) + 2) * (if (-1 : ℝ) = w then 1 else 0)
      + (if (-3 : ℝ) = w then 1 else 0) + (h : ℝ) * (if (1 : ℝ) = w then 1 else 0)
      + (if (3 : ℝ) = w then 1 else 0))

/-- **The correction summed over the slot, the flip and the single's position.** -/
theorem sigma_corr (k : ℕ) (hk2 : 2 ≤ k) (hk : k ≤ 2 * h + 1) (w : ℝ) :
    ∑ s : Fin (h + 1), ∑ p : Fin (2 * h + 1 + 2),
        (corr k s.val false p.val w + corr k s.val true p.val w) = sigmaVal h k w := by
  have e : ∀ s : Fin (h + 1), ∑ p : Fin (2 * h + 1 + 2),
      (corr k s.val false p.val w + corr k s.val true p.val w)
      = (k : ℝ) * cB k s.val false w + ((2 * h + 1 + 2 - k : ℕ) : ℝ) * cA k s.val false w
        + ((k : ℝ) * cB k s.val true w + ((2 * h + 1 + 2 - k : ℕ) : ℝ) * cA k s.val true w) := by
    intro s
    rw [Finset.sum_add_distrib, corr_psum h k s.val (by omega) false w,
      corr_psum h k s.val (by omega) true w]
  rw [Finset.sum_congr rfl (fun s _ => e s)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [cA_ssum h k hk false w, cA_ssum h k hk true w, cB_false_ssum h k hk2 hk w,
    cB_true_ssum h k hk2 hk w]
  unfold sigmaVal
  rcases Nat.mod_two_eq_zero_or_one k with hev | hodd
  · rw [if_neg (show ¬ k % 2 = 1 by omega), if_neg (show ¬ k % 2 = 1 by omega),
      if_pos hev, if_pos hev, if_neg (show ¬ k % 2 = 1 by omega)]
    ring
  · rw [if_pos hodd, if_pos hodd, if_neg (show ¬ k % 2 = 0 by omega),
      if_neg (show ¬ k % 2 = 0 by omega), if_pos hodd]
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul, neg_neg]
    ring

/-! ## 3. The band -/

theorem abs_le_of_mul (S A b : ℝ) (hb : 0 < b) (h1 : S * b ≤ A) (h2 : -S * b ≤ A) :
    |S| ≤ A / b := by
  rw [abs_le]
  constructor
  · rw [neg_le, le_div_iff₀ hb]; exact h2
  · rw [le_div_iff₀ hb]; exact h1

/-- **Each class's summed correction is within the band.** -/
theorem sigma_bound (hh : 1 ≤ h) (k : ℕ) (hk2 : 2 ≤ k) (hk : k ≤ 2 * h + 1) (w C : ℝ)
    (hwC : (w = -3 ∧ C = 1) ∨ (w = -1 ∧ C = (h : ℝ) + 1) ∨ (w = 1 ∧ C = (h : ℝ))
      ∨ (w = 3 ∧ C = 1)) :
    |sigmaVal h k w| ≤ 2 * ((h : ℝ) + 1) * C * etaOne h := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hpos : (0 : ℝ) < (h : ℝ) + 1 := by linarith
  have hE : 2 * ((h : ℝ) + 1) * C * etaOne h
      = (2 * C * (h : ℝ) * ((h : ℝ) + 2)) / ((h : ℝ) + 1) := by
    unfold etaOne; field_simp
  rw [hE]
  have hA : (0 : ℝ) ≤ (h : ℝ) * ((h : ℝ) + 1) := by positivity
  have hB : (0 : ℝ) ≤ ((h : ℝ) + 2) * ((h : ℝ) + 1) := by positivity
  have hC2 : (1 : ℝ) ≤ (h : ℝ) + 2 := by linarith
  unfold sigmaVal
  rcases Nat.mod_two_eq_zero_or_one k with hev | hodd
  · have hX : (k : ℝ) ≤ 2 * (h : ℝ) := by exact_mod_cast (show k ≤ 2 * h by omega)
    have hX0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    rw [if_neg (show ¬ k % 2 = 1 by omega)]
    generalize (k : ℝ) = X at hX hX0 ⊢
    apply abs_le_of_mul _ _ _ hpos
    all_goals
      rcases hwC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num <;>
        nlinarith [mul_le_mul_of_nonneg_right hX hpos.le, mul_le_mul_of_nonneg_right hX hA,
          mul_le_mul_of_nonneg_right hX hB, mul_nonneg hX0 hpos.le, mul_nonneg hX0 hA,
          mul_nonneg hX0 hB, mul_le_mul_of_nonneg_left hhR hA,
          mul_le_mul_of_nonneg_left hC2 hA, sq_nonneg (h : ℝ)]
  · have hX : ((2 * h + 1 + 2 - k : ℕ) : ℝ) ≤ 2 * (h : ℝ) := by
      exact_mod_cast (show 2 * h + 1 + 2 - k ≤ 2 * h by omega)
    have hX0 : (0 : ℝ) ≤ ((2 * h + 1 + 2 - k : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [if_pos hodd]
    generalize ((2 * h + 1 + 2 - k : ℕ) : ℝ) = X at hX hX0 ⊢
    apply abs_le_of_mul _ _ _ hpos
    all_goals
      rcases hwC with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num <;>
        nlinarith [mul_le_mul_of_nonneg_right hX hpos.le, mul_le_mul_of_nonneg_right hX hA,
          mul_le_mul_of_nonneg_right hX hB, mul_nonneg hX0 hpos.le, mul_nonneg hX0 hA,
          mul_nonneg hX0 hB, mul_le_mul_of_nonneg_left hhR hA,
          mul_le_mul_of_nonneg_left hC2 hA, sq_nonneg (h : ℝ)]

theorem dev_bound (C S : ℝ) (hC : 0 < C)
    (hS : |S| ≤ 2 * ((h : ℝ) + 1) * C * etaOne h) :
    |1 / (2 * ((h : ℝ) + 1) * (2 * (h : ℝ) + 3)) * S / C| * ((2 * h + 1 + 2 : ℕ) : ℝ)
      ≤ etaOne h := by
  have hmR : ((2 * h + 1 + 2 : ℕ) : ℝ) = 2 * (h : ℝ) + 3 := by push_cast; ring
  have hA : 0 < 2 * ((h : ℝ) + 1) * (2 * (h : ℝ) + 3) := by positivity
  have hC' := hC.ne'
  rw [abs_div, abs_mul, abs_of_pos (one_div_pos.mpr hA), abs_of_pos hC, hmR]
  rw [show 1 / (2 * ((h : ℝ) + 1) * (2 * (h : ℝ) + 3)) * |S| / C * (2 * (h : ℝ) + 3)
      = |S| / (2 * ((h : ℝ) + 1) * C) by field_simp]
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **The final item marginals are within `etaOne h / m` of `k/m`** at every middle budget. -/
theorem oddT_band (hh : 1 ≤ h) (k : Fin (2 * h + 1 + 2 + 1)) (hk2 : 2 ≤ k.val)
    (hkm : k.val ≤ 2 * h + 1) (i : Fin (2 * h + 1 + 2)) :
    |∑ x, oddQ h x * ((((oddT h hh k x).filter
        (fun j => gFamily (2 * h + 1 + 2) j = gFamily (2 * h + 1 + 2) i)).card : ℝ)
        / ((univ.filter (fun j : Fin (2 * h + 1 + 2) =>
            gFamily (2 * h + 1 + 2) j = gFamily (2 * h + 1 + 2) i)).card : ℝ))
      - (k.val : ℝ) / ((2 * h + 1 + 2 : ℕ) : ℝ)| ≤ etaOne h / ((2 * h + 1 + 2 : ℕ) : ℝ) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hmR : ((2 * h + 1 + 2 : ℕ) : ℝ) = 2 * (h : ℝ) + 3 := by push_cast; ring
  have hwv := gFamily_weights (2 * h + 1 + 2) i
  set w := gFamily (2 * h + 1 + 2) i with hw
  set C : ℝ := ((univ.filter (fun j : Fin (2 * h + 1 + 2) =>
      gFamily (2 * h + 1 + 2) j = w)).card : ℝ) with hCdef
  have hCpos : 0 < C := by
    have : 0 < (univ.filter (fun j : Fin (2 * h + 1 + 2) => gFamily (2 * h + 1 + 2) j = w)).card :=
      Finset.card_pos.mpr ⟨i, by simp [hw]⟩
    rw [hCdef]; exact_mod_cast this
  have hwC : (w = -3 ∧ C = 1) ∨ (w = -1 ∧ C = (h : ℝ) + 1) ∨ (w = 1 ∧ C = (h : ℝ))
      ∨ (w = 3 ∧ C = 1) := by
    rcases hwv with h1 | h1 | h1 | h1
    · refine Or.inl ⟨h1, ?_⟩
      rw [hCdef, h1, class_card_m3 (2 * h + 1) (by omega)]; norm_num
    · refine Or.inr (Or.inl ⟨h1, ?_⟩)
      rw [hCdef, h1, class_card_m1 (2 * h + 1) (by omega),
        show (2 * h + 1 + 1) / 2 = h + 1 by omega]; push_cast; ring
    · refine Or.inr (Or.inr (Or.inl ⟨h1, ?_⟩))
      rw [hCdef, h1, class_card_p1 (2 * h + 1) (by omega),
        show 2 * h + 1 - (2 * h + 1 + 1) / 2 = h by omega]
    · refine Or.inr (Or.inr (Or.inr ⟨h1, ?_⟩))
      rw [hCdef, h1, class_card_p3 (2 * h + 1) (by omega)]; norm_num
  have hwgf : w = -3 ∨ w = -1 ∨ w = 1 ∨ w = 3 := by
    rcases hwC with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h1))
    · exact Or.inr (Or.inr (Or.inr h1))
  have hsplit : ∑ x, oddQ h x * ((((oddT h hh k x).filter
        (fun j => gFamily (2 * h + 1 + 2) j = w)).card : ℝ) / C)
      = (∑ x, oddQ h x * (∑ i' ∈ univ.filter (fun i' : Fin (2 * h + 1 + 2) => i'.val < k.val),
            (if gFamily (2 * h + 1 + 2) (oddBase h hh x i') = w then (1 : ℝ) else 0))) / C
        + (∑ x, oddQ h x * corr k.val x.1.val x.2.1 x.2.2.val w) / C := by
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [oddT_count h hh k hk2 hkm x w]
    ring
  have hpa : (∑ x, oddQ h x * (∑ i' ∈ univ.filter (fun i' : Fin (2 * h + 1 + 2) => i'.val < k.val),
            (if gFamily (2 * h + 1 + 2) (oddBase h hh x i') = w then (1 : ℝ) else 0)))
      = C * ((k.val : ℝ) / (2 * (h : ℝ) + 3)) :=
    prefix_avg h hh k.val (by omega) w hwgf
  have hca : (∑ x, oddQ h x * corr k.val x.1.val x.2.1 x.2.2.val w)
      = 1 / (2 * ((h : ℝ) + 1) * (2 * (h : ℝ) + 3)) * sigmaVal h k.val w := by
    rw [odd_avg h (fun x => corr k.val x.1.val x.2.1 x.2.2.val w)]
    dsimp only
    rw [sigma_corr h k.val hk2 hkm w]
  rw [hsplit, hpa, hca]
  refine band_of_diff (δ := 1 / (2 * ((h : ℝ) + 1) * (2 * (h : ℝ) + 3)) * sigmaVal h k.val w / C)
    (by positivity) ?_ ?_
  · rw [hmR]
    have hC' := hCpos.ne'
    field_simp
    ring
  · exact dev_bound h C _ hCpos (sigma_bound h hh k.val hk2 hkm w C hwC)

/-! ## 4. The middle budgets and the end budgets -/

/-- **The middle plan**: feasible at every `η ≥ etaOne h`, with cost `0`. -/
theorem mid_spec (hh : 1 ≤ h) (η : ℝ) (hη : etaOne h ≤ η) (k : Fin (2 * h + 1 + 2 + 1))
    (hk2 : 2 ≤ k.val) (hkm : k.val ≤ 2 * h + 1) :
    CIGAMF.P13.PaperCBudgetExchange.planJ (gFamily (2 * h + 1 + 2)) (oddBase h hh) (oddQ h)
        (oddT h hh k) ∈ PlanFeasible (oddLaw h hh) k 1 η ∧
      planCost (gFamily (2 * h + 1 + 2)) k
          (CIGAMF.P13.PaperCBudgetExchange.planJ (gFamily (2 * h + 1 + 2)) (oddBase h hh)
            (oddQ h) (oddT h hh k)) = 0 := by
  obtain ⟨hJ, hc⟩ := CIGAMF.P13.PaperCBudgetExchange.sym_plan (gFamily (2 * h + 1 + 2))
    (oddBase h hh) (oddQ h) (oddQ_nonneg h) k 1 η (oddT h hh k)
    (fun x => oddT_card h hh k hk2 hkm x) (fun x => oddT_sdiff h hh k x)
    (fun i => (oddT_band h hh k hk2 hkm i).trans
      (div_le_div_of_nonneg_right hη (Nat.cast_nonneg _)))
  refine ⟨hJ, ?_⟩
  rw [hc]
  exact Finset.sum_eq_zero fun x _ => by rw [oddT_cost h hh k hk2 hkm x, mul_zero]

/-- **The end budgets `1` and `m-1`**: any subset law of the layer is reached by one exchange
from the committed law, with that law's cost. -/
theorem end_budget (hh : 1 ≤ h) (η : ℝ) (hη : 0 ≤ η) (k : Fin (2 * h + 1 + 2 + 1))
    (hk : k.val = 1 ∨ k.val = 2 * h + 2) (Q : Finset (Fin (2 * h + 1 + 2)) → ℝ)
    (hQ : Q ∈ SubFeasible k.val η) :
    indepPlan (oddLaw h hh) Q ∈ PlanFeasible (oddLaw h hh) k 1 η ∧
      planCost (gFamily (2 * h + 1 + 2)) k (indepPlan (oddLaw h hh) Q)
        = ∑ S, Q S * subCost (gFamily (2 * h + 1 + 2)) k S := by
  have hP := oddLaw_feasible h hh η hη
  exact ⟨indep_feasible _ η hP k 1 (by omega) Q hQ, indep_cost _ _ hP.2.1 k Q⟩

end Band

/-! ## 5. One exchange reaches `B` -/

/-- **One exchange suffices on `g_m`, odd `m ≥ 5`, at every band level**:
`V^{(1)}_{g_m}(η) = B_{g_m}(η)`. -/
theorem recourse_one_odd (m : ℕ) (hm : 5 ≤ m) (hodd : m % 2 = 1) (η : ℝ) (hη : 0 ≤ η) :
    recourseValue (gFamily m) η 1 (interiorK m) (interiorK_nonempty m (by omega))
      = awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega)) := by
  obtain ⟨h, rfl⟩ : ∃ h, m = 2 * h + 1 + 2 := ⟨(m - 3) / 2, by omega⟩
  have hh : 1 ≤ h := by omega
  haveI : NeZero (2 * h + 1 + 2) := ⟨by omega⟩
  by_cases hlow : η ≤ etaOne h
  · exact recourse_eq_aware_odd (2 * h + 1 + 2) (by omega) hodd η hη
      (hlow.trans (etaOne_le_etaT h)) 1
  push_neg at hlow
  refine le_antisymm ?_ (aware_le_recourse _ η hη 1 _ _)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hnear : ∀ k : Fin (2 * h + 1 + 2 + 1), ∃ Q ∈ SubFeasible (m := 2 * h + 1 + 2) k.val η,
      ∑ S, Q S * subCost (gFamily (2 * h + 1 + 2)) k S
        < layerValue (gFamily (2 * h + 1 + 2)) η k + ε := by
    intro k
    obtain ⟨_, ⟨Q, hQ, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt ((sub_nonempty η hη k).image _)
      (show layerValue (gFamily (2 * h + 1 + 2)) η k
          < layerValue (gFamily (2 * h + 1 + 2)) η k + ε by linarith)
    exact ⟨Q, hQ, hlt⟩
  choose Qf hQf hQc using hnear
  have hP := oddLaw_feasible h hh η hη
  let J : Fin (2 * h + 1 + 2 + 1) → Equiv.Perm (Fin (2 * h + 1 + 2))
      → Finset (Fin (2 * h + 1 + 2)) → ℝ :=
    fun k => if k.val = 1 ∨ k.val = 2 * h + 2 then indepPlan (oddLaw h hh) (Qf k)
      else CIGAMF.P13.PaperCBudgetExchange.planJ (gFamily (2 * h + 1 + 2)) (oddBase h hh)
        (oddQ h) (oddT h hh k)
  have hmem : (interiorK (2 * h + 1 + 2)).sup' (interiorK_nonempty (2 * h + 1 + 2) (by omega))
      (fun k => planCost (gFamily (2 * h + 1 + 2)) k (J k))
      ∈ recourseSet (gFamily (2 * h + 1 + 2)) η 1 (interiorK (2 * h + 1 + 2))
        (interiorK_nonempty (2 * h + 1 + 2) (by omega)) := by
    refine ⟨oddLaw h hh, hP, J, fun k hk => ?_, rfl⟩
    have hk' : 1 ≤ k.val ∧ k.val ≤ 2 * h + 1 + 2 - 1 := by simpa [interiorK] using hk
    by_cases hend : k.val = 1 ∨ k.val = 2 * h + 2
    · simp only [J, if_pos hend]
      exact (end_budget h hh η hη k hend (Qf k) (hQf k)).1
    · simp only [J, if_neg hend]
      exact (mid_spec h hh η hlow.le k (by omega) (by omega)).1
  refine lt_of_le_of_lt (csInf_le (recourse_bdd _ η 1 _ _) hmem) ?_
  rw [Finset.sup'_lt_iff]
  intro k hk
  have hk' : 1 ≤ k.val ∧ k.val ≤ 2 * h + 1 + 2 - 1 := by simpa [interiorK] using hk
  have hlay : layerValue (gFamily (2 * h + 1 + 2)) η k
      ≤ awareValue (gFamily (2 * h + 1 + 2)) η (interiorK (2 * h + 1 + 2))
        (interiorK_nonempty (2 * h + 1 + 2) (by omega)) :=
    Finset.le_sup' (fun k => layerValue (gFamily (2 * h + 1 + 2)) η k) hk
  by_cases hend : k.val = 1 ∨ k.val = 2 * h + 2
  · simp only [J, if_pos hend]
    rw [(end_budget h hh η hη k hend (Qf k) (hQf k)).2]
    linarith [hQc k]
  · simp only [J, if_neg hend]
    rw [(mid_spec h hh η hlow.le k (by omega) (by omega)).2]
    linarith [layer_nonneg (gFamily (2 * h + 1 + 2)) η k (sub_nonempty η hη k)]

/-- **`m = 3`**: both interior budgets are end budgets, so one exchange reaches `B`. -/
theorem recourse_one_three (η : ℝ) (hη : 0 ≤ η) :
    recourseValue (gFamily 3) η 1 (interiorK 3) (interiorK_nonempty 3 (by omega))
      = awareValue (gFamily 3) η (interiorK 3) (interiorK_nonempty 3 (by omega)) := by
  haveI : NeZero 3 := ⟨by norm_num⟩
  exact recourse_full _ η hη 1 _ _ (fun k hk => by
    have : 1 ≤ k.val ∧ k.val ≤ 3 - 1 := by simpa [interiorK] using hk
    omega)

/-- **Every odd `m ≥ 3`, every band level**: `V^{(1)}_{g_m}(η) = B_{g_m}(η)`. -/
theorem recourse_one_odd_all (m : ℕ) (hm : 3 ≤ m) (hodd : m % 2 = 1) (η : ℝ) (hη : 0 ≤ η) :
    recourseValue (gFamily m) η 1 (interiorK m) (interiorK_nonempty m (by omega))
      = awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega)) := by
  rcases Nat.lt_or_ge m 5 with h5 | h5
  · obtain rfl : m = 3 := by omega
    exact recourse_one_three η hη
  · exact recourse_one_odd m h5 hodd η hη

/-- **The hypotheses are satisfiable, on the plan branch**: at `m = 5` (`h = 1`) and `η = 1`,
`etaOne 1 = 3/4 < 1`, and the conclusion holds. -/
theorem recourse_one_odd_satisfiable :
    ∃ η : ℝ, 0 ≤ η ∧ etaOne 1 < η ∧
      recourseValue (gFamily 5) η 1 (interiorK 5) (interiorK_nonempty 5 (by norm_num))
        = awareValue (gFamily 5) η (interiorK 5) (interiorK_nonempty 5 (by norm_num)) := by
  refine ⟨1, zero_le_one, ?_, recourse_one_odd 5 le_rfl rfl 1 zero_le_one⟩
  unfold etaOne
  norm_num

#print axioms etaOne_le_etaT
#print axioms corr_split
#print axioms sigma_corr
#print axioms sigma_bound
#print axioms oddT_band
#print axioms mid_spec
#print axioms end_budget
#print axioms recourse_one_odd
#print axioms recourse_one_three
#print axioms recourse_one_odd_all
#print axioms recourse_one_odd_satisfiable

end CIGAMF.P13.PaperCBudgetExchangeOddV2
