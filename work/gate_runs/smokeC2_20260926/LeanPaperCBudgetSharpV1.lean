import «LeanPaperCBudgetSymV1»

/-!
# Paper C: the exact budget-aware value of `g_m`, and sharpness of the zero-value ranges

`g_m = (-3, -1 × p, +1 × q, +3)`, `D = m + 4`, interior budgets `1, …, m-1`.

* `aware_even_exact`: for even `m ≥ 4` and every `η ≥ 0`,
  `B_{g_m}(η) = 4 max(1-η, 0)/(mD)`.
* `aware_odd_exact`: for odd `m ≥ 3` and every `η ≥ 0`,
  `B_{g_m}(η) = max(m+3-(m+1)η, m+1-(m-1)η, 0)/(mD)`.
* `advantage_even`, `advantage_even_pos_iff`: `A = U - B` in closed form, and `A > 0` exactly
  when `η > (m-2)/(2(m-1))`.
* `advantage_odd_pos_iff`: `A > 0` exactly when `η > 1 - 2/(m(m-1))`.
  So both ranges of `aware_even`/`aware_odd` (`LeanPaperCBudgetGmV1`) are sharp, and past them
  knowing the budget helps at EVERY band level.
* `recourse_eq_aware_even`, `recourse_eq_aware_odd`: on those ranges `V^{(R)} = B` for every
  `R` (in particular one exchange reaches `B`), since `B = U` there.

Upper bounds come from explicit subset laws (`LeanPaperCBudgetSymV1`): drop vectors at the budgets
`1` and `m-1`, and symmetrised count-vector mixtures at the middle budgets (cost `0` except at
even middle budgets of odd `m`, where a mixture of a cost-`k/(mD)` law at `η = 0` and a cost-`0`
law at `η = 1` is used). Lower bounds are linear certificates (`layer_ge_of_linear`).
-/

namespace CIGAMF.P13.PaperCBudgetSharp

open Finset
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCFrontier CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCBudgetAware CIGAMF.P13.PaperCFamily CIGAMF.P13.PaperCStabilityFamily
open CIGAMF.P13.PaperCEndgame CIGAMF.P13.PaperCEndpointLaw CIGAMF.P13.PaperCOddFrontier
open CIGAMF.P13.PaperCRelaxedJoin CIGAMF.P13.PaperCBudgetSym

/-! ## 0. Helpers -/

theorem band_of_eq {x t η M : ℝ} (hM : 0 < M) (hη : 0 ≤ η) (h : x = t) : |x - t| ≤ η / M := by
  rw [h, sub_self, abs_zero]; positivity

theorem band_of_diff {x t δ η M : ℝ} (hM : 0 < M) (hd : x - t = δ) (hδ : |δ| * M ≤ η) :
    |x - t| ≤ η / M := by
  rw [hd, le_div_iff₀ hM]; exact hδ

theorem sum_fn_even (h : ℕ) (hh : 1 ≤ h) (f : ℝ → ℝ) :
    ∑ i, f (gFamily (2 * h + 2) i) = f (-3) + f 3 + (h : ℝ) * f (-1) + (h : ℝ) * f 1 := by
  have := sum_fn_gFamily (2 * h) (by omega) f
  rw [this, show (2 * h + 1) / 2 = h by omega, show 2 * h - h = h by omega]

theorem sum_fn_odd (h : ℕ) (f : ℝ → ℝ) :
    ∑ i, f (gFamily (2 * h + 1 + 2) i)
      = f (-3) + f 3 + ((h : ℝ) + 1) * f (-1) + (h : ℝ) * f 1 := by
  have := sum_fn_gFamily (2 * h + 1) (by omega) f
  rw [this, show (2 * h + 1 + 1) / 2 = h + 1 by omega, show 2 * h + 1 - (h + 1) = h by omega]
  push_cast; ring

theorem normMass_g (n : ℕ) (hn : 1 ≤ n) : normMass (gFamily (n + 2)) = (n : ℝ) + 6 := by
  rw [CIGAMF.P13.PaperCBaselineAttain.normMass_gFamily (n + 2) (by omega)]; push_cast; ring

theorem sum_compl_one {m : ℕ} (g : Fin m → ℝ) (j : Fin m) :
    ∑ i ∈ ({j} : Finset (Fin m))ᶜ, g i = (∑ i, g i) - g j := by
  have := Finset.sum_add_sum_compl ({j} : Finset (Fin m)) g
  rw [Finset.sum_singleton] at this; linarith

theorem subCost_single (n : ℕ) (hn : 1 ≤ n) (j : Fin (n + 2)) :
    subCost (gFamily (n + 2)) ⟨1, by omega⟩ {j}
      = (|gFamily (n + 2) j| - 1) / ((n : ℝ) + 6) := by
  unfold subCost
  rw [Finset.sum_singleton, normMass_g n hn,
    CIGAMF.P13.PaperCBaselineAttain.familyBaselineIdentification_holds (n + 2) (by omega)
      ⟨1, by omega⟩ (show 1 ≤ 1 from le_refl 1) (show 1 < n + 2 by omega)]
  norm_num

/-- The dropped-item cost at budget `m-1`, as a function of the dropped weight. -/
noncomputable def subC (n : ℕ) (x : ℝ) : ℝ :=
  (|(∑ i, gFamily (n + 2) i) - x| - (((n + 1) % 2 : ℕ) : ℝ)) / ((n : ℝ) + 6)

theorem subCost_compl (n : ℕ) (hn : 1 ≤ n) (j : Fin (n + 2)) :
    subCost (gFamily (n + 2)) ⟨n + 1, by omega⟩ {j}ᶜ = subC n (gFamily (n + 2) j) := by
  unfold subCost subC
  rw [sum_compl_one, normMass_g n hn,
    CIGAMF.P13.PaperCBaselineAttain.familyBaselineIdentification_holds (n + 2) (by omega)
      ⟨n + 1, by omega⟩ (show 1 ≤ n + 1 by omega) (show n + 1 < n + 2 by omega)]

theorem total_even (h : ℕ) (hh : 1 ≤ h) : ∑ i, gFamily (2 * h + 2) i = 0 := by
  have := sum_fn_even h hh (fun x => x); rw [this]; ring

theorem total_odd (h : ℕ) : ∑ i, gFamily (2 * h + 1 + 2) i = -1 := by
  have := sum_fn_odd h (fun x => x); rw [this]; ring

/-! ## 1. Drop vectors at the budgets `1` and `m-1` -/

/-- Relative deviations of the drop vector on the four weight classes. -/
noncomputable def dev4 (e3n e1n e1p e3p x : ℝ) : ℝ :=
  if x = -3 then e3n else if x = -1 then e1n else if x = 1 then e1p else e3p

theorem dev4_m3 (e3n e1n e1p e3p : ℝ) : dev4 e3n e1n e1p e3p (-3) = e3n := by simp [dev4]
theorem dev4_m1 (e3n e1n e1p e3p : ℝ) : dev4 e3n e1n e1p e3p (-1) = e1n := by norm_num [dev4]
theorem dev4_p1 (e3n e1n e1p e3p : ℝ) : dev4 e3n e1n e1p e3p 1 = e1p := by norm_num [dev4]
theorem dev4_p3 (e3n e1n e1p e3p : ℝ) : dev4 e3n e1n e1p e3p 3 = e3p := by norm_num [dev4]

/-- The worst-budget cost of the drop vector with deviations `e`. -/
noncomputable def dropC (n : ℕ) (e3n e1n e1p e3p : ℝ) : ℝ :=
  ((1 + e3n) * subC n (-3) + (1 + e3p) * subC n 3
    + (((n + 1) / 2 : ℕ) : ℝ) * ((1 + e1n) * subC n (-1))
    + ((n - (n + 1) / 2 : ℕ) : ℝ) * ((1 + e1p) * subC n 1)) / ((n : ℝ) + 2)

/-- **The drop vector `π_i = (1 + e_{g_i})/m` bounds the budgets `1` and `m-1`.** -/
theorem drop4 (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (e3n e1n e1p e3p : ℝ)
    (hle : ∀ j : Fin (n + 2), subCost (gFamily (n + 2)) ⟨1, by omega⟩ {j}
      ≤ subCost (gFamily (n + 2)) ⟨n + 1, by omega⟩ {j}ᶜ)
    (n3n : 0 ≤ 1 + e3n) (n1n : 0 ≤ 1 + e1n) (n1p : 0 ≤ 1 + e1p) (n3p : 0 ≤ 1 + e3p)
    (b3n : |e3n| ≤ η) (b1n : |e1n| ≤ η) (b1p : |e1p| ≤ η) (b3p : |e3p| ≤ η)
    (hsum : e3n + e3p + (((n + 1) / 2 : ℕ) : ℝ) * e1n + ((n - (n + 1) / 2 : ℕ) : ℝ) * e1p = 0) :
    layerValue (gFamily (n + 2)) η ⟨1, by omega⟩ ≤ dropC n e3n e1n e1p e3p ∧
      layerValue (gFamily (n + 2)) η ⟨n + 1, by omega⟩ ≤ dropC n e3n e1n e1p e3p := by
  set g := gFamily (n + 2) with hg
  set u : ℝ → ℝ := fun x => (1 + dev4 e3n e1n e1p e3p x) / ((n : ℝ) + 2) with hu
  have hM : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  have h0 : ∀ i, 0 ≤ u (g i) := by
    intro i
    rcases gFamily_weights (n + 2) i with h | h | h | h <;> rw [hg, h] <;>
      simp only [hu, dev4_m3, dev4_m1, dev4_p1, dev4_p3] <;> positivity
  have hpq : (((n + 1) / 2 : ℕ) : ℝ) + ((n - (n + 1) / 2 : ℕ) : ℝ) = n := by
    rw [← Nat.cast_add, show (n + 1) / 2 + (n - (n + 1) / 2) = n by omega]
  have h1 : ∑ i, u (g i) = 1 := by
    rw [hg, sum_fn_gFamily n hn u]
    simp only [hu, dev4_m3, dev4_m1, dev4_p1, dev4_p3]
    field_simp
    linear_combination hsum + hpq
  have hb : ∀ i, |u (g i) - 1 / ((n + 2 : ℕ) : ℝ)| ≤ η / ((n + 2 : ℕ) : ℝ) := by
    intro i
    rw [hcast]
    have key : ∀ e : ℝ, |e| ≤ η → |(1 + e) / ((n : ℝ) + 2) - 1 / ((n : ℝ) + 2)| ≤ η / ((n : ℝ) + 2) := by
      intro e he
      rw [← sub_div, add_sub_cancel_left, abs_div, abs_of_pos hM]
      exact div_le_div_of_nonneg_right he hM.le
    rcases gFamily_weights (n + 2) i with h | h | h | h <;> rw [hg, h] <;>
      simp only [hu, dev4_m3, dev4_m1, dev4_p1, dev4_p3]
    · exact key _ b3n
    · exact key _ b1n
    · exact key _ b1p
    · exact key _ b3p
  have hC : ∑ j, u (g j) * subCost g ⟨n + 1, by omega⟩ {j}ᶜ = dropC n e3n e1n e1p e3p := by
    rw [Finset.sum_congr rfl fun j _ => by rw [hg, subCost_compl n hn j]]
    rw [sum_fn_gFamily n hn (fun x => u x * subC n x)]
    simp only [hu, dev4_m3, dev4_m1, dev4_p1, dev4_p3, dropC]
    ring
  have hle' : ∀ j : Fin (n + 2), subCost g ⟨1, by omega⟩ {j}
      ≤ subCost g ⟨n + 1, by omega⟩ {j}ᶜ := hle
  constructor
  · refine (layer_le_drop1 g η (by omega) _ h0 h1 hb).trans ?_
    rw [← hC]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hle' j) (h0 j)
  · have := layer_le_dropc g η (by omega) _ h0 h1 hb
    have e : (⟨n + 2 - 1, by omega⟩ : Fin (n + 2 + 1)) = ⟨n + 1, by omega⟩ := Fin.ext (by simp)
    rw [e, hC] at this
    exact this

/-! ## 2. Even `m`: the layers -/

/-- **Even `m`, budgets `1` and `m-1`.** -/
theorem even_drop (h : ℕ) (hh : 1 ≤ h) (η : ℝ) (hη : 0 ≤ η) :
    layerValue (gFamily (2 * h + 2)) η ⟨1, by omega⟩
        ≤ 4 * max (1 - η) 0 / ((2 * (h : ℝ) + 2) * (2 * (h : ℝ) + 2 + 4)) ∧
      layerValue (gFamily (2 * h + 2)) η ⟨2 * h + 1, by omega⟩
        ≤ 4 * max (1 - η) 0 / ((2 * (h : ℝ) + 2) * (2 * (h : ℝ) + 2 + 4)) := by
  set M := max (1 - η) 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM1 : 1 - η ≤ M := le_max_left _ _
  have hM2 : M ≤ 1 := max_le (by linarith) (by norm_num)
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hle : ∀ j : Fin (2 * h + 2), subCost (gFamily (2 * h + 2)) ⟨1, by omega⟩ {j}
      ≤ subCost (gFamily (2 * h + 2)) ⟨2 * h + 1, by omega⟩ {j}ᶜ := by
    intro j
    rw [subCost_single (2 * h) (by omega) j, subCost_compl (2 * h) (by omega) j]
    unfold subC
    rw [total_even h hh, show (2 * h + 1) % 2 = 1 by omega]
    simp
  have hp : (((2 * h + 1) / 2 : ℕ) : ℝ) = h := by rw [show (2 * h + 1) / 2 = h by omega]
  have hq : ((2 * h - (2 * h + 1) / 2 : ℕ) : ℝ) = h := by
    rw [show 2 * h - (2 * h + 1) / 2 = h by omega]
  have hd := drop4 (2 * h) (by omega) η (M - 1) ((1 - M) / h) ((1 - M) / h) (M - 1) hle
    (by linarith) (by have : 0 ≤ (1 - M) / h := div_nonneg (by linarith) (by linarith); linarith)
    (by have : 0 ≤ (1 - M) / h := div_nonneg (by linarith) (by linarith); linarith)
    (by linarith)
    (by rw [abs_le]; constructor <;> linarith)
    (by rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith)), div_le_iff₀ (by linarith)]
        nlinarith)
    (by rw [abs_of_nonneg (div_nonneg (by linarith) (by linarith)), div_le_iff₀ (by linarith)]
        nlinarith)
    (by rw [abs_le]; constructor <;> linarith)
    (by rw [hp, hq]; field_simp; ring)
  have hC : dropC (2 * h) (M - 1) ((1 - M) / h) ((1 - M) / h) (M - 1)
      = 4 * M / ((2 * (h : ℝ) + 2) * (2 * (h : ℝ) + 2 + 4)) := by
    unfold dropC subC
    rw [total_even h hh, show (2 * h + 1) % 2 = 1 by omega, hp, hq]
    push_cast
    norm_num
    field_simp
    ring
  rw [hC] at hd
  exact hd

/-- **Even `m`, even middle budgets `k = 2j+2 ≤ m-2`: cost `0`.** -/
theorem even_mid_even (h j : ℕ) (hh : 1 ≤ h) (hj : j + 1 ≤ h) (η : ℝ) (hη : 0 ≤ η)
    (k : Fin (2 * h + 2 + 1)) (hk : k.val = 2 * j + 2) :
    layerValue (gFamily (2 * h + 2)) η k ≤ 0 := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hjR : (j : ℝ) + 1 ≤ h := by exact_mod_cast hj
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 * (j : ℝ) + 2) / (2 * (h : ℝ) + 2) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hK1 : K ≤ 1 := by rw [hK, div_le_one (by positivity)]; linarith
  have hM : (0 : ℝ) < ((2 * h : ℕ) : ℝ) + 2 := by positivity
  obtain ⟨Q, hQ, hc⟩ := exists_counts_law (2 * h) (by omega) η k (by omega) (by omega)
    (r := 2) ![1, 0] ![j, j + 1] ![j, j + 1] ![1, 0] ![K, 1 - K]
    (fun x => by fin_cases x <;> simp) (fun x => by fin_cases x <;> simp <;> omega)
    (fun x => by fin_cases x <;> simp <;> omega) (fun x => by fin_cases x <;> simp)
    (fun x => by fin_cases x <;> simp [hk] <;> omega)
    (fun x => by fin_cases x <;> simp <;> linarith) (by simp [Fin.sum_univ_succ])
    (band_of_eq hM hη (by rw [hk, hK]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by rw [hk, hK]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by
      rw [hk, hK, show (2 * h + 1) / 2 = h by omega]
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by
      rw [hk, hK, show (2 * h + 1) / 2 = h by omega, show 2 * h - h = h by omega]
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
  refine (layer_le _ η k Q hQ).trans (le_of_eq ?_)
  rw [hc, hk, show (2 * j + 2) % 2 = 0 by omega]
  simp [Fin.sum_univ_succ]

/-- **Even `m`, odd middle budgets `k = 2j+3 ≤ m-3`: cost `0`.** -/
theorem even_mid_odd (h j : ℕ) (hh : 1 ≤ h) (hj : j + 2 ≤ h) (η : ℝ) (hη : 0 ≤ η)
    (k : Fin (2 * h + 2 + 1)) (hk : k.val = 2 * j + 3) :
    layerValue (gFamily (2 * h + 2)) η k ≤ 0 := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hjR : (j : ℝ) + 2 ≤ h := by exact_mod_cast hj
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 * (j : ℝ) + 3) / (2 * (h : ℝ) + 2) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hK1 : K ≤ 1 := by rw [hK, div_le_one (by positivity)]; linarith
  have hM : (0 : ℝ) < ((2 * h : ℕ) : ℝ) + 2 := by positivity
  obtain ⟨Q, hQ, hc⟩ := exists_counts_law (2 * h) (by omega) η k (by omega) (by omega)
    (r := 4) ![1, 1, 0, 0] ![j, j + 1, j + 1, j + 2] ![j + 1, j, j + 2, j + 1] ![1, 1, 0, 0]
    ![K / 2, K / 2, (1 - K) / 2, (1 - K) / 2]
    (fun x => by fin_cases x <;> simp) (fun x => by fin_cases x <;> simp <;> omega)
    (fun x => by fin_cases x <;> simp <;> omega) (fun x => by fin_cases x <;> simp)
    (fun x => by fin_cases x <;> simp [hk] <;> omega)
    (fun x => by fin_cases x <;> simp <;> linarith) (by simp [Fin.sum_univ_succ]; ring)
    (band_of_eq hM hη (by rw [hk, hK]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by rw [hk, hK]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by
      rw [hk, hK, show (2 * h + 1) / 2 = h by omega]
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by
      rw [hk, hK, show (2 * h + 1) / 2 = h by omega, show 2 * h - h = h by omega]
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
  refine (layer_le _ η k Q hQ).trans (le_of_eq ?_)
  rw [hc, hk, show (2 * j + 3) % 2 = 1 by omega]
  simp [Fin.sum_univ_succ] <;> ring_nf <;> (try simp) <;> (try ring)

/-! ## 3. Odd `m`: the layers -/

/-- **Odd `m`, budgets `1` and `m-1`**, in three band regimes. -/
theorem odd_drop (h : ℕ) (η : ℝ) (hη : 0 ≤ η) :
    layerValue (gFamily (2 * h + 1 + 2)) η ⟨1, by omega⟩
        ≤ max (2 * (h : ℝ) + 6 - (2 * (h : ℝ) + 4) * η)
            (max (2 * (h : ℝ) + 4 - (2 * (h : ℝ) + 2) * η) 0)
          / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) ∧
      layerValue (gFamily (2 * h + 1 + 2)) η ⟨2 * h + 1 + 1, by omega⟩
        ≤ max (2 * (h : ℝ) + 6 - (2 * (h : ℝ) + 4) * η)
            (max (2 * (h : ℝ) + 4 - (2 * (h : ℝ) + 2) * η) 0)
          / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) := by
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hle : ∀ j : Fin (2 * h + 1 + 2), subCost (gFamily (2 * h + 1 + 2)) ⟨1, by omega⟩ {j}
      ≤ subCost (gFamily (2 * h + 1 + 2)) ⟨2 * h + 1 + 1, by omega⟩ {j}ᶜ := by
    intro j
    rw [subCost_single (2 * h + 1) (by omega) j, subCost_compl (2 * h + 1) (by omega) j]
    unfold subC
    rw [total_odd h, show (2 * h + 1 + 1) % 2 = 0 by omega]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rcases gFamily_weights (2 * h + 1 + 2) j with hw | hw | hw | hw <;> rw [hw] <;> norm_num
  have hp : (((2 * h + 1 + 1) / 2 : ℕ) : ℝ) = (h : ℝ) + 1 := by
    rw [show (2 * h + 1 + 1) / 2 = h + 1 by omega]; push_cast; ring
  have hq : ((2 * h + 1 - (2 * h + 1 + 1) / 2 : ℕ) : ℝ) = h := by
    rw [show 2 * h + 1 - (2 * h + 1 + 1) / 2 = h by omega]
  have hsubC : ∀ x, subC (2 * h + 1) x = |-1 - x| / (2 * (h : ℝ) + 7) := by
    intro x; unfold subC; rw [total_odd h, show (2 * h + 1 + 1) % 2 = 0 by omega]
    push_cast; ring_nf
  have hD : (0 : ℝ) < (2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7) := by positivity
  set T := max (2 * (h : ℝ) + 6 - (2 * (h : ℝ) + 4) * η)
      (max (2 * (h : ℝ) + 4 - (2 * (h : ℝ) + 2) * η) 0) with hT
  rcases le_total η 1 with h1 | h1
  · -- regime A
    have hr : 0 ≤ (h : ℝ) * η / ((h : ℝ) + 1) ∧ (h : ℝ) * η / ((h : ℝ) + 1) ≤ η := by
      constructor
      · positivity
      · rw [div_le_iff₀ (by positivity)]; nlinarith
    have hd := drop4 (2 * h + 1) (by omega) η (-(h * η / (h + 1))) η (-(h * η / (h + 1))) (-η)
      hle (by nlinarith) (by linarith) (by nlinarith) (by linarith)
      (by rw [abs_neg, abs_of_nonneg hr.1]; exact hr.2) (by rw [abs_of_nonneg hη])
      (by rw [abs_neg, abs_of_nonneg hr.1]; exact hr.2) (by rw [abs_neg, abs_of_nonneg hη])
      (by rw [hp, hq]; field_simp; ring)
    have hC : dropC (2 * h + 1) (-(h * η / (h + 1))) η (-(h * η / (h + 1))) (-η)
        = (2 * (h : ℝ) + 6 - (2 * (h : ℝ) + 4) * η) / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) := by
      unfold dropC
      rw [hsubC, hsubC, hsubC, hsubC, hp, hq]
      push_cast; norm_num
      field_simp; ring
    rw [hC] at hd
    have : (2 * (h : ℝ) + 6 - (2 * (h : ℝ) + 4) * η) / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7))
        ≤ T / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) :=
      div_le_div_of_nonneg_right (le_max_left _ _) hD.le
    exact ⟨hd.1.trans this, hd.2.trans this⟩
  · rcases le_total η ((h + 2) / (h + 1)) with h2 | h2
    · -- regime B
      have hr : 1 / ((h : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have hr2 : ((h : ℝ) + 1) * η ≤ h + 2 := by
        rw [le_div_iff₀ (by positivity)] at h2; linarith
      have hnnB : (0 : ℝ) ≤ 1 + (1 / ((h : ℝ) + 1) - η) := by
        rw [show (1 : ℝ) + (1 / ((h : ℝ) + 1) - η) = ((h : ℝ) + 2 - ((h : ℝ) + 1) * η) / ((h : ℝ) + 1)
          by field_simp; ring]
        exact div_nonneg (by linarith) (by positivity)
      have hd := drop4 (2 * h + 1) (by omega) η (1 / (h + 1) - η) η (1 / (h + 1) - η) (-1)
        hle hnnB (by linarith) hnnB
        (by norm_num)
        (by rw [abs_le]; constructor <;> nlinarith [div_nonneg zero_le_one (by positivity : (0:ℝ) ≤ h + 1)])
        (by rw [abs_of_nonneg hη])
        (by rw [abs_le]; constructor <;> nlinarith [div_nonneg zero_le_one (by positivity : (0:ℝ) ≤ h + 1)])
        (by rw [abs_neg, abs_one]; exact h1)
        (by rw [hp, hq]; field_simp; ring)
      have hC : dropC (2 * h + 1) (1 / (h + 1) - η) η (1 / (h + 1) - η) (-1)
          = (2 * (h : ℝ) + 4 - (2 * (h : ℝ) + 2) * η)
            / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) := by
        unfold dropC
        rw [hsubC, hsubC, hsubC, hsubC, hp, hq]
        push_cast; norm_num
        field_simp; ring
      rw [hC] at hd
      have : (2 * (h : ℝ) + 4 - (2 * (h : ℝ) + 2) * η) / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7))
          ≤ T / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) :=
        div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hD.le
      exact ⟨hd.1.trans this, hd.2.trans this⟩
    · -- regime C
      have hd := drop4 (2 * h + 1) (by omega) η (-1) ((h + 2) / (h + 1)) (-1) (-1)
        hle (by norm_num) (by positivity) (by norm_num) (by norm_num)
        (by rw [abs_neg, abs_one]; exact h1)
        (by rw [abs_of_nonneg (by positivity)]; exact h2)
        (by rw [abs_neg, abs_one]; exact h1) (by rw [abs_neg, abs_one]; exact h1)
        (by rw [hp, hq]; field_simp; ring)
      have hC : dropC (2 * h + 1) (-1) ((h + 2) / (h + 1)) (-1) (-1) = 0 := by
        unfold dropC
        rw [hsubC, hsubC, hsubC, hsubC]
        norm_num
      rw [hC] at hd
      have : (0 : ℝ) ≤ T / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) :=
        div_nonneg ((le_max_right _ _).trans (le_max_right _ _)) hD.le
      exact ⟨hd.1.trans this, hd.2.trans this⟩

/-- **Odd `m`, odd middle budgets `k = 2j+3 ≤ m-4`: cost `0`.** -/
theorem odd_mid_odd_a (h j : ℕ) (hj : j + 2 ≤ h) (η : ℝ) (hη : 0 ≤ η)
    (k : Fin (2 * h + 1 + 2 + 1)) (hk : k.val = 2 * j + 3) :
    layerValue (gFamily (2 * h + 1 + 2)) η k ≤ 0 := by
  have hjR : (j : ℝ) + 2 ≤ h := by exact_mod_cast hj
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 * (j : ℝ) + 3) / (2 * (h : ℝ) + 3) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hK1 : K ≤ 1 := by rw [hK, div_le_one (by positivity)]; linarith
  have hM : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) + 2 := by positivity
  obtain ⟨Q, hQ, hc⟩ := exists_counts_law (2 * h + 1) (by omega) η k (by omega) (by omega)
    (r := 3) ![1, 0, 0] ![j + 1, j + 2, j + 1] ![j, j + 1, j + 2] ![1, 0, 0]
    ![K, (1 - K) / 2, (1 - K) / 2]
    (fun x => by fin_cases x <;> simp) (fun x => by fin_cases x <;> simp <;> omega)
    (fun x => by fin_cases x <;> simp <;> omega) (fun x => by fin_cases x <;> simp)
    (fun x => by fin_cases x <;> simp [hk] <;> omega)
    (fun x => by fin_cases x <;> simp <;> linarith) (by simp [Fin.sum_univ_succ] <;> ring)
    (band_of_eq hM hη (by rw [hk, hK]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by rw [hk, hK]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by
      rw [hk, hK, show (2 * h + 1 + 1) / 2 = h + 1 by omega]
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by
      rw [hk, hK, show (2 * h + 1 + 1) / 2 = h + 1 by omega,
        show 2 * h + 1 - (h + 1) = h by omega]
      have : (h : ℝ) ≠ 0 := by linarith
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
  refine (layer_le _ η k Q hQ).trans (le_of_eq ?_)
  rw [hc, hk, show (2 * j + 3) % 2 = 1 by omega]
  simp [Fin.sum_univ_succ] <;> ring_nf <;> (try simp) <;> (try ring)

/-- **Odd `m`, the odd middle budget `k = m-2`: cost `0`.** -/
theorem odd_mid_odd_b (h j : ℕ) (hj : j + 1 = h) (η : ℝ) (hη : 0 ≤ η)
    (k : Fin (2 * h + 1 + 2 + 1)) (hk : k.val = 2 * j + 3) :
    layerValue (gFamily (2 * h + 1 + 2)) η k ≤ 0 := by
  subst hj
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 * (j : ℝ) + 3) / (2 * (j : ℝ) + 5) := ⟨_, rfl⟩
  have hK0 : 0 ≤ 3 * K - 1 := by
    rw [hK, mul_div_assoc', div_sub_one (by positivity)]; apply div_nonneg <;> linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hK1 : K ≤ 1 := by rw [hK, div_le_one (by positivity)]; linarith
  have hM : (0 : ℝ) < ((2 * (j + 1) + 1 : ℕ) : ℝ) + 2 := by positivity
  obtain ⟨Q, hQ, hc⟩ := exists_counts_law (2 * (j + 1) + 1) (by omega) η k (by omega) (by omega)
    (r := 3) ![1, 1, 0] ![j + 1, j, j + 2] ![j, j + 1, j + 1] ![1, 1, 0]
    ![(3 * K - 1) / 2, (1 - K) / 2, 1 - K]
    (fun x => by fin_cases x <;> simp) (fun x => by fin_cases x <;> simp <;> omega)
    (fun x => by fin_cases x <;> simp <;> omega) (fun x => by fin_cases x <;> simp)
    (fun x => by fin_cases x <;> simp [hk] <;> omega)
    (fun x => by fin_cases x <;> simp <;> linarith) (by simp [Fin.sum_univ_succ]; ring)
    (band_of_eq hM hη (by rw [hk, hK]; push_cast; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by rw [hk, hK]; push_cast; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by
      rw [hk, hK, show (2 * (j + 1) + 1 + 1) / 2 = j + 2 by omega]
      push_cast; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM hη (by
      rw [hk, hK, show (2 * (j + 1) + 1 + 1) / 2 = j + 2 by omega,
        show 2 * (j + 1) + 1 - (j + 2) = j + 1 by omega]
      push_cast; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
  refine (layer_le _ η k Q hQ).trans (le_of_eq ?_)
  rw [hc, hk, show (2 * j + 3) % 2 = 1 by omega]
  simp [Fin.sum_univ_succ] <;> ring_nf <;> (try simp) <;> (try ring)

/-- Odd `m`, even middle budget `k = 2j+2`: a cost-`0` law at band `1`. -/
theorem odd_L1 (h j : ℕ) (hh : 1 ≤ h) (hj : j + 1 ≤ h)
    (k : Fin (2 * h + 1 + 2 + 1)) (hk : k.val = 2 * j + 2) :
    ∃ Q ∈ SubFeasible (m := 2 * h + 1 + 2) k.val 1,
      ∑ S, Q S * subCost (gFamily (2 * h + 1 + 2)) k S = 0 := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hjR : (j : ℝ) + 1 ≤ h := by exact_mod_cast hj
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (2 * (j : ℝ) + 2) / (2 * (h : ℝ) + 3) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hK1 : K ≤ 1 := by rw [hK, div_le_one (by positivity)]; linarith
  have hM : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) + 2 := by positivity
  obtain ⟨Q, hQ, hc⟩ := exists_counts_law (2 * h + 1) (by omega) 1 k (by omega) (by omega)
    (r := 2) ![0, 1] ![j + 1, j] ![j + 1, j] ![0, 1] ![1 - K, K]
    (fun x => by fin_cases x <;> simp) (fun x => by fin_cases x <;> simp <;> omega)
    (fun x => by fin_cases x <;> simp <;> omega) (fun x => by fin_cases x <;> simp)
    (fun x => by fin_cases x <;> simp [hk] <;> omega)
    (fun x => by fin_cases x <;> simp <;> linarith) (by simp [Fin.sum_univ_succ])
    (band_of_eq hM zero_le_one (by rw [hk, hK]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM zero_le_one (by rw [hk, hK]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_diff hM (δ := -(((j : ℝ) + 1) / ((2 * (h : ℝ) + 3) * ((h : ℝ) + 1)))) (by
      rw [hk, hK, show (2 * h + 1 + 1) / 2 = h + 1 by omega]
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring) (by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      push_cast
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      nlinarith))
    (band_of_diff hM (δ := ((j : ℝ) + 1) / ((2 * (h : ℝ) + 3) * (h : ℝ))) (by
      rw [hk, hK, show (2 * h + 1 + 1) / 2 = h + 1 by omega,
        show 2 * h + 1 - (h + 1) = h by omega]
      have : (h : ℝ) ≠ 0 := by linarith
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring) (by
      rw [abs_of_nonneg (by positivity)]
      push_cast
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      nlinarith))
  refine ⟨Q, hQ, ?_⟩
  rw [hc, hk, show (2 * j + 2) % 2 = 0 by omega]
  simp [Fin.sum_univ_succ]

/-- Odd `m`, the even middle budget `k = 2`: an exact-marginal law of cost `2/(mD)`. -/
theorem odd_L0_two (h : ℕ) (hh : 1 ≤ h) (k : Fin (2 * h + 1 + 2 + 1)) (hk : k.val = 2) :
    ∃ Q ∈ SubFeasible (m := 2 * h + 1 + 2) k.val 0,
      ∑ S, Q S * subCost (gFamily (2 * h + 1 + 2)) k S
        = 2 / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hM : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) + 2 := by positivity
  obtain ⟨Q, hQ, hc⟩ := exists_counts_law (2 * h + 1) (by omega) 0 k (by omega) (by omega)
    (r := 3) ![0, 1, 0] ![1, 0, 2] ![1, 0, 0] ![0, 1, 0]
    ![2 * (h : ℝ) / (2 * h + 3), 2 / (2 * h + 3), 1 / (2 * h + 3)]
    (fun x => by fin_cases x <;> simp) (fun x => by fin_cases x <;> simp <;> omega)
    (fun x => by fin_cases x <;> simp <;> omega) (fun x => by fin_cases x <;> simp)
    (fun x => by fin_cases x <;> simp [hk])
    (fun x => by fin_cases x <;> simp <;> positivity)
    (by simp [Fin.sum_univ_succ]; field_simp; ring)
    (band_of_eq hM le_rfl (by rw [hk]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM le_rfl (by rw [hk]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM le_rfl (by
      rw [hk, show (2 * h + 1 + 1) / 2 = h + 1 by omega]
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM le_rfl (by
      rw [hk, show (2 * h + 1 + 1) / 2 = h + 1 by omega,
        show 2 * h + 1 - (h + 1) = h by omega]
      have : (h : ℝ) ≠ 0 := by linarith
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
  refine ⟨Q, hQ, ?_⟩
  rw [hc, hk]
  simp [Fin.sum_univ_succ]
  norm_num
  field_simp
  ring

/-- Odd `m`, the even middle budget `k = 2i+4`: an exact-marginal law of cost `k/(mD)`. -/
theorem odd_L0_big (h i : ℕ) (hi : i + 2 ≤ h) (k : Fin (2 * h + 1 + 2 + 1))
    (hk : k.val = 2 * i + 4) :
    ∃ Q ∈ SubFeasible (m := 2 * h + 1 + 2) k.val 0,
      ∑ S, Q S * subCost (gFamily (2 * h + 1 + 2)) k S
        = (2 * (i : ℝ) + 4) / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) := by
  have hiR : (i : ℝ) + 2 ≤ h := by exact_mod_cast hi
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = ((i : ℝ) + 2) / (2 * (h : ℝ) + 3) := ⟨_, rfl⟩
  have hJ0 : 0 ≤ J := by rw [hJ]; positivity
  have hJ1 : 2 * J ≤ 1 := by rw [hJ, mul_div_assoc', div_le_one (by positivity)]; linarith
  have hM : (0 : ℝ) < ((2 * h + 1 : ℕ) : ℝ) + 2 := by positivity
  obtain ⟨Q, hQ, hc⟩ := exists_counts_law (2 * h + 1) (by omega) 0 k (by omega) (by omega)
    (r := 3) ![0, 1, 1] ![i + 2, i + 1, i + 2] ![i + 2, i + 1, i] ![0, 1, 1]
    ![1 - 2 * J, J, J]
    (fun x => by fin_cases x <;> simp) (fun x => by fin_cases x <;> simp <;> omega)
    (fun x => by fin_cases x <;> simp <;> omega) (fun x => by fin_cases x <;> simp)
    (fun x => by fin_cases x <;> simp [hk] <;> omega)
    (fun x => by fin_cases x <;> simp <;> linarith) (by simp [Fin.sum_univ_succ]; ring)
    (band_of_eq hM le_rfl (by rw [hk, hJ]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM le_rfl (by rw [hk, hJ]; simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM le_rfl (by
      rw [hk, hJ, show (2 * h + 1 + 1) / 2 = h + 1 by omega]
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
    (band_of_eq hM le_rfl (by
      rw [hk, hJ, show (2 * h + 1 + 1) / 2 = h + 1 by omega,
        show 2 * h + 1 - (h + 1) = h by omega]
      have : (h : ℝ) ≠ 0 := by linarith
      simp [Fin.sum_univ_succ] <;> (try field_simp) <;> ring))
  refine ⟨Q, hQ, ?_⟩
  rw [hc, hk, show (2 * i + 4) % 2 = 0 by omega, hJ]
  simp [Fin.sum_univ_succ]
  ring_nf
  norm_num
  field_simp
  ring

/-- **Odd `m`, even middle budgets `k = 2j+2 ≤ m-3`**: mixing the two laws. -/
theorem odd_mid_even (h j : ℕ) (hh : 1 ≤ h) (hj : j + 1 ≤ h) (η : ℝ) (hη : 0 ≤ η)
    (k : Fin (2 * h + 1 + 2 + 1)) (hk : k.val = 2 * j + 2) :
    layerValue (gFamily (2 * h + 1 + 2)) η k
      ≤ max (1 - η) 0 * ((2 * (j : ℝ) + 2) / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7))) := by
  obtain ⟨Q1, hQ1, hc1⟩ := odd_L1 h j hh hj k hk
  obtain ⟨Q0, hQ0, hc0⟩ : ∃ Q ∈ SubFeasible (m := 2 * h + 1 + 2) k.val 0,
      ∑ S, Q S * subCost (gFamily (2 * h + 1 + 2)) k S
        = (2 * (j : ℝ) + 2) / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      obtain ⟨Q, hQ, hc⟩ := odd_L0_two h hh k (by rw [hk])
      exact ⟨Q, hQ, by rw [hc]; norm_num⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨Q, hQ, hc⟩ := odd_L0_big h i (by omega) k (by rw [hk]; ring)
      exact ⟨Q, hQ, by rw [hc]; push_cast; ring_nf⟩
  rcases le_total η 1 with h1 | h1
  · have := layer_le_mix (gFamily (2 * h + 1 + 2)) k 0 1 η η hη h1 (le_of_eq (by ring))
      Q0 Q1 hQ0 hQ1
    rw [hc0, hc1] at this
    rw [max_eq_left (by linarith)]
    linarith
  · have := layer_le (gFamily (2 * h + 1 + 2)) η k Q1 (sub_mono k.val h1 Q1 hQ1)
    rw [hc1] at this
    rw [max_eq_right (by linarith), zero_mul]
    exact this

/-! ## 4. The lower bounds -/

/-- The even budget-one certificate, for every `η`. -/
theorem even_lower (h : ℕ) (hh : 1 ≤ h) (η : ℝ) (hη : 0 ≤ η) :
    4 * (1 - η) / ((2 * (h : ℝ) + 2) * (2 * (h : ℝ) + 2 + 4))
      ≤ layerValue (gFamily (2 * h + 2)) η ⟨1, by omega⟩ := by
  set k1 : Fin (2 * h + 2 + 1) := ⟨1, by omega⟩ with hk1
  have hD : 0 < normMass (gFamily (2 * h + 2)) := by
    rw [normMass_g (2 * h) (by omega)]; positivity
  have hbase : trueBaseline (gFamily (2 * h + 2)) k1 = 1 := by
    rw [CIGAMF.P13.PaperCBaselineAttain.familyBaselineIdentification_holds (2 * h + 2) (by omega)
      k1 (by simp [hk1]) (by simp [hk1])]
    simp [hk1]
  have hlay := layer_ge_of_linear (gFamily (2 * h + 2)) η k1 (sub_nonempty η hη k1) hD 0
    (fun i => |gFamily (2 * h + 2) i| - 1) (by
      intro S hS
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hS
      rw [Finset.sum_singleton, Finset.sum_singleton, hbase]
      linarith)
  have hs1 : ∑ i, (|gFamily (2 * h + 2) i| - 1) = 4 := by
    rw [sum_fn_even h hh (fun x => |x| - 1)]; norm_num
  have hs2 : ∑ i, |(|gFamily (2 * h + 2) i| - 1)| = 4 := by
    rw [sum_fn_even h hh (fun x => |(|x| - 1)|)]; norm_num
  rw [hs1, hs2, normMass_g (2 * h) (by omega)] at hlay
  refine le_trans (le_of_eq ?_) hlay
  simp only [hk1]
  push_cast
  field_simp
  ring

/-- An odd budget-`(m-1)` certificate with weights `β_i = f(g_i)`. -/
theorem odd_cert (h : ℕ) (η : ℝ) (hη : 0 ≤ η) (f : ℝ → ℝ) (α : ℝ)
    (hcert : ∀ x : ℝ, (x = -3 ∨ x = -1 ∨ x = 1 ∨ x = 3) →
      α + (f (-3) + f 3 + ((h : ℝ) + 1) * f (-1) + (h : ℝ) * f 1) - f x ≤ |-1 - x|) :
    (α + (2 * (h : ℝ) + 2) / (2 * (h : ℝ) + 3)
        * (f (-3) + f 3 + ((h : ℝ) + 1) * f (-1) + (h : ℝ) * f 1)
      - η / (2 * (h : ℝ) + 3)
        * (|f (-3)| + |f 3| + ((h : ℝ) + 1) * |f (-1)| + (h : ℝ) * |f 1|))
      / (2 * (h : ℝ) + 7)
      ≤ layerValue (gFamily (2 * h + 1 + 2)) η ⟨2 * h + 1 + 1, by omega⟩ := by
  set km : Fin (2 * h + 1 + 2 + 1) := ⟨2 * h + 1 + 1, by omega⟩ with hkm
  have hD : 0 < normMass (gFamily (2 * h + 1 + 2)) := by
    rw [normMass_g (2 * h + 1) (by omega)]; positivity
  have hbase : trueBaseline (gFamily (2 * h + 1 + 2)) km = 0 := by
    rw [CIGAMF.P13.PaperCBaselineAttain.familyBaselineIdentification_holds (2 * h + 1 + 2)
      (by omega) km (by simp [hkm]) (by simp [hkm])]
    simp only [hkm]
    rw [show (2 * h + 1 + 1) % 2 = 0 by omega]; simp
  have hF := sum_fn_odd h f
  have hlay := layer_ge_of_linear (gFamily (2 * h + 1 + 2)) η km (sub_nonempty η hη km) hD α
    (fun i => f (gFamily (2 * h + 1 + 2) i)) (by
      intro S hS
      have hc : Sᶜ.card = 1 := by
        rw [Finset.card_compl, hS, Fintype.card_fin]; simp [hkm]
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
      have hSj : S = {j}ᶜ := by rw [← hj, compl_compl]
      subst hSj
      rw [sum_compl_one, sum_compl_one, total_odd h, hbase, hF, sub_zero]
      have := hcert _ (gFamily_weights (2 * h + 1 + 2) j)
      linarith)
  rw [hF, sum_fn_odd h (fun x => |f x|), normMass_g (2 * h + 1) (by omega)] at hlay
  refine le_trans (le_of_eq ?_) hlay
  simp only [hkm]
  push_cast
  ring

/-! ## 5. The exact budget-aware values -/

/-- **Even `m`: the exact budget-aware value, for every `η ≥ 0`.** -/
theorem aware_even_exact (m : ℕ) (hm : 4 ≤ m) (heven : Even m) (η : ℝ) (hη : 0 ≤ η) :
    awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
      = 4 * max (1 - η) 0 / ((m : ℝ) * ((m : ℝ) + 4)) := by
  obtain ⟨h, rfl⟩ : ∃ h, m = 2 * h + 2 := ⟨(m - 2) / 2, by obtain ⟨r, hr⟩ := heven; omega⟩
  have hh : 1 ≤ h := by omega
  have hcast : ((2 * h + 2 : ℕ) : ℝ) = 2 * (h : ℝ) + 2 := by push_cast; ring
  rw [hcast]
  have hpos : (0 : ℝ) < (2 * (h : ℝ) + 2) * (2 * (h : ℝ) + 2 + 4) := by positivity
  have htgt : 0 ≤ 4 * max (1 - η) 0 / ((2 * (h : ℝ) + 2) * (2 * (h : ℝ) + 2 + 4)) :=
    div_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) hpos.le
  set k1 : Fin (2 * h + 2 + 1) := ⟨1, by omega⟩ with hk1
  have hk1K : k1 ∈ interiorK (2 * h + 2) := by simp [interiorK, hk1] <;> omega
  apply le_antisymm
  · unfold awareValue
    refine Finset.sup'_le _ _ fun k hk => ?_
    have hk' : 1 ≤ k.val ∧ k.val ≤ 2 * h + 2 - 1 := by simpa [interiorK] using hk
    obtain ⟨d1, dc⟩ := even_drop h hh η hη
    rcases Nat.even_or_odd k.val with ⟨r, hr⟩ | ⟨r, hr⟩
    · -- even budget: a middle one
      exact (even_mid_even h (r - 1) hh (by omega) η hη k (by omega)).trans htgt
    · rcases Nat.lt_or_ge r 1 with hr0 | hr0
      · have : k = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
        rw [this]; exact d1
      · rcases Nat.lt_or_ge r h with hrh | hrh
        · exact (even_mid_odd h (r - 1) hh (by omega) η hη k (by omega)).trans htgt
        · have : k = ⟨2 * h + 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [this]; exact dc
  · have hle := Finset.le_sup' (fun k => layerValue (gFamily (2 * h + 2)) η k) hk1K
    unfold awareValue
    refine le_trans ?_ hle
    rcases le_total η 1 with h1 | h1
    · rw [max_eq_left (by linarith)]
      exact even_lower h hh η hη
    · rw [max_eq_right (by linarith), mul_zero, zero_div]
      exact layer_nonneg _ η k1 (sub_nonempty η hη k1)

/-- **Odd `m`: the exact budget-aware value, for every `η ≥ 0`.** -/
theorem aware_odd_exact (m : ℕ) (hm : 3 ≤ m) (hodd : m % 2 = 1) (η : ℝ) (hη : 0 ≤ η) :
    awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
      = max ((m : ℝ) + 3 - ((m : ℝ) + 1) * η) (max ((m : ℝ) + 1 - ((m : ℝ) - 1) * η) 0)
        / ((m : ℝ) * ((m : ℝ) + 4)) := by
  obtain ⟨h, rfl⟩ : ∃ h, m = 2 * h + 1 + 2 := ⟨(m - 3) / 2, by omega⟩
  have hcast : ((2 * h + 1 + 2 : ℕ) : ℝ) = 2 * (h : ℝ) + 3 := by push_cast; ring
  rw [hcast]
  have e1 : 2 * (h : ℝ) + 3 + 3 - (2 * (h : ℝ) + 3 + 1) * η = 2 * (h : ℝ) + 6 - (2 * (h : ℝ) + 4) * η := by ring
  have e2 : 2 * (h : ℝ) + 3 + 1 - (2 * (h : ℝ) + 3 - 1) * η = 2 * (h : ℝ) + 4 - (2 * (h : ℝ) + 2) * η := by ring
  have e3 : (2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 3 + 4) = (2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7) := by ring
  rw [e1, e2, e3]
  have hD : (0 : ℝ) < (2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7) := by positivity
  set T := max (2 * (h : ℝ) + 6 - (2 * (h : ℝ) + 4) * η)
      (max (2 * (h : ℝ) + 4 - (2 * (h : ℝ) + 2) * η) 0) with hT
  have hTa : 2 * (h : ℝ) + 6 - (2 * (h : ℝ) + 4) * η ≤ T := le_max_left _ _
  have hTb : 2 * (h : ℝ) + 4 - (2 * (h : ℝ) + 2) * η ≤ T :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hT0 : 0 ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  set km : Fin (2 * h + 1 + 2 + 1) := ⟨2 * h + 1 + 1, by omega⟩ with hkm
  have hkmK : km ∈ interiorK (2 * h + 1 + 2) := by simp [interiorK, hkm]
  apply le_antisymm
  · unfold awareValue
    refine Finset.sup'_le _ _ fun k hk => ?_
    have hk' : 1 ≤ k.val ∧ k.val ≤ 2 * h + 1 + 2 - 1 := by simpa [interiorK] using hk
    obtain ⟨d1, dc⟩ := odd_drop h η hη
    have htgt : 0 ≤ T / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7)) := div_nonneg hT0 hD.le
    rcases Nat.lt_or_ge k.val 2 with hk1 | hk2
    · have : k = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this]; exact d1
    rcases Nat.lt_or_ge k.val (2 * h + 2) with hkl | hkl
    · rcases Nat.even_or_odd k.val with ⟨r, hr⟩ | ⟨r, hr⟩
      · refine (odd_mid_even h (r - 1) (by omega) (by omega) η hη k (by omega)).trans ?_
        rcases le_total η 1 with h1 | h1
        · rw [max_eq_left (by linarith)]
          refine le_trans ?_ (div_le_div_of_nonneg_right hTa hD.le)
          rw [mul_div_assoc']
          refine div_le_div_of_nonneg_right ?_ hD.le
          have hr1 : ((r - 1 : ℕ) : ℝ) + 1 ≤ h := by
            have : r - 1 + 1 ≤ h := by omega
            exact_mod_cast this
          nlinarith
        · rw [max_eq_right (by linarith), zero_mul]; exact htgt
      · rcases Nat.lt_or_ge r h with hra | hrb
        · exact (odd_mid_odd_a h (r - 1) (by omega) η hη k (by omega)).trans htgt
        · exact (odd_mid_odd_b h (r - 1) (by omega) η hη k (by omega)).trans htgt
    · have : k = ⟨2 * h + 1 + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [this]; exact dc
  · have hle := Finset.le_sup' (fun k => layerValue (gFamily (2 * h + 1 + 2)) η k) hkmK
    unfold awareValue
    refine le_trans ?_ hle
    have c1 := odd_cert h η hη (fun x => 2 - |-1 - x|) (2 - 2 * h) (by
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num <;> ring_nf <;> norm_num)
    have c2 := odd_cert h η hη (fun x => if x = -1 then 2 else 0) (-2 * h) (by
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num <;> ring_nf <;> norm_num)
    have c0 : 0 ≤ layerValue (gFamily (2 * h + 1 + 2)) η km :=
      layer_nonneg _ η km (sub_nonempty η hη km)
    rw [div_le_iff₀ hD]
    have v1 : (2 * (h : ℝ) + 6 - (2 * (h : ℝ) + 4) * η) / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7))
        ≤ layerValue (gFamily (2 * h + 1 + 2)) η km := by
      refine le_trans (le_of_eq ?_) c1
      norm_num
      field_simp
      ring
    have v2 : (2 * (h : ℝ) + 4 - (2 * (h : ℝ) + 2) * η) / ((2 * (h : ℝ) + 3) * (2 * (h : ℝ) + 7))
        ≤ layerValue (gFamily (2 * h + 1 + 2)) η km := by
      refine le_trans (le_of_eq ?_) c2
      norm_num
      field_simp
      ring
    rw [div_le_iff₀ hD] at v1 v2
    exact max_le v1 (max_le v2 (mul_nonneg c0 hD.le))

/-! ## 6. Sharpness: the value of knowing the budget -/

/-- **Even `m`: the value of knowing the budget, in closed form.** -/
theorem advantage_even (m : ℕ) (hm : 4 ≤ m) (heven : Even m) (η : ℝ) (hη : 0 ≤ η) :
    trueValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
        - awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
      = max (freeValue m) (4 * (1 - η) / ((m : ℝ) * denom m))
        - 4 * max (1 - η) 0 / ((m : ℝ) * ((m : ℝ) + 4)) := by
  rw [trueValue_family m (by omega) η, even_frontier_all m hm heven η hη,
    aware_even_exact m hm heven η hη]

/-- **Even `m`: knowing the budget helps exactly past `η* = (m-2)/(2(m-1))`.** -/
theorem advantage_even_pos_iff (m : ℕ) (hm : 4 ≤ m) (heven : Even m) (η : ℝ) (hη : 0 ≤ η) :
    0 < trueValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
        - awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
      ↔ etaStar m < η := by
  constructor
  · intro hA
    by_contra hle
    push_neg at hle
    obtain ⟨hB, hU⟩ := CIGAMF.P13.PaperCBudgetGm.aware_even m hm heven η hη hle
    rw [hB, hU, sub_self] at hA
    exact lt_irrefl _ hA
  · intro hlt
    rw [advantage_even m hm heven η hη, sub_pos]
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    have hmR : (4 : ℝ) ≤ m := by exact_mod_cast hm
    unfold freeValue denom
    unfold etaStar at hlt
    rw [div_lt_iff₀ (by linarith)] at hlt
    rcases le_total η 1 with h1 | h1
    · rw [max_eq_left (show (0 : ℝ) ≤ 1 - η by linarith), div_lt_div_iff₀ (by positivity) (by nlinarith)]
      nlinarith
    · rw [max_eq_right (show 1 - η ≤ (0 : ℝ) by linarith), mul_zero, zero_div]
      apply div_pos (by norm_num); nlinarith

/-- **Odd `m`: knowing the budget helps exactly past `η_t = 1 - 2/(m(m-1))`.** -/
theorem advantage_odd_pos_iff (m : ℕ) (hm : 3 ≤ m) (hodd : m % 2 = 1) (η : ℝ) (hη : 0 ≤ η) :
    0 < trueValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
        - awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega))
      ↔ 1 - 2 / ((m : ℝ) * ((m : ℝ) - 1)) < η := by
  constructor
  · intro hA
    by_contra hle
    push_neg at hle
    obtain ⟨hB, hU⟩ := CIGAMF.P13.PaperCBudgetGm.aware_odd m hm hodd η hη hle
    rw [hB, hU, sub_self] at hA
    exact lt_irrefl _ hA
  · intro hlt
    rw [trueValue_family m (by omega) η, odd_frontier m hm hodd η hη,
      aware_odd_exact m hm hodd η hη, sub_pos]
    refine lt_of_lt_of_le ?_ (le_max_right _ _)
    have hx : (3 : ℝ) ≤ m := by exact_mod_cast hm
    set x : ℝ := (m : ℝ) with hxdef
    have hx1 : 0 < x - 1 := by linarith
    have hxx : 0 < x * (x - 1) := by positivity
    rw [sub_lt_comm, lt_div_iff₀ hxx] at hlt
    -- `w = 2x/(x-1)` is the free value in units of `1/(xD)`
    set w : ℝ := 2 * x / (x - 1) with hw
    have hw1 : w * (x - 1) = 2 * x := by rw [hw]; field_simp
    have hw2 : 2 < w := by rw [hw, lt_div_iff₀ hx1]; linarith
    have hfree : freeValue m + max 0 (1 - η) / (x * denom m)
        = (w + max 0 (1 - η)) / (x * (x + 4)) := by
      unfold freeValue denom
      rw [← hxdef, hw]
      field_simp
    rw [hfree]
    refine div_lt_div_of_pos_right ?_ (by positivity)
    rcases le_total η 1 with h1 | h1
    · rw [max_eq_right (show (0 : ℝ) ≤ 1 - η by linarith)]
      have k0 : (x + 2 - x * η) * (x - 1) < w * (x - 1) := by rw [hw1]; nlinarith
      have k1 : x + 2 - x * η < w := lt_of_mul_lt_mul_right k0 hx1.le
      refine max_lt (by linarith) (max_lt (by nlinarith) (by linarith))
    · rw [max_eq_left (show 1 - η ≤ (0 : ℝ) by linarith), add_zero]
      have e1 : (x + 1) * 1 ≤ (x + 1) * η := mul_le_mul_of_nonneg_left h1 (by linarith)
      have e2 : (x - 1) * 1 ≤ (x - 1) * η := mul_le_mul_of_nonneg_left h1 (by linarith)
      refine max_lt (by linarith) (max_lt (by linarith) (by linarith))

/-! ## 7. Recourse on the zero-value ranges -/

/-- **Even `m`, `0 ≤ η ≤ η*`: every recourse level, one exchange included, equals `B`.** -/
theorem recourse_eq_aware_even (m : ℕ) (hm : 4 ≤ m) (heven : Even m) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ etaStar m) (R : ℕ) :
    recourseValue (gFamily m) η R (interiorK m) (interiorK_nonempty m (by omega))
      = awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega)) := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨hB, hU⟩ := CIGAMF.P13.PaperCBudgetGm.aware_even m hm heven η hη0 hη
  exact le_antisymm ((recourse_le_true _ η hη0 R _ _).trans (by rw [hU, hB]))
    (aware_le_recourse _ η hη0 R _ _)

/-- **Odd `m`, `0 ≤ η ≤ 1 - 2/(m(m-1))`: every recourse level equals `B`.** -/
theorem recourse_eq_aware_odd (m : ℕ) (hm : 3 ≤ m) (hodd : m % 2 = 1) (η : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1 - 2 / ((m : ℝ) * ((m : ℝ) - 1))) (R : ℕ) :
    recourseValue (gFamily m) η R (interiorK m) (interiorK_nonempty m (by omega))
      = awareValue (gFamily m) η (interiorK m) (interiorK_nonempty m (by omega)) := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨hB, hU⟩ := CIGAMF.P13.PaperCBudgetGm.aware_odd m hm hodd η hη0 hη
  exact le_antisymm ((recourse_le_true _ η hη0 R _ _).trans (by rw [hU, hB]))
    (aware_le_recourse _ η hη0 R _ _)

#print axioms drop4
#print axioms even_drop
#print axioms even_mid_even
#print axioms even_mid_odd
#print axioms odd_drop
#print axioms odd_mid_odd_a
#print axioms odd_mid_odd_b
#print axioms odd_mid_even
#print axioms even_lower
#print axioms odd_cert
#print axioms aware_even_exact
#print axioms aware_odd_exact
#print axioms advantage_even
#print axioms advantage_even_pos_iff
#print axioms advantage_odd_pos_iff
#print axioms recourse_eq_aware_even
#print axioms recourse_eq_aware_odd

end CIGAMF.P13.PaperCBudgetSharp
