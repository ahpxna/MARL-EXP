import «LeanPaperCPathMixV1»

/-!
# Paper C: the two-magnitude family with counts `(1,1,2,2)`, on `13/5 ≤ a/b ≤ 3`

`g = (a, -a, b, b, -b, -b)`, `D = ‖g‖₁ = 2a + 4b`, interior budgets `{1,…,5}`.

This first part fixes the objects:
* `sum_typed`: a subset's sum is `Σ_τ wt_τ · #(S ∩ type τ)`, so the baselines are minima over
  count vectors (`baseline_ge_counts`).
* `base1` … `base5`: `b, 0, a - 2b, 0, b` on `2b ≤ a ≤ 3b`.
* `cost_eq`: the cost of a count state is `(|a(v₀-v₁) + b(v₂-v₃)| - b_k)/D`.
* `band_lower`: the band certificate. An `a`-item comes first with probability at least
  `(1-η)/3`, which costs `a - b` at budget one. So every banded flow has
  `max_k E c_k ≥ (1-η)(a-b)/(3D)`.
-/

namespace CIGAMF.P13.PaperCTwoMagSix

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCFlowBandJoin CIGAMF.P13.PaperCVacuity CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFreeBand CIGAMF.P13.PaperCFlowCert
open CIGAMF.P13.PaperCPathMix CIGAMF.P13.PaperCFrontier

/-- Item types: `+a, -a, +b, +b, -b, -b`. -/
def ty6 : Fin 6 → Fin 4 := ![0, 1, 2, 2, 3, 3]

/-- Type weights. -/
noncomputable def wt (a b : ℝ) : Fin 4 → ℝ := ![a, -a, b, -b]

/-- The multiset. -/
noncomputable def g6 (a b : ℝ) : Fin 6 → ℝ := typedG ty6 (wt a b)

theorem mult0 : mult ty6 0 = 1 := by decide
theorem mult1 : mult ty6 1 = 1 := by decide
theorem mult2 : mult ty6 2 = 2 := by decide
theorem mult3 : mult ty6 3 = 2 := by decide

variable {a b : ℝ}

theorem normMass_g6 (hb : 0 < b) (hab : b < a) : normMass (g6 a b) = 2 * a + 4 * b := by
  have ha : 0 < a := hb.trans hab
  unfold normMass g6 typedG
  simp [ty6, wt, Fin.sum_univ_succ, abs_of_pos ha, abs_of_pos hb]
  ring

/-! ## 1. Subset sums through type counts -/

theorem sum_typed {d m : ℕ} (ty : Fin m → Fin d) (w : Fin d → ℝ) (S : Finset (Fin m)) :
    ∑ i ∈ S, typedG ty w i = ∑ τ, w τ * ((S.filter fun i => ty i = τ).card : ℝ) := by
  rw [← Finset.sum_fiberwise S ty (typedG ty w)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have : ∀ i ∈ S.filter (fun i => ty i = τ), typedG ty w i = w τ := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    unfold typedG; rw [hi.2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **Baselines are minima over count vectors.** -/
theorem baseline_ge_counts {d m : ℕ} (ty : Fin m → Fin d) (w : Fin d → ℝ) (k : Fin (m + 1))
    (L : ℝ)
    (h : ∀ u : Fin d → ℕ, (∀ τ, u τ ≤ mult ty τ) → ∑ τ, u τ = k.val →
      L ≤ |∑ τ, w τ * (u τ : ℝ)|) :
    L ≤ trueBaseline (typedG ty w) k := by
  unfold trueBaseline baseline
  refine Finset.le_inf' _ _ fun S hS => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  rw [sum_typed]
  refine h (fun τ => (S.filter fun i => ty i = τ).card) (fun τ => ?_) ?_
  · unfold mult
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))
  · rw [← hS]
    exact (Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ (ty i))).symm

theorem baseline_le_set {d m : ℕ} (ty : Fin m → Fin d) (w : Fin d → ℝ) (k : Fin (m + 1))
    (S : Finset (Fin m)) (hS : S.card = k.val) :
    trueBaseline (typedG ty w) k ≤ |∑ i ∈ S, typedG ty w i| := by
  unfold trueBaseline baseline
  exact Finset.inf'_le _ (by simp [hS])

/-! ## 2. The baselines on `2b ≤ a ≤ 3b` -/

theorem sum_wt (u : Fin 4 → ℕ) :
    ∑ τ, wt a b τ * (u τ : ℝ) = a * ((u 0 : ℝ) - u 1) + b * ((u 2 : ℝ) - u 3) := by
  simp [wt, Fin.sum_univ_four]; ring

theorem counts_cases (u : Fin 4 → ℕ) (hu : ∀ τ, u τ ≤ mult ty6 τ) :
    u 0 ≤ 1 ∧ u 1 ≤ 1 ∧ u 2 ≤ 2 ∧ u 3 ≤ 2 := by
  have := hu 0; have := hu 1; have := hu 2; have := hu 3
  rw [mult0] at *; rw [mult1] at *; rw [mult2] at *; rw [mult3] at *
  omega

theorem sum_four (u : Fin 4 → ℕ) : ∑ τ, u τ = u 0 + u 1 + u 2 + u 3 := by
  simp [Fin.sum_univ_four]

/-- A lower bound on `|a x + b y|` over the count vectors of one size, by cases. -/
theorem lin_ge (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (k : ℕ) (L : ℝ)
    (hL : ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 → x0 + x1 + x2 + x3 = k →
      L ≤ |a * ((x0 : ℝ) - x1) + b * ((x2 : ℝ) - x3)|)
    (u : Fin 4 → ℕ) (hu : ∀ τ, u τ ≤ mult ty6 τ) (hs : ∑ τ, u τ = k) :
    L ≤ |∑ τ, wt a b τ * (u τ : ℝ)| := by
  obtain ⟨h0, h1, h2', h3'⟩ := counts_cases u hu
  rw [sum_wt]
  exact hL _ _ _ _ h0 h1 h2' h3' (by rw [← hs, sum_four])

theorem base1 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    trueBaseline (g6 a b) 1 = b := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 1 {2} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty6, wt, abs_of_pos hb]
  · refine baseline_ge_counts ty6 (wt a b) 1 b (lin_ge hb h2 h3 1 b ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

theorem base2 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    trueBaseline (g6 a b) 2 = 0 := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 2 {0, 1} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty6, wt]
  · exact baseline_ge_counts ty6 (wt a b) 2 0 fun u _ _ => abs_nonneg _

theorem base3 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    trueBaseline (g6 a b) 3 = a - 2 * b := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 3 {0, 4, 5} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty6, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    rw [abs_of_nonneg (by linarith)]; ring
  · refine baseline_ge_counts ty6 (wt a b) 3 (a - 2 * b) (lin_ge hb h2 h3 3 (a - 2 * b) ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

theorem base4 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    trueBaseline (g6 a b) 4 = 0 := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 4 {0, 1, 2, 4} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty6, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
  · exact baseline_ge_counts ty6 (wt a b) 4 0 fun u _ _ => abs_nonneg _

theorem base5 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    trueBaseline (g6 a b) 5 = b := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 5 {0, 1, 2, 3, 4} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty6, wt, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
      abs_of_pos hb]
  · refine baseline_ge_counts ty6 (wt a b) 5 b (lin_ge hb h2 h3 5 b ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      simp at hs <;> rw [le_abs] <;> push_cast <;> first | (left; linarith) | (right; linarith)

/-! ## 3. The cost of a count state -/

theorem cost_eq (hb : 0 < b) (hab : b < a) (k : Fin 7) (v : CState 4 6) :
    typedCost ty6 (wt a b) k v
      = (|a * (((v 0 : ℕ) : ℝ) - (v 1 : ℕ)) + b * (((v 2 : ℕ) : ℝ) - (v 3 : ℕ))|
          - trueBaseline (g6 a b) k) / (2 * a + 4 * b) := by
  unfold typedCost
  rw [show normMass (typedG ty6 (wt a b)) = 2 * a + 4 * b from normMass_g6 hb hab]
  congr 2
  rw [sum_wt (fun τ => (v τ : ℕ))]

end CIGAMF.P13.PaperCTwoMagSix
