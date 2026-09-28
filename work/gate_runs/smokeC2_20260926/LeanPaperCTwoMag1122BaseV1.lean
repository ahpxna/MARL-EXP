import «LeanPaperCTwoMagSixV1»

/-!
# Paper C: counts `(1,1,2,2)` at every ratio — the base layer

`g = (a, -a, b, b, -b, -b)` with `0 < b < a`, `D = ‖g‖₁ = 2a + 4b`, interior budgets
`K5 = {1,…,5}`. The objects `ty6`, `wt`, `g6` and `cost_eq` come from `LeanPaperCTwoMagSixV1`.

This module is the glue for the value computations of `LeanPaperCTwoMag1122PriceV1`.
* `base_bl`: the baselines at every ratio, `b_k = 0, b, 0, min(b, |a-2b|), 0, b, 0`.
* `rawC`: the raw cost `|a(v₀-v₁) + b(v₂-v₃)| - b_k` of a count state in coordinates, and
  `cost_coord`: the normalised flow cost is `rawC / D`.
* `RL`, `RM`, `RH`: the raw cost as a table linear in `a, b` on the three cost regimes
  `a ≤ 2b`, `2b ≤ a ≤ 3b`, `3b ≤ a` (`rawC_L`, `rawC_M`, `rawC_H`); off layer three the table
  `RL` is right at every ratio (`rawC_off3`).
* `cert6`: a dual certificate for the banded count-flow program, in coordinates. Budget weights
  `M_k / q`, a band multiplier `Lb_k / (qD)` on each of the two `a`-types, and potentials
  `Ψ / (qD)`. The edge inequalities are checked on the 36 states of the box (`EdgeOK`). It is
  `cert_lower` of `LeanPaperCFlowCertV1` specialised to this multiset.
* `mix_cost`, `mix_band`: the budget costs and the band of a mixture of type sequences whose
  prefix counts are given by a table (checked by `decide` in the users).
* `value_le_flow`: a banded count-feasible flow bounds the value from above.
-/

namespace CIGAMF.P13.PaperCTwoMag1122

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCFlow
open CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCRankFlow
open CIGAMF.P13.PaperCFlowLaw CIGAMF.P13.PaperCNaming
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCBreakpoint
open CIGAMF.P13.PaperCFlowBandJoin CIGAMF.P13.PaperCVacuity CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFreeBand CIGAMF.P13.PaperCFlowCert
open CIGAMF.P13.PaperCPathMix CIGAMF.P13.PaperCFrontier CIGAMF.P13.PaperCLawPush
open CIGAMF.P13.PaperCTwoMagSix

/-- The interior budgets. -/
def K5 : Finset (Fin 7) := {1, 2, 3, 4, 5}

theorem K5_ne : K5.Nonempty := ⟨1, by simp [K5]⟩

variable {a b : ℝ}

/-! ## 1. Baselines at every ratio -/

theorem lin_all (k : ℕ) (L : ℝ)
    (hL : ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 → x0 + x1 + x2 + x3 = k →
      L ≤ |a * ((x0 : ℝ) - x1) + b * ((x2 : ℝ) - x3)|)
    (u : Fin 4 → ℕ) (hu : ∀ τ, u τ ≤ mult ty6 τ) (hs : ∑ τ, u τ = k) :
    L ≤ |∑ τ, wt a b τ * (u τ : ℝ)| := by
  obtain ⟨h0, h1, h2', h3'⟩ := counts_cases u hu
  rw [sum_wt]
  exact hL _ _ _ _ h0 h1 h2' h3' (by rw [← hs, sum_four])

theorem base0' : trueBaseline (g6 a b) 0 = 0 := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 0 ∅ (by decide)).trans (le_of_eq ?_)
    simp
  · exact baseline_nonneg _ _

theorem base1' (hb : 0 < b) (hab : b < a) : trueBaseline (g6 a b) 1 = b := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 1 {2} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty6, wt, abs_of_pos hb]
  · refine baseline_ge_counts ty6 (wt a b) 1 b (lin_all 1 b ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      first
      | omega
      | (rw [le_abs]; push_cast; first | (left; linarith) | (right; linarith))

theorem base2' : trueBaseline (g6 a b) 2 = 0 := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 2 {0, 1} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty6, wt]
  · exact baseline_nonneg _ _

theorem base3' (hb : 0 < b) (hab : b < a) : trueBaseline (g6 a b) 3 = min b |a - 2 * b| := by
  apply le_antisymm
  · refine le_min ?_ ?_
    · refine (baseline_le_set ty6 (wt a b) 3 {0, 1, 2} (by decide)).trans (le_of_eq ?_)
      simp [typedG, ty6, wt, Finset.sum_insert, abs_of_pos hb]
    · refine (baseline_le_set ty6 (wt a b) 3 {0, 4, 5} (by decide)).trans (le_of_eq ?_)
      simp [typedG, ty6, wt, Finset.sum_insert]
      congr 1; ring
  · refine baseline_ge_counts ty6 (wt a b) 3 _ (lin_all 3 _ ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      first
      | omega
      | exact min_le_of_left_le (by
          rw [le_abs]; push_cast; first | (left; linarith) | (right; linarith))
      | exact min_le_of_right_le (le_of_eq (by push_cast; congr 1; ring1))
      | exact min_le_of_right_le (le_of_eq (by push_cast; rw [← abs_neg]; congr 1; ring1))

theorem base4' : trueBaseline (g6 a b) 4 = 0 := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 4 {0, 1, 2, 4} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty6, wt, Finset.sum_insert]
  · exact baseline_nonneg _ _

theorem base5' (hb : 0 < b) (hab : b < a) : trueBaseline (g6 a b) 5 = b := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 5 {0, 1, 2, 3, 4} (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty6, wt, Finset.sum_insert, abs_of_pos hb]
  · refine baseline_ge_counts ty6 (wt a b) 5 b (lin_all 5 b ?_)
    intro x0 x1 x2 x3 h0 h1 h2 h3 hs
    interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
      first
      | omega
      | (rw [le_abs]; push_cast; first | (left; linarith) | (right; linarith))

theorem base6' : trueBaseline (g6 a b) 6 = 0 := by
  apply le_antisymm
  · refine (baseline_le_set ty6 (wt a b) 6 Finset.univ (by decide)).trans (le_of_eq ?_)
    simp [typedG, ty6, wt, Fin.sum_univ_succ]
  · exact baseline_nonneg _ _

/-- The baselines as a function of the budget. -/
noncomputable def bl (a b : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => b
  | 2 => 0
  | 3 => min b |a - 2 * b|
  | 4 => 0
  | 5 => b
  | _ => 0

/-- **The baselines at every ratio.** -/
theorem base_bl (hb : 0 < b) (hab : b < a) (k : Fin 7) : trueBaseline (g6 a b) k = bl a b k.val := by
  fin_cases k
  · exact base0'
  · exact base1' hb hab
  · exact base2'
  · exact base3' hb hab
  · exact base4'
  · exact base5' hb hab
  · exact base6'

theorem min_L (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) : min b |a - 2 * b| = 2 * b - a := by
  rw [abs_of_nonpos (by linarith), min_eq_right (by linarith)]; ring

theorem min_M (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) : min b |a - 2 * b| = a - 2 * b := by
  rw [abs_of_nonneg (by linarith), min_eq_right (by linarith)]

theorem min_H (hb : 0 < b) (h3 : 3 * b ≤ a) : min b |a - 2 * b| = b := by
  rw [abs_of_nonneg (by linarith), min_eq_left (by linarith)]

/-! ## 2. The raw cost of a count state -/

/-- The raw (unnormalised) cost of the count state `(x₀, x₁, x₂, x₃)` at its own layer. -/
noncomputable def rawC (a b : ℝ) (x0 x1 x2 x3 : ℕ) : ℝ :=
  |a * ((x0 : ℝ) - (x1 : ℝ)) + b * ((x2 : ℝ) - (x3 : ℝ))| - bl a b (x0 + x1 + x2 + x3)

/-- **The flow cost in coordinates.** -/
theorem cost_coord (hb : 0 < b) (hab : b < a) (k : Fin 7) (v : CState 4 6)
    (hk : (v 0 : ℕ) + (v 1 : ℕ) + (v 2 : ℕ) + (v 3 : ℕ) = k.val) :
    typedCost ty6 (wt a b) k v = rawC a b (v 0) (v 1) (v 2) (v 3) / (2 * a + 4 * b) := by
  rw [cost_eq hb hab, base_bl hb hab]
  unfold rawC
  rw [hk]

/-- The raw cost table on regime L. -/
def RL (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => 0
  | 0, 0, 0, 1 => 0
  | 0, 0, 0, 2 => 2 * b
  | 0, 0, 1, 0 => 0
  | 0, 0, 1, 1 => 0
  | 0, 0, 1, 2 => a - b
  | 0, 0, 2, 0 => 2 * b
  | 0, 0, 2, 1 => a - b
  | 0, 0, 2, 2 => 0
  | 0, 1, 0, 0 => a - b
  | 0, 1, 0, 1 => a + b
  | 0, 1, 0, 2 => 2 * a
  | 0, 1, 1, 0 => a - b
  | 0, 1, 1, 1 => 2 * a - 2 * b
  | 0, 1, 1, 2 => a + b
  | 0, 1, 2, 0 => 0
  | 0, 1, 2, 1 => a - b
  | 0, 1, 2, 2 => a - b
  | 1, 0, 0, 0 => a - b
  | 1, 0, 0, 1 => a - b
  | 1, 0, 0, 2 => 0
  | 1, 0, 1, 0 => a + b
  | 1, 0, 1, 1 => 2 * a - 2 * b
  | 1, 0, 1, 2 => a - b
  | 1, 0, 2, 0 => 2 * a
  | 1, 0, 2, 1 => a + b
  | 1, 0, 2, 2 => a - b
  | 1, 1, 0, 0 => 0
  | 1, 1, 0, 1 => a - b
  | 1, 1, 0, 2 => 2 * b
  | 1, 1, 1, 0 => a - b
  | 1, 1, 1, 1 => 0
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => 2 * b
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

/-- The raw cost table on regime M. -/
def RM (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => 0
  | 0, 0, 0, 1 => 0
  | 0, 0, 0, 2 => 2 * b
  | 0, 0, 1, 0 => 0
  | 0, 0, 1, 1 => 0
  | 0, 0, 1, 2 => -a + 3 * b
  | 0, 0, 2, 0 => 2 * b
  | 0, 0, 2, 1 => -a + 3 * b
  | 0, 0, 2, 2 => 0
  | 0, 1, 0, 0 => a - b
  | 0, 1, 0, 1 => a + b
  | 0, 1, 0, 2 => 4 * b
  | 0, 1, 1, 0 => a - b
  | 0, 1, 1, 1 => 2 * b
  | 0, 1, 1, 2 => a + b
  | 0, 1, 2, 0 => 0
  | 0, 1, 2, 1 => a - b
  | 0, 1, 2, 2 => a - b
  | 1, 0, 0, 0 => a - b
  | 1, 0, 0, 1 => a - b
  | 1, 0, 0, 2 => 0
  | 1, 0, 1, 0 => a + b
  | 1, 0, 1, 1 => 2 * b
  | 1, 0, 1, 2 => a - b
  | 1, 0, 2, 0 => 4 * b
  | 1, 0, 2, 1 => a + b
  | 1, 0, 2, 2 => a - b
  | 1, 1, 0, 0 => 0
  | 1, 1, 0, 1 => -a + 3 * b
  | 1, 1, 0, 2 => 2 * b
  | 1, 1, 1, 0 => -a + 3 * b
  | 1, 1, 1, 1 => 0
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => 2 * b
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

/-- The raw cost table on regime H. -/
def RH (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => 0
  | 0, 0, 0, 1 => 0
  | 0, 0, 0, 2 => 2 * b
  | 0, 0, 1, 0 => 0
  | 0, 0, 1, 1 => 0
  | 0, 0, 1, 2 => 0
  | 0, 0, 2, 0 => 2 * b
  | 0, 0, 2, 1 => 0
  | 0, 0, 2, 2 => 0
  | 0, 1, 0, 0 => a - b
  | 0, 1, 0, 1 => a + b
  | 0, 1, 0, 2 => a + b
  | 0, 1, 1, 0 => a - b
  | 0, 1, 1, 1 => a - b
  | 0, 1, 1, 2 => a + b
  | 0, 1, 2, 0 => a - 3 * b
  | 0, 1, 2, 1 => a - b
  | 0, 1, 2, 2 => a - b
  | 1, 0, 0, 0 => a - b
  | 1, 0, 0, 1 => a - b
  | 1, 0, 0, 2 => a - 3 * b
  | 1, 0, 1, 0 => a + b
  | 1, 0, 1, 1 => a - b
  | 1, 0, 1, 2 => a - b
  | 1, 0, 2, 0 => a + b
  | 1, 0, 2, 1 => a + b
  | 1, 0, 2, 2 => a - b
  | 1, 1, 0, 0 => 0
  | 1, 1, 0, 1 => 0
  | 1, 1, 0, 2 => 2 * b
  | 1, 1, 1, 0 => 0
  | 1, 1, 1, 1 => 0
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => 2 * b
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0


theorem rawC_L (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (x0 x1 x2 x3 : ℕ) (h0 : x0 ≤ 1)
    (h1 : x1 ≤ 1) (h2' : x2 ≤ 2) (h3 : x3 ≤ 2) : rawC a b x0 x1 x2 x3 = RL a b x0 x1 x2 x3 := by
  have hm := min_L hb hab h2
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    simp only [rawC, RL, bl, hm, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.reduceAdd] <;>
    first
    | ring1
    | (rw [abs_of_nonneg (by linarith)]; ring1)
    | (rw [abs_of_nonpos (by linarith)]; ring1)

theorem rawC_M (hb : 0 < b) (h2 : 2 * b ≤ a) (h3b : a ≤ 3 * b) (x0 x1 x2 x3 : ℕ) (h0 : x0 ≤ 1)
    (h1 : x1 ≤ 1) (h2' : x2 ≤ 2) (h3 : x3 ≤ 2) : rawC a b x0 x1 x2 x3 = RM a b x0 x1 x2 x3 := by
  have hm := min_M h2 h3b
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    simp only [rawC, RM, bl, hm, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.reduceAdd] <;>
    first
    | ring1
    | (rw [abs_of_nonneg (by linarith)]; ring1)
    | (rw [abs_of_nonpos (by linarith)]; ring1)

theorem rawC_H (hb : 0 < b) (h3b : 3 * b ≤ a) (x0 x1 x2 x3 : ℕ) (h0 : x0 ≤ 1)
    (h1 : x1 ≤ 1) (h2' : x2 ≤ 2) (h3 : x3 ≤ 2) : rawC a b x0 x1 x2 x3 = RH a b x0 x1 x2 x3 := by
  have hm := min_H hb h3b
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    simp only [rawC, RH, bl, hm, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.reduceAdd] <;>
    first
    | ring1
    | (rw [abs_of_nonneg (by linarith)]; ring1)
    | (rw [abs_of_nonpos (by linarith)]; ring1)

/-- Off layer three the table `RL` is right at every ratio. -/
theorem rawC_off3 (hb : 0 < b) (hab : b < a) (x0 x1 x2 x3 : ℕ) (h0 : x0 ≤ 1)
    (h1 : x1 ≤ 1) (h2' : x2 ≤ 2) (h3 : x3 ≤ 2) (hk : x0 + x1 + x2 + x3 ≠ 3) :
    rawC a b x0 x1 x2 x3 = RL a b x0 x1 x2 x3 := by
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    first
    | exact absurd rfl hk
    | (simp only [rawC, RL, bl, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Nat.reduceAdd] <;>
        first
        | ring1
        | (rw [abs_of_nonneg (by linarith)]; ring1)
        | (rw [abs_of_nonpos (by linarith)]; ring1))

/-! ## 3. Upper and lower bounds through flows -/

theorem normMass_pos (hb : 0 < b) (hab : b < a) : 0 < normMass (g6 a b) := by
  rw [normMass_g6 hb hab]; linarith

/-- A banded count-feasible flow bounds the value from above. -/
theorem value_le_flow (hb : 0 < b) (hab : b < a) (η : ℝ) (F : LayeredFlow (CState 4 6))
    (hF : CountFeasibleH ty6 F) (hB : FlowBand ty6 F η) :
    trueValue (g6 a b) η K5 K5_ne ≤ K5.sup' K5_ne (flowObj (typedCost ty6 (wt a b)) F) := by
  obtain ⟨P, hP, hPy⟩ := (Set.ext_iff.mp (typed_flow_equivalence ty6 (wt a b) η)
    (flowObj (typedCost ty6 (wt a b)) F)).mpr ⟨F, hF, hB, rfl⟩
  unfold trueValue
  refine (csInf_le (trueValue_bddBelow _ (normMass_pos hb hab) η K5 K5_ne) ⟨P, hP, rfl⟩).trans
    (le_of_eq ?_)
  show K5.sup' K5_ne (fun k => ∑ σ, P σ * normalizedRegret (typedG ty6 (wt a b)) σ k) = _
  rw [hPy]

/-- A bound on every banded count-feasible flow bounds the value from below. -/
theorem value_ge (η : ℝ) (hη : 0 ≤ η) (L : ℝ)
    (h : ∀ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F → FlowBand ty6 F η →
      L ≤ K5.sup' K5_ne (flowObj (typedCost ty6 (wt a b)) F)) :
    L ≤ trueValue (g6 a b) η K5 K5_ne := by
  show L ≤ trueValue (typedG ty6 (wt a b)) η K5 K5_ne
  rw [trueValue_eq_flow]
  unfold flowValue
  obtain ⟨P, hP⟩ := allPerm_feasible_nonempty 6 η hη
  obtain ⟨F, hF, hB, -⟩ := (Set.ext_iff.mp (typed_flow_equivalence ty6 (wt a b) η)
    (fun k => ∑ σ, P σ * normalizedRegret (typedG ty6 (wt a b)) σ k)).mp ⟨P, hP, rfl⟩
  refine le_csInf ⟨_, Set.mem_image_of_mem _ ⟨F, hF, hB, rfl⟩⟩ ?_
  rintro _ ⟨y, ⟨G, hG, hGB, rfl⟩, rfl⟩
  exact h G hG hGB

/-! ## 4. Dual certificates in coordinates -/

/-- The edge inequalities of a certificate at the state `(x₀, x₁, x₂, x₃)`. -/
def EdgeOK (M Lb : ℕ → ℝ) (R Ψ : ℕ → ℕ → ℕ → ℕ → ℝ) (x0 x1 x2 x3 : ℕ) : Prop :=
  (x0 = 0 → Ψ x0 x1 x2 x3 ≤ M (x0 + x1 + x2 + x3) * R x0 x1 x2 x3
      + Lb (x0 + x1 + x2 + x3) * ((x0 : ℝ) + x1 - ((x0 + x1 + x2 + x3 : ℕ) : ℝ) / 3)
      + Ψ 1 x1 x2 x3)
  ∧ (x1 = 0 → Ψ x0 x1 x2 x3 ≤ M (x0 + x1 + x2 + x3) * R x0 x1 x2 x3
      + Lb (x0 + x1 + x2 + x3) * ((x0 : ℝ) + x1 - ((x0 + x1 + x2 + x3 : ℕ) : ℝ) / 3)
      + Ψ x0 1 x2 x3)
  ∧ (x2 < 2 → Ψ x0 x1 x2 x3 ≤ M (x0 + x1 + x2 + x3) * R x0 x1 x2 x3
      + Lb (x0 + x1 + x2 + x3) * ((x0 : ℝ) + x1 - ((x0 + x1 + x2 + x3 : ℕ) : ℝ) / 3)
      + Ψ x0 x1 (x2 + 1) x3)
  ∧ (x3 < 2 → Ψ x0 x1 x2 x3 ≤ M (x0 + x1 + x2 + x3) * R x0 x1 x2 x3
      + Lb (x0 + x1 + x2 + x3) * ((x0 : ℝ) + x1 - ((x0 + x1 + x2 + x3 : ℕ) : ℝ) / 3)
      + Ψ x0 x1 x2 (x3 + 1))

theorem inbox_bounds (v : CState 4 6) (hv : InBox ty6 v) :
    (v 0 : ℕ) ≤ 1 ∧ (v 1 : ℕ) ≤ 1 ∧ (v 2 : ℕ) ≤ 2 ∧ (v 3 : ℕ) ≤ 2 := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h3 := hv 3
  rw [mult0] at h0
  rw [mult1] at h1
  rw [mult2] at h2
  rw [mult3] at h3
  exact ⟨h0, h1, h2, h3⟩

theorem served_coord (v : CState 4 6) :
    served v = (((v 0 : ℕ) + (v 1 : ℕ) + (v 2 : ℕ) + (v 3 : ℕ) : ℕ) : ℝ) := by
  unfold served
  rw [Fin.sum_univ_four]
  push_cast; ring

theorem mult_pos (τ : Fin 4) : 0 < mult ty6 τ := by
  fin_cases τ <;> decide

/-- **A dual certificate in coordinates.** -/
theorem cert6 (hb : 0 < b) (hab : b < a) (q : ℝ) (hq : 0 < q) (M Lb : ℕ → ℝ)
    (R Ψ : ℕ → ℕ → ℕ → ℕ → ℝ) (hM : ∀ k, 0 ≤ M k) (hM0 : M 0 = 0) (hL0 : Lb 0 = 0)
    (hMsum : M 1 + M 2 + M 3 + M 4 + M 5 = q)
    (hR : ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      M (x0 + x1 + x2 + x3) * rawC a b x0 x1 x2 x3 = M (x0 + x1 + x2 + x3) * R x0 x1 x2 x3)
    (hedge : ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 → EdgeOK M Lb R Ψ x0 x1 x2 x3)
    (hend : Ψ 1 1 2 2 = 0) (η : ℝ) (hη : 0 ≤ η) :
    (Ψ 0 0 0 0 - η / 3 * (|Lb 1| + |Lb 2| + |Lb 3| + |Lb 4| + |Lb 5|)) / (q * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  have hqD : 0 < q * (2 * a + 4 * b) := mul_pos hq hD
  apply value_ge η hη
  intro F hF hband
  set μ : ℕ → ℝ := fun k => if k < 6 then M k / q else 0 with hμdef
  set ℓ : ℕ → Fin 4 → ℝ := fun k τ => if (τ : ℕ) < 2 then Lb k / (q * (2 * a + 4 * b)) else 0
    with hℓdef
  set φ : ℕ → CState 4 6 → ℝ := fun _ v => Ψ (v 0) (v 1) (v 2) (v 3) / (q * (2 * a + 4 * b))
    with hφdef
  have hμ0 : ∀ k, 0 ≤ μ k := by
    intro k; simp only [hμdef]; split_ifs
    · exact div_nonneg (hM k) hq.le
    · exact le_rfl
  have hμK : ∀ k : Fin 7, k ∉ K5 → μ k = 0 := by
    intro k hk
    fin_cases k
    · simp [hμdef, hM0]
    · exact absurd (by simp [K5]) hk
    · exact absurd (by simp [K5]) hk
    · exact absurd (by simp [K5]) hk
    · exact absurd (by simp [K5]) hk
    · exact absurd (by simp [K5]) hk
    · simp [hμdef]
  have hμm : ∀ k, 6 ≤ k → μ k = 0 := by
    intro k hk; simp only [hμdef]; rw [if_neg (by omega)]
  have hμ1 : ∑ k ∈ range 6, μ k = 1 := by
    simp only [hμdef, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    rw [hM0]
    field_simp
    linarith
  have hℓ0 : ∀ k τ, mult ty6 τ = 0 → ℓ k τ = 0 := by
    intro k τ h
    exact absurd h (Nat.pos_iff_ne_zero.mp (mult_pos τ))
  have hend' : ∀ v, InBox ty6 v → served v = 6 → φ 6 v = 0 := by
    intro v hv hs
    obtain ⟨h0, h1, h2, h3⟩ := inbox_bounds v hv
    rw [served_coord] at hs
    have hs' : (v 0 : ℕ) + (v 1 : ℕ) + (v 2 : ℕ) + (v 3 : ℕ) = 6 := by exact_mod_cast hs
    have e0 : (v 0 : ℕ) = 1 := by omega
    have e1 : (v 1 : ℕ) = 1 := by omega
    have e2 : (v 2 : ℕ) = 2 := by omega
    have e3 : (v 3 : ℕ) = 2 := by omega
    simp only [hφdef, e0, e1, e2, e3, hend, zero_div]
  have hstart : Ψ 0 0 0 0 / (q * (2 * a + 4 * b)) ≤ φ 0 0 := by
    simp [hφdef]
  have hedge' : ∀ k : ℕ, k < 6 → ∀ v w : CState 4 6, InBox ty6 v → served v = (k : ℝ) →
      InBox ty6 w → StepC v w →
      φ k v ≤ nodeCost ty6 (typedCost ty6 (wt a b)) μ ℓ k v + φ (k + 1) w := by
    intro k hk v w hv hs hw hstep
    obtain ⟨h0, h1, h2, h3⟩ := inbox_bounds v hv
    obtain ⟨g0, g1, g2, g3⟩ := inbox_bounds w hw
    rw [served_coord] at hs
    have hs' : (v 0 : ℕ) + (v 1 : ℕ) + (v 2 : ℕ) + (v 3 : ℕ) = k := by exact_mod_cast hs
    have hk7 : k < 7 := by omega
    have hval : ((Fin.ofNat 7 k : Fin 7) : ℕ) = k := by
      simp [Fin.ofNat, Nat.mod_eq_of_lt hk7]
    -- the node cost in coordinates
    have hnode : nodeCost ty6 (typedCost ty6 (wt a b)) μ ℓ k v
        = (M k * rawC a b (v 0) (v 1) (v 2) (v 3)
          + Lb k * (((v 0 : ℕ) : ℝ) + ((v 1 : ℕ) : ℝ) - (k : ℝ) / 3)) / (q * (2 * a + 4 * b)) := by
      have hμk : μ k = M k / q := by simp only [hμdef]; rw [if_pos hk]
      have hbt : bandTerm ty6 ℓ k v = Lb k / (q * (2 * a + 4 * b))
          * (((v 0 : ℕ) : ℝ) + ((v 1 : ℕ) : ℝ) - (k : ℝ) / 3) := by
        unfold bandTerm
        rw [Fin.sum_univ_four]
        simp only [hℓdef, mult0, mult1, mult2, mult3]
        norm_num
        ring
      unfold nodeCost
      rw [hμk, hbt, cost_coord hb hab _ v (by rw [hval]; exact hs')]
      field_simp
    rw [hnode]
    -- the edge
    obtain ⟨τ, hτ, hrest⟩ := hstep
    have hE := hedge _ _ _ _ h0 h1 h2 h3
    have hRk := hR _ _ _ _ h0 h1 h2 h3
    unfold EdgeOK at hE
    rw [hs'] at hE hRk
    obtain ⟨E0, E1, E2, E3⟩ := hE
    have key : ∀ X : ℝ, Ψ (v 0) (v 1) (v 2) (v 3) ≤ M k * R (v 0) (v 1) (v 2) (v 3)
        + Lb k * (((v 0 : ℕ) : ℝ) + ((v 1 : ℕ) : ℝ) - (k : ℝ) / 3) + X →
        φ k v ≤ (M k * rawC a b (v 0) (v 1) (v 2) (v 3)
          + Lb k * (((v 0 : ℕ) : ℝ) + ((v 1 : ℕ) : ℝ) - (k : ℝ) / 3)) / (q * (2 * a + 4 * b))
          + X / (q * (2 * a + 4 * b)) := by
      intro X hX
      simp only [hφdef]
      rw [← add_div, hRk]
      exact div_le_div_of_nonneg_right (by linarith) hqD.le
    fin_cases τ
    · have hw0 : (w 0 : ℕ) = (v 0 : ℕ) + 1 := hτ
      have hw1 : w 1 = v 1 := hrest 1 (by decide)
      have hw2 : w 2 = v 2 := hrest 2 (by decide)
      have hw3 : w 3 = v 3 := hrest 3 (by decide)
      have hv0 : (v 0 : ℕ) = 0 := by omega
      have := key _ (E0 hv0)
      simp only [hφdef] at this ⊢
      rw [hw0, hw1, hw2, hw3, hv0]
      rw [hv0] at this
      exact this
    · have hw1 : (w 1 : ℕ) = (v 1 : ℕ) + 1 := hτ
      have hw0 : w 0 = v 0 := hrest 0 (by decide)
      have hw2 : w 2 = v 2 := hrest 2 (by decide)
      have hw3 : w 3 = v 3 := hrest 3 (by decide)
      have hv1 : (v 1 : ℕ) = 0 := by omega
      have := key _ (E1 hv1)
      simp only [hφdef] at this ⊢
      rw [hw0, hw1, hw2, hw3, hv1]
      rw [hv1] at this
      exact this
    · have hw2 : (w 2 : ℕ) = (v 2 : ℕ) + 1 := hτ
      have hw0 : w 0 = v 0 := hrest 0 (by decide)
      have hw1 : w 1 = v 1 := hrest 1 (by decide)
      have hw3 : w 3 = v 3 := hrest 3 (by decide)
      have hv2 : (v 2 : ℕ) < 2 := by omega
      have := key _ (E2 hv2)
      simp only [hφdef] at this ⊢
      rw [hw0, hw1, hw2, hw3]
      exact this
    · have hw3 : (w 3 : ℕ) = (v 3 : ℕ) + 1 := hτ
      have hw0 : w 0 = v 0 := hrest 0 (by decide)
      have hw1 : w 1 = v 1 := hrest 1 (by decide)
      have hw2 : w 2 = v 2 := hrest 2 (by decide)
      have hv3 : (v 3 : ℕ) < 2 := by omega
      have := key _ (E3 hv3)
      simp only [hφdef] at this ⊢
      rw [hw0, hw1, hw2, hw3]
      exact this
  have key := cert_lower ty6 (typedCost ty6 (wt a b)) K5 K5_ne μ hμ0 hμK hμm hμ1 ℓ hℓ0 φ
    (Ψ 0 0 0 0 / (q * (2 * a + 4 * b))) hedge' hend' hstart η F hF hband
  have hpen : (η / (6 : ℕ)) * ∑ k ∈ range 6, ∑ τ, |ℓ k τ|
      = η / 3 * (|Lb 1| + |Lb 2| + |Lb 3| + |Lb 4| + |Lb 5|) / (q * (2 * a + 4 * b)) := by
    simp only [hℓdef, Finset.sum_range_succ, Finset.sum_range_zero, Fin.sum_univ_four,
      Fin.val_zero, Fin.val_one, Fin.val_two, hL0]
    norm_num
    rw [abs_div, abs_div, abs_div, abs_div, abs_div, abs_of_pos hqD]
    field_simp
    ring
  rw [hpen] at key
  rw [sub_div]
  linarith

/-! ## 5. Mixtures of type sequences, through a table of prefix counts -/

theorem mix_cost (hb : 0 < b) (hab : b < a) {P : ℕ} (s : Fin P → Fin 6 → Fin 4)
    (tab : Fin P → Fin 7 → Fin 4 → ℕ)
    (hspec : ∀ j, ∀ k : Fin 7, ∀ τ, ((stC (s j) k τ : Fin 7) : ℕ) = tab j k τ)
    (w : Fin P → ℝ) (hw : ∀ j, 0 ≤ w j) (k : Fin 7)
    (hsum : ∀ j, tab j k 0 + tab j k 1 + tab j k 2 + tab j k 3 = k.val) :
    flowObj (typedCost ty6 (wt a b)) (mixFlow s w hw) k
      = (∑ j, w j * rawC a b (tab j k 0) (tab j k 1) (tab j k 2) (tab j k 3))
        / (2 * a + 4 * b) := by
  rw [mixFlow_obj, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cost_coord hb hab k _ (by rw [hspec, hspec, hspec, hspec]; exact hsum j),
    hspec, hspec, hspec, hspec]
  ring

theorem mix_band {P : ℕ} (s : Fin P → Fin 6 → Fin 4) (tab : Fin P → Fin 7 → Fin 4 → ℕ)
    (hspec : ∀ j, ∀ k : Fin 7, ∀ τ, ((stC (s j) k τ : Fin 7) : ℕ) = tab j k τ)
    (w : Fin P → ℝ) (hw : ∀ j, 0 ≤ w j) (η : ℝ)
    (h : ∀ k : Fin 7, ∀ τ : Fin 4,
      |(∑ j, w j * (tab j k τ : ℝ)) / (mult ty6 τ : ℝ) - (k.val : ℝ) / 6| ≤ η / 6) :
    FlowBand ty6 (mixFlow s w hw) η := by
  intro k τ _
  rw [mixFlow_mean]
  simp only [hspec]
  push_cast
  exact h k τ

#print axioms base_bl
#print axioms cost_coord
#print axioms rawC_L
#print axioms rawC_M
#print axioms rawC_H
#print axioms rawC_off3
#print axioms value_le_flow
#print axioms value_ge
#print axioms cert6
#print axioms mix_cost
#print axioms mix_band

end CIGAMF.P13.PaperCTwoMag1122
