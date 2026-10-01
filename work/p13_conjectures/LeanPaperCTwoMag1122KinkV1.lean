import «LeanPaperCTwoMag1122FlowV1»

/-!
# Paper C: counts `(1,1,2,2)` — the flows at the kinks of the band frontier

Three weightings of the eighteen type sequences of `LeanPaperCTwoMag1122FlowV1`, one at each
interior kink of the band frontier. With `r = a/b`:

| flow | range | band | budget costs at most (times `D`) | orbits |
|---|---|---|---|---|
| `K1` | `2 ≤ r ≤ 7/3` | `2(a-2b)/(5b-a)` | `2b(3b-a)/(5b-a)` | `AaBbBb`, `BBaAbb` |
| `K2` | `7/3 ≤ r ≤ 13/5` | `2(5a²-25ab+32b²)/((a-b)(17b-5a))` | `4b(3b-a)/(17b-5a)` | `AaBbBb`, `BaAbBb`, `BBaAbb` |
| `K3` | `5/2 ≤ r ≤ 13/5` | `2(2a-5b)/(a-b)` | `3b-a` | `AbaBBb`, `BaAbBb`, `AaBbBb` |

`K2` and `K3` meet their cost bound with equality at every budget. The weights, bands and costs
are checked exactly by `scratchpad/c1122f/gflow2.py` before emission.
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

variable {a b : ℝ}

/-- Weight numerators of `K1` (denominator `2 * (5 * b - a)`). -/
noncomputable def W_K1 (a b : ℝ) : Fin 18 → ℝ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (1) * b, (1) * b, (1) * b, (1) * b, (3) * b + (-1) * a, (3) * b + (-1) * a, 0, 0]

/-- Weight numerators of `K2` (denominator `4 * (a - b) * (17 * b - 5 * a)`). -/
noncomputable def W_K2 (a b : ℝ) : Fin 18 → ℝ :=
  ![0, 0, 0, 0, 0, 0, (-28) * b * b + (12) * a * b, (-28) * b * b + (12) * a * b, (-28) * b * b + (12) * a * b, (-28) * b * b + (12) * a * b, (24) * b * b + (-8) * a * b, (24) * b * b + (-8) * a * b, (24) * b * b + (-8) * a * b, (24) * b * b + (-8) * a * b, (-26) * b * b + (36) * a * b + (-10) * a * a, (-26) * b * b + (36) * a * b + (-10) * a * a, 0, 0]

/-- Weight numerators of `K3` (denominator `4 * (a - b)`). -/
noncomputable def W_K3 (a b : ℝ) : Fin 18 → ℝ :=
  ![(13) * b + (-5) * a, (13) * b + (-5) * a, (13) * b + (-5) * a, (13) * b + (-5) * a, 0, 0, (-7) * b + (3) * a, (-7) * b + (3) * a, (-7) * b + (3) * a, (-7) * b + (3) * a, (-7) * b + (3) * a, (-7) * b + (3) * a, (-7) * b + (3) * a, (-7) * b + (3) * a, 0, 0, 0, 0]

/-! ### `K1`: band `2(a-2b)/(5b-a)`, budget costs at most `2b(3b-a)/(5b-a)`, on `2b ≤ a ≤ 7b/3` -/

set_option maxHeartbeats 0 in
theorem flow_K1 (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (2 * (a - 2 * b) / (5 * b - a))
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ (2 * b * (3 * b - a) / (5 * b - a)) / (2 * a + 4 * b) := by
  have hne0 : (5 * b - a) ≠ 0 := by apply ne_of_gt; linarith
  have hQ : (0 : ℝ) < 2 * (5 * b - a) := by linarith
  have hw : ∀ j, 0 ≤ W_K1 a b j / (2 * (5 * b - a)) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_K1] <;> first | linarith | nlinarith [mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg hb.le (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg hb.le (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg (sub_nonneg.2 hab.le) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a)]
  have hW : ∑ j, W_K1 a b j = 2 * (5 * b - a) := by simp [W_K1, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_K1 a b) (2 * (5 * b - a)) hQ hw ((-8) * b + (4) * a) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_K1, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg hb.le (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg hb.le (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a)]) | nlinarith [mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg hb.le (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg hb.le (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a)])
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    field_simp
    try ring
  · have hQT : (2 * (5 * b - a)) * (2 * b * (3 * b - a) / (5 * b - a)) = (12) * b * b + (-4) * a * b := by
      field_simp
      try ring
    refine flow_obj_le hb hab (RM a b) (rawC_M hb h2 (by linarith)) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_K1, RM] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg hb.le (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg hb.le (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), hb]

/-! ### `K2`: band `2(5a²-25ab+32b²)/((a-b)(17b-5a))`, budget costs at most `4b(3b-a)/(17b-5a)`, on `7b/3 ≤ a ≤ 13b/5` -/

set_option maxHeartbeats 0 in
theorem flow_K2 (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (2 * (5 * a * a - 25 * a * b + 32 * b * b) / ((a - b) * (17 * b - 5 * a)))
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ (4 * b * (3 * b - a) / (17 * b - 5 * a)) / (2 * a + 4 * b) := by
  have hne0 : (a - b) ≠ 0 := by apply ne_of_gt; linarith
  have hne1 : (17 * b - 5 * a) ≠ 0 := by apply ne_of_gt; linarith
  have hQ : (0 : ℝ) < 4 * (a - b) * (17 * b - 5 * a) :=
    mul_pos (mul_pos (by norm_num) (sub_pos.2 hab)) (by linarith)
  have hw : ∀ j, 0 ≤ W_K2 a b j / (4 * (a - b) * (17 * b - 5 * a)) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_K2] <;> first | linarith | nlinarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg hb.le (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg hb.le (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 hab.le) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)]
  have hW : ∑ j, W_K2 a b j = 4 * (a - b) * (17 * b - 5 * a) := by simp [W_K2, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_K2 a b) (4 * (a - b) * (17 * b - 5 * a)) hQ hw ((256) * b * b + (-200) * a * b + (40) * a * a) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_K2, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg hb.le (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg hb.le (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)]) | nlinarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg hb.le (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg hb.le (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)])
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    field_simp
    try ring
  · have hQT : (4 * (a - b) * (17 * b - 5 * a)) * (4 * b * (3 * b - a) / (17 * b - 5 * a)) = (-48) * b * b * b + (64) * a * b * b + (-16) * a * a * b := by
      calc (4 * (a - b) * (17 * b - 5 * a)) * (4 * b * (3 * b - a) / (17 * b - 5 * a))
          = 4 * (a - b) * (4 * b * (3 * b - a)) * ((17 * b - 5 * a) / (17 * b - 5 * a)) := by ring
        _ = _ := by rw [div_self hne1]; ring
    refine flow_obj_le hb hab (RM a b) (rawC_M hb (by linarith) (by linarith)) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_K2, RM] <;> nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b)) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg (mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b)) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg hb.le (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg hb.le (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), hb]

/-! ### `K3`: band `2(2a-5b)/(a-b)`, budget costs at most `3b-a`, on `5b/2 ≤ a ≤ 13b/5` -/

set_option maxHeartbeats 0 in
theorem flow_K3 (hb : 0 < b) (hab : b < a) (h5 : 5 * b ≤ 2 * a) (h13 : 5 * a ≤ 13 * b) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (2 * (2 * a - 5 * b) / (a - b))
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ (3 * b - a) / (2 * a + 4 * b) := by
  have hne0 : (a - b) ≠ 0 := by apply ne_of_gt; linarith
  have hQ : (0 : ℝ) < 4 * (a - b) := by linarith
  have hw : ∀ j, 0 ≤ W_K3 a b j / (4 * (a - b)) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_K3] <;> first | linarith | nlinarith [mul_nonneg (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b) (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg hb.le (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b), mul_nonneg hb.le (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 hab.le) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)]
  have hW : ∑ j, W_K3 a b j = 4 * (a - b) := by simp [W_K3, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_K3 a b) (4 * (a - b)) hQ hw ((-40) * b + (16) * a) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_K3, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b) (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg hb.le (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b), mul_nonneg hb.le (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)]) | nlinarith [mul_nonneg (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b) (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg hb.le (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b), mul_nonneg hb.le (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)])
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    field_simp
    try ring
  · have hQT : (4 * (a - b)) * (3 * b - a) = (-12) * b * b + (16) * a * b + (-4) * a * a := by
      field_simp
      try ring
    refine flow_obj_le hb hab (RM a b) (rawC_M hb (by linarith) (by linarith)) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_K3, RM] <;> nlinarith [mul_nonneg (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b) (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg hb.le (sub_nonneg.2 h5 : (0:ℝ) ≤ 2 * a - 5 * b), mul_nonneg hb.le (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), hb]

#print axioms flow_K1
#print axioms flow_K2
#print axioms flow_K3

end CIGAMF.P13.PaperCTwoMag1122
