import «LeanPaperCTwoMag1122BaseV1»

/-!
# Paper C: counts `(1,1,2,2)` — the primal flows

Eighteen type sequences (six orbits under flipping all signs and reversing the order), their
prefix counts (`tq`, checked by `decide` in `tq_spec`), and eight weightings of them. Each
weighting is a count-feasible flow (`mixFlow` of `LeanPaperCPathMixV1`); for each we prove the
band it meets and a bound on every interior budget cost. The weights are `W_j / Q` with `W`, `Q`
polynomial in `a, b`; the checks are exact (`linarith`, with the products of the range constraints
for the quadratic ones).

The data come from `scratchpad/c1122/genflow.py`, which checks every weight, band and cost bound
exactly before emitting.
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

/-! ## 1. The sequences -/

/-- The type sequences: AbaBBb, aBAbbB, bBBabA, BbbABa, BaBbAb, bAbBaB, BaAbBb, bAaBbB, bBbAaB, BbBaAb, AaBbBb, aAbBbB, bBbBaA, BbBbAa, BBaAbb, bbAaBB, BbAaBb, bBaAbB. -/
def sq : Fin 18 → Fin 6 → Fin 4 :=
  ![![0, 3, 1, 2, 2, 3],
    ![1, 2, 0, 3, 3, 2],
    ![3, 2, 2, 1, 3, 0],
    ![2, 3, 3, 0, 2, 1],
    ![2, 1, 2, 3, 0, 3],
    ![3, 0, 3, 2, 1, 2],
    ![2, 1, 0, 3, 2, 3],
    ![3, 0, 1, 2, 3, 2],
    ![3, 2, 3, 0, 1, 2],
    ![2, 3, 2, 1, 0, 3],
    ![0, 1, 2, 3, 2, 3],
    ![1, 0, 3, 2, 3, 2],
    ![3, 2, 3, 2, 1, 0],
    ![2, 3, 2, 3, 0, 1],
    ![2, 2, 1, 0, 3, 3],
    ![3, 3, 0, 1, 2, 2],
    ![2, 3, 0, 1, 2, 3],
    ![3, 2, 1, 0, 3, 2]]

/-- Their prefix counts. -/
def tq : Fin 18 → Fin 7 → Fin 4 → ℕ :=
  ![![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 0, 0, 1], ![1, 1, 0, 1], ![1, 1, 1, 1], ![1, 1, 2, 1], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 1, 0, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 1], ![1, 1, 1, 2], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 2, 1], ![0, 1, 2, 1], ![0, 1, 2, 2], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 1, 2], ![1, 0, 1, 2], ![1, 0, 2, 2], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![0, 1, 2, 0], ![0, 1, 2, 1], ![1, 1, 2, 1], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 1], ![1, 0, 0, 2], ![1, 0, 1, 2], ![1, 1, 1, 2], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 1, 1, 1], ![1, 1, 2, 1], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1], ![1, 0, 0, 1], ![1, 1, 0, 1], ![1, 1, 1, 1], ![1, 1, 1, 2], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 2], ![1, 0, 1, 2], ![1, 1, 1, 2], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 2, 1], ![0, 1, 2, 1], ![1, 1, 2, 1], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![1, 0, 0, 0], ![1, 1, 0, 0], ![1, 1, 1, 0], ![1, 1, 1, 1], ![1, 1, 2, 1], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 1, 0, 0], ![1, 1, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 1], ![1, 1, 1, 2], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 0, 1, 2], ![0, 0, 2, 2], ![0, 1, 2, 2], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 2, 1], ![0, 0, 2, 2], ![1, 0, 2, 2], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 2, 0], ![0, 1, 2, 0], ![1, 1, 2, 0], ![1, 1, 2, 1], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 0, 2], ![1, 0, 0, 2], ![1, 1, 0, 2], ![1, 1, 1, 2], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 1, 0], ![0, 0, 1, 1], ![1, 0, 1, 1], ![1, 1, 1, 1], ![1, 1, 2, 1], ![1, 1, 2, 2]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 1, 2], ![1, 1, 2, 2]]]


set_option maxRecDepth 20000 in
theorem sq_mult : ∀ j τ, mult (sq j) τ = mult ty6 τ := by
  intro j; fin_cases j <;> decide

set_option maxRecDepth 20000 in
theorem tq_spec : ∀ j : Fin 18, ∀ k : Fin 7, ∀ τ : Fin 4,
    ((stC (sq j) k τ : Fin 7) : ℕ) = tq j k τ := by
  intro j; fin_cases j <;> decide

set_option maxRecDepth 20000 in
theorem tq_sum : ∀ j : Fin 18, ∀ k : Fin 7, tq j k 0 + tq j k 1 + tq j k 2 + tq j k 3 = k.val := by
  decide

set_option maxRecDepth 20000 in
theorem tq_box : ∀ j : Fin 18, ∀ k : Fin 7,
    tq j k 0 ≤ 1 ∧ tq j k 1 ≤ 1 ∧ tq j k 2 ≤ 2 ∧ tq j k 3 ≤ 2 := by
  decide

/-! ## 2. Weighted mixtures of the sequences -/

theorem sum_wq (W : Fin 18 → ℝ) (Q : ℝ) (X : Fin 18 → ℝ) :
    ∑ j, W j / Q * X j = (∑ j, W j * X j) / Q := by
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem flow_feas (W : Fin 18 → ℝ) (Q : ℝ) (hQ : 0 < Q) (hw : ∀ j, 0 ≤ W j / Q)
    (hW : ∑ j, W j = Q) : CountFeasibleH ty6 (mixFlow sq (fun j => W j / Q) hw) := by
  refine mixFlow_feasible ty6 sq _ hw ?_ sq_mult
  rw [← Finset.sum_div, hW, div_self hQ.ne']

theorem flow_obj_le (hb : 0 < b) (hab : b < a) (R : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hR : ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      rawC a b x0 x1 x2 x3 = R x0 x1 x2 x3)
    (W : Fin 18 → ℝ) (Q : ℝ) (hQ : 0 < Q) (hw : ∀ j, 0 ≤ W j / Q) (T : ℝ) (k : Fin 7)
    (h : ∑ j, W j * R (tq j k 0) (tq j k 1) (tq j k 2) (tq j k 3) ≤ Q * T) :
    flowObj (typedCost ty6 (wt a b)) (mixFlow sq (fun j => W j / Q) hw) k
      ≤ T / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  rw [mix_cost hb hab sq tq tq_spec _ hw k (fun j => tq_sum j k)]
  apply div_le_div_of_nonneg_right _ hD.le
  have e : ∑ j, W j / Q * rawC a b (tq j k 0) (tq j k 1) (tq j k 2) (tq j k 3)
      = (∑ j, W j * R (tq j k 0) (tq j k 1) (tq j k 2) (tq j k 3)) / Q := by
    rw [sum_wq]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨b0, b1, b2, b3⟩ := tq_box j k
    rw [hR _ _ _ _ b0 b1 b2 b3]
  show ∑ j, W j / Q * rawC a b (tq j k 0) (tq j k 1) (tq j k 2) (tq j k 3) ≤ T
  rw [e, div_le_iff₀ hQ]
  linarith

theorem flow_band (W : Fin 18 → ℝ) (Q : ℝ) (hQ : 0 < Q) (hw : ∀ j, 0 ≤ W j / Q) (E : ℝ)
    (h : ∀ k : Fin 7, ∀ τ : Fin 4,
      |∑ j, W j * (tq j k τ : ℝ) - Q * (mult ty6 τ : ℝ) * (k.val : ℝ) / 6|
        ≤ (mult ty6 τ : ℝ) * E / 6) :
    FlowBand ty6 (mixFlow sq (fun j => W j / Q) hw) (E / Q) := by
  apply mix_band sq tq tq_spec
  intro k τ
  have hm : (0 : ℝ) < mult ty6 τ := by exact_mod_cast mult_pos τ
  have hQm : 0 < Q * (mult ty6 τ : ℝ) := mul_pos hQ hm
  show |(∑ j, W j / Q * (tq j k τ : ℝ)) / (mult ty6 τ : ℝ) - (k.val : ℝ) / 6| ≤ E / Q / 6
  rw [sum_wq]
  rw [show (∑ j, W j * (tq j k τ : ℝ)) / Q / (mult ty6 τ : ℝ) - (k.val : ℝ) / 6
      = (∑ j, W j * (tq j k τ : ℝ) - Q * (mult ty6 τ : ℝ) * (k.val : ℝ) / 6)
        / (Q * (mult ty6 τ : ℝ)) by first | (field_simp; ring) | field_simp]
  rw [abs_div, abs_of_pos hQm, div_le_iff₀ hQm]
  calc _ ≤ (mult ty6 τ : ℝ) * E / 6 := h k τ
    _ = E / Q / 6 * (Q * (mult ty6 τ : ℝ)) := by field_simp

/-! ## 3. The weightings -/

/-- Weight numerators of `L0` (denominator `(6)`). -/
noncomputable def W_L0 (a b : ℝ) : Fin 18 → ℝ :=
  ![(1), (1), (1), (1), (1), (1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]


/-- Weight numerators of `M0` (denominator `(36) * b + (-12) * a`). -/
noncomputable def W_M0 (a b : ℝ) : Fin 18 → ℝ :=
  ![(-2) * b + (1) * a, (-2) * b + (1) * a, (-2) * b + (1) * a, (-2) * b + (1) * a, 0, 0, (-2) * b + (1) * a, (-2) * b + (1) * a, (-2) * b + (1) * a, (-2) * b + (1) * a, (8) * b + (-3) * a, (8) * b + (-3) * a, (8) * b + (-3) * a, (8) * b + (-3) * a, (10) * b + (-4) * a, (10) * b + (-4) * a, 0, 0]


/-- Weight numerators of `H0` (denominator `(24)`). -/
noncomputable def W_H0 (a b : ℝ) : Fin 18 → ℝ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, (4), (4), (4), (4), (3), (3), (1), (1)]


/-- Weight numerators of `Lf` (denominator `(8)`). -/
noncomputable def W_Lf (a b : ℝ) : Fin 18 → ℝ :=
  ![0, 0, 0, 0, (2), (2), 0, 0, 0, 0, (1), (1), (1), (1), 0, 0, 0, 0]


/-- Weight numerators of `M1f` (denominator `(8) * b`). -/
noncomputable def W_M1f (a b : ℝ) : Fin 18 → ℝ :=
  ![0, 0, 0, 0, (6) * b + (-2) * a, (6) * b + (-2) * a, 0, 0, 0, 0, (-1) * b + (1) * a, (-1) * b + (1) * a, (-1) * b + (1) * a, (-1) * b + (1) * a, 0, 0, 0, 0]


/-- Weight numerators of `M23f` (denominator `(44) * b + (-12) * a`). -/
noncomputable def W_M23f (a b : ℝ) : Fin 18 → ℝ :=
  ![0, 0, 0, 0, (26) * b + (-10) * a, (26) * b + (-10) * a, (-14) * b + (6) * a, (-14) * b + (6) * a, (-14) * b + (6) * a, (-14) * b + (6) * a, (12) * b + (-4) * a, (12) * b + (-4) * a, (12) * b + (-4) * a, (12) * b + (-4) * a, 0, 0, 0, 0]


/-- Weight numerators of `M4f` (denominator `(-20) * b + (20) * a`). -/
noncomputable def W_M4f (a b : ℝ) : Fin 18 → ℝ :=
  ![0, 0, 0, 0, 0, 0, (4) * b, (4) * b, (4) * b, (4) * b, (4) * b, (4) * b, (4) * b, (4) * b, 0, 0, (-26) * b + (10) * a, (-26) * b + (10) * a]


/-- Weight numerators of `Hf` (denominator `(10)`). -/
noncomputable def W_Hf (a b : ℝ) : Fin 18 → ℝ :=
  ![0, 0, 0, 0, 0, 0, (1), (1), (1), (1), (1), (1), (1), (1), 0, 0, (1), (1)]

/-! ### `L0`: band `0`, budget costs at most `2(a-b)/3`, on `a ≤ 2b` -/

set_option maxHeartbeats 0 in
theorem flow_L0 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (0)
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ (2 * (a - b) / 3) / (2 * a + 4 * b) := by
  have hQ : (0 : ℝ) < 6 := by linarith
  have hbne : b ≠ 0 := hb.ne'
  have habne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have hw : ∀ j, 0 ≤ W_L0 a b j / (6) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_L0] <;> linarith
  have hW : ∑ j, W_L0 a b j = 6 := by simp [W_L0, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_L0 a b) (6) hQ hw (0) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_L0, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> linarith) | linarith)
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    first | (norm_num; done) | (field_simp; done) | (field_simp; ring)
  · have hQT : (6) * (2 * (a - b) / 3) = (-4) * b + (4) * a := by
      ring
    refine flow_obj_le hb hab (RL a b) (rawC_L hb hab h2) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_L0, RL] <;> linarith

/-! ### `M0`: band `0`, budget costs at most `(4b-a)/3`, on `2b ≤ a ≤ 5b/2` -/

set_option maxHeartbeats 0 in
theorem flow_M0 (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h5 : 2 * a ≤ 5 * b) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (0)
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ ((4 * b - a) / 3) / (2 * a + 4 * b) := by
  have hQ : (0 : ℝ) < 12 * (3 * b - a) := by linarith
  have hbne : b ≠ 0 := hb.ne'
  have habne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have hw : ∀ j, 0 ≤ W_M0 a b j / (12 * (3 * b - a)) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_M0] <;> linarith
  have hW : ∑ j, W_M0 a b j = 12 * (3 * b - a) := by simp [W_M0, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_M0 a b) (12 * (3 * b - a)) hQ hw (0) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_M0, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> linarith) | linarith)
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    first | (norm_num; done) | (field_simp; done) | (field_simp; ring)
  · have hQT : (12 * (3 * b - a)) * ((4 * b - a) / 3) = (48) * b * b + (-28) * a * b + (4) * a * a := by
      ring
    refine flow_obj_le hb hab (RM a b) (rawC_M hb h2 (by linarith)) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_M0, RM] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h5 : (0:ℝ) ≤ 5 * b - 2 * a), mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg (sub_nonneg.2 h5 : (0:ℝ) ≤ 5 * b - 2 * a) (sub_nonneg.2 h5 : (0:ℝ) ≤ 5 * b - 2 * a), hb]

/-! ### `H0M`: band `0`, budget costs at most `(a-b)/3`, on `5b/2 ≤ a ≤ 3b` -/

set_option maxHeartbeats 0 in
theorem flow_H0M (hb : 0 < b) (hab : b < a) (h5 : 5 * b ≤ 2 * a) (h3 : a ≤ 3 * b) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (0)
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ ((a - b) / 3) / (2 * a + 4 * b) := by
  have hQ : (0 : ℝ) < 24 := by linarith
  have hbne : b ≠ 0 := hb.ne'
  have habne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have hw : ∀ j, 0 ≤ W_H0 a b j / (24) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_H0] <;> linarith
  have hW : ∑ j, W_H0 a b j = 24 := by simp [W_H0, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_H0 a b) (24) hQ hw (0) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_H0, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> linarith) | linarith)
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    first | (norm_num; done) | (field_simp; done) | (field_simp; ring)
  · have hQT : (24) * ((a - b) / 3) = (-8) * b + (8) * a := by
      ring
    refine flow_obj_le hb hab (RM a b) (rawC_M hb (by linarith) h3) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_H0, RM] <;> linarith

/-! ### `H0H`: band `0`, budget costs at most `(a-b)/3`, on `3b ≤ a` -/

set_option maxHeartbeats 0 in
theorem flow_H0H (hb : 0 < b) (hab : b < a) (h3 : 3 * b ≤ a) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (0)
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ ((a - b) / 3) / (2 * a + 4 * b) := by
  have hQ : (0 : ℝ) < 24 := by linarith
  have hbne : b ≠ 0 := hb.ne'
  have habne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have hw : ∀ j, 0 ≤ W_H0 a b j / (24) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_H0] <;> linarith
  have hW : ∑ j, W_H0 a b j = 24 := by simp [W_H0, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_H0 a b) (24) hQ hw (0) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_H0, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> linarith) | linarith)
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    first | (norm_num; done) | (field_simp; done) | (field_simp; ring)
  · have hQT : (24) * ((a - b) / 3) = (-8) * b + (8) * a := by
      ring
    refine flow_obj_le hb hab (RH a b) (rawC_H hb h3) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_H0, RH] <;> linarith

/-! ### `Lf`: deviation `1`, budget costs at most `(a-b)/2`, on `a ≤ 2b` -/

set_option maxHeartbeats 0 in
theorem flow_Lf (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (1)
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ ((a - b) / 2) / (2 * a + 4 * b) := by
  have hQ : (0 : ℝ) < 8 := by linarith
  have hbne : b ≠ 0 := hb.ne'
  have habne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have hw : ∀ j, 0 ≤ W_Lf a b j / (8) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_Lf] <;> linarith
  have hW : ∑ j, W_Lf a b j = 8 := by simp [W_Lf, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_Lf a b) (8) hQ hw ((8)) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_Lf, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> linarith) | linarith)
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    first | (norm_num; done) | (field_simp; done) | (field_simp; ring)
  · have hQT : (8) * ((a - b) / 2) = (-4) * b + (4) * a := by
      ring
    refine flow_obj_le hb hab (RL a b) (rawC_L hb hab h2) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_Lf, RL] <;> linarith

/-! ### `M1f`: deviation `1`, budget costs at most `(a-b)(3b-a)/(2b)`, on `2b ≤ a ≤ 7b/3` -/

set_option maxHeartbeats 0 in
theorem flow_M1f (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (1)
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ ((a - b) * (3 * b - a) / (2 * b)) / (2 * a + 4 * b) := by
  have hQ : (0 : ℝ) < 8 * b := by linarith
  have hbne : b ≠ 0 := hb.ne'
  have habne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have hw : ∀ j, 0 ≤ W_M1f a b j / (8 * b) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_M1f] <;> linarith
  have hW : ∑ j, W_M1f a b j = 8 * b := by simp [W_M1f, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_M1f a b) (8 * b) hQ hw ((8) * b) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_M1f, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> linarith) | linarith)
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    first | (norm_num; done) | (field_simp; done) | (field_simp; ring)
  · have hQT : (8 * b) * ((a - b) * (3 * b - a) / (2 * b)) = (-12) * b * b + (16) * a * b + (-4) * a * a := by
      field_simp; ring
    refine flow_obj_le hb hab (RM a b) (rawC_M hb h2 (by linarith)) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_M1f, RM] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), hb]

/-! ### `M23f`: deviation `4(8b-3a)/(11b-3a)`, budget costs at most `2(a-b)(3b-a)/(11b-3a)`, on `7b/3 ≤ a ≤ 13b/5` -/

set_option maxHeartbeats 0 in
theorem flow_M23f (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (4 * (8 * b - 3 * a) / (11 * b - 3 * a))
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ (2 * (a - b) * (3 * b - a) / (11 * b - 3 * a)) / (2 * a + 4 * b) := by
  have hQ : (0 : ℝ) < 4 * (11 * b - 3 * a) := by linarith
  have hbne : b ≠ 0 := hb.ne'
  have habne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have h11 : 11 * b - 3 * a ≠ 0 := by apply ne_of_gt; linarith
  have hw : ∀ j, 0 ≤ W_M23f a b j / (4 * (11 * b - 3 * a)) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_M23f] <;> linarith
  have hW : ∑ j, W_M23f a b j = 4 * (11 * b - 3 * a) := by simp [W_M23f, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_M23f a b) (4 * (11 * b - 3 * a)) hQ hw ((128) * b + (-48) * a) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_M23f, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> linarith) | linarith)
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    first | (norm_num; done) | (field_simp; done) | (field_simp; ring)
  · have hQT : (4 * (11 * b - 3 * a)) * (2 * (a - b) * (3 * b - a) / (11 * b - 3 * a)) = (-24) * b * b + (32) * a * b + (-8) * a * a := by
      field_simp; ring
    refine flow_obj_le hb hab (RM a b) (rawC_M hb (by linarith) (by linarith)) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_M23f, RM] <;> nlinarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), hb]

/-! ### `M4f`: deviation `(5a-11b)/(5(a-b))`, budget costs at most `2b/5`, on `13b/5 ≤ a ≤ 3b` -/

set_option maxHeartbeats 0 in
theorem flow_M4f (hb : 0 < b) (hab : b < a) (h13 : 13 * b ≤ 5 * a) (h3 : a ≤ 3 * b) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F ((5 * a - 11 * b) / (5 * (a - b)))
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ (2 * b / 5) / (2 * a + 4 * b) := by
  have hQ : (0 : ℝ) < 20 * (a - b) := by linarith
  have hbne : b ≠ 0 := hb.ne'
  have habne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have hw : ∀ j, 0 ≤ W_M4f a b j / (20 * (a - b)) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_M4f] <;> linarith
  have hW : ∑ j, W_M4f a b j = 20 * (a - b) := by simp [W_M4f, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_M4f a b) (20 * (a - b)) hQ hw ((-44) * b + (20) * a) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_M4f, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> linarith) | linarith)
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    first | (norm_num; done) | (field_simp; done) | (field_simp; ring)
  · have hQT : (20 * (a - b)) * (2 * b / 5) = (-8) * b * b + (8) * a * b := by
      ring
    refine flow_obj_le hb hab (RM a b) (rawC_M hb (by linarith) h3) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_M4f, RM] <;> nlinarith [mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 5 * a - 13 * b) (sub_nonneg.2 h3 : (0:ℝ) ≤ 3 * b - a), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 5 * a - 13 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 5 * a - 13 * b), mul_nonneg (sub_nonneg.2 h3 : (0:ℝ) ≤ 3 * b - a) (sub_nonneg.2 h3 : (0:ℝ) ≤ 3 * b - a), hb]

/-! ### `Hf`: deviation `2/5`, budget costs at most `(a-b)/5`, on `3b ≤ a` -/

set_option maxHeartbeats 0 in
theorem flow_Hf (hb : 0 < b) (hab : b < a) (h3 : 3 * b ≤ a) :
    ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F (2 / 5)
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ ((a - b) / 5) / (2 * a + 4 * b) := by
  have hQ : (0 : ℝ) < 10 := by linarith
  have hbne : b ≠ 0 := hb.ne'
  have habne : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have hw : ∀ j, 0 ≤ W_Hf a b j / (10) := by
    intro j; apply div_nonneg _ hQ.le; fin_cases j <;> simp [W_Hf] <;> linarith
  have hW : ∑ j, W_Hf a b j = 10 := by simp [W_Hf, Fin.sum_univ_succ] <;> ring
  have hB := flow_band (W_Hf a b) (10) hQ hw ((4)) (by
    intro k τ
    fin_cases k <;> fin_cases τ <;>
      simp [Fin.sum_univ_succ, tq, W_Hf, mult0, mult1, mult2, mult3] <;>
      first | (rw [abs_le]; constructor <;> linarith) | linarith)
  refine ⟨_, flow_feas _ _ hQ hw hW, ?_, fun k hk => ?_⟩
  · convert hB using 1
    first | (norm_num; done) | (field_simp; done) | (field_simp; ring)
  · have hQT : (10) * ((a - b) / 5) = (-2) * b + (2) * a := by
      ring
    refine flow_obj_le hb hab (RH a b) (rawC_H hb h3) _ _ hQ hw _ k ?_
    rw [hQT]
    simp only [K5, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;>
      simp [Fin.sum_univ_succ, tq, W_Hf, RH] <;> linarith

#print axioms sq_mult
#print axioms tq_spec
#print axioms flow_feas
#print axioms flow_obj_le
#print axioms flow_band
#print axioms flow_L0
#print axioms flow_M0
#print axioms flow_H0M
#print axioms flow_H0H
#print axioms flow_Lf
#print axioms flow_M1f
#print axioms flow_M23f
#print axioms flow_M4f
#print axioms flow_Hf

end CIGAMF.P13.PaperCTwoMag1122