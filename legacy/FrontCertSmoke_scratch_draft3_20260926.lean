import «LeanPaperCTwoMag2222CertV1»

/-!
# Paper C: counts `(2,2,2,2)` — the certificate of the line `L3`

`g = (a, a, -a, -a, b, b, -b, -b)`, `D = 4(a+b)`. On `2b ≤ a ≤ 17b/7`, for every `η ≥ 0`,

  `D·V_g(η) ≥ (3b-a)(2(a²-2ab+3b²) - η(a-b)(3b-a)) / (2(a-b)(10b-3a))`   (`lower_L3`).

Budget weights `μ = (2(3b-a)(a-2b), (a-b)(3b-a), 2b(a-b), 2b(3b-a), 2b(3b-a), (a-b)(3b-a),
2(3b-a)(a-2b))` on budgets `1..7`, total `Z = 2(a-b)(10b-3a)`; band multipliers `±2(a-b)(3b-a)²`
on the two heavy types at budgets `2` (upper side) and `6` (lower side). The potentials are an
exact dynamic program (`scratchpad/c2222f/cert3.py`); every edge slack is a cubic form, checked
here on the whole range as a nonnegative combination of `(a-2b)^i (17b-7a)^(3-i)`.
-/

namespace CIGAMF.P13.PaperCTwoMag2222

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFlowCert

variable {a b : ℝ}

noncomputable def μL3 (a b : ℝ) : ℕ → ℝ
  | 1 => (-2 * a^2 + 10 * a * b - 12 * b^2)
  | 2 => (-a^2 + 4 * a * b - 3 * b^2)
  | 3 => (2 * a * b - 2 * b^2)
  | 4 => (-2 * a * b + 6 * b^2)
  | 5 => (-2 * a * b + 6 * b^2)
  | 6 => (-a^2 + 4 * a * b - 3 * b^2)
  | 7 => (-2 * a^2 + 10 * a * b - 12 * b^2)
  | _ => 0

noncomputable def lamL3 (a b : ℝ) : ℝ := (2 * a^3 - 14 * a^2 * b + 30 * a * b^2 - 18 * b^3)

noncomputable def ℓL3 (a b : ℝ) (k : ℕ) (τ : Fin 4) : ℝ :=
  if k = 2 ∧ (τ = 0 ∨ τ = 1) then lamL3 a b else if k = 6 ∧ (τ = 0 ∨ τ = 1) then -lamL3 a b else 0

set_option maxHeartbeats 4000000 in
noncomputable def φL3 (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3)
  | 0, 0, 0, 1 => (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3)
  | 0, 0, 0, 2 => (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3)
  | 0, 0, 1, 0 => (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3)
  | 0, 0, 1, 1 => (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3)
  | 0, 0, 1, 2 => (-a^3 + 3 * a^2 * b - 3 * a * b^2 + 9 * b^3)
  | 0, 0, 2, 0 => (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3)
  | 0, 0, 2, 1 => (-a^3 + 3 * a^2 * b - 3 * a * b^2 + 9 * b^3)
  | 0, 0, 2, 2 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 0, 1, 0, 0 => (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3)
  | 0, 1, 0, 1 => (-2 * a^3 + 8 * a^2 * b - 10 * a * b^2 + 12 * b^3)
  | 0, 1, 0, 2 => (-a^3 + 5 * a^2 * b - 3 * a * b^2 + 7 * b^3)
  | 0, 1, 1, 0 => (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3)
  | 0, 1, 1, 1 => (-a^3 + 7 * a^2 * b - 15 * a * b^2 + 17 * b^3)
  | 0, 1, 1, 2 => (-a^3 + 5 * a^2 * b - 15 * a * b^2 + 27 * b^3)
  | 0, 1, 2, 0 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 0, 1, 2, 1 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 0, 1, 2, 2 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 0, 2, 0, 0 => (-2 * a^3 + 10 * a^2 * b - 14 * a * b^2 + 14 * b^3)
  | 0, 2, 0, 1 => (-a^3 + 9 * a^2 * b - 19 * a * b^2 + 27 * b^3)
  | 0, 2, 0, 2 => (-a^3 + a^2 * b - 7 * a * b^2 + 39 * b^3)
  | 0, 2, 1, 0 => (-a^3 + 9 * a^2 * b - 19 * a * b^2 + 19 * b^3)
  | 0, 2, 1, 1 => (-a^3 + 3 * a^2 * b - 7 * a * b^2 + 21 * b^3)
  | 0, 2, 1, 2 => (-a^3 + a^2 * b + a * b^2 + 15 * b^3)
  | 0, 2, 2, 0 => (-a^3 + a^2 * b + 9 * a * b^2 - 9 * b^3)
  | 0, 2, 2, 1 => (-a^3 + 3 * a^2 * b - 3 * a * b^2 + 9 * b^3)
  | 0, 2, 2, 2 => (-3 * a^3 + 13 * a^2 * b - 13 * a * b^2 + 3 * b^3)
  | 1, 0, 0, 0 => (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3)
  | 1, 0, 0, 1 => (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3)
  | 1, 0, 0, 2 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 1, 0, 1, 0 => (-2 * a^3 + 8 * a^2 * b - 10 * a * b^2 + 12 * b^3)
  | 1, 0, 1, 1 => (-a^3 + 7 * a^2 * b - 15 * a * b^2 + 17 * b^3)
  | 1, 0, 1, 2 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 1, 0, 2, 0 => (-a^3 + 5 * a^2 * b - 3 * a * b^2 + 7 * b^3)
  | 1, 0, 2, 1 => (-a^3 + 5 * a^2 * b - 15 * a * b^2 + 27 * b^3)
  | 1, 0, 2, 2 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 1, 1, 0, 0 => (-2 * a^2 * b + 4 * a * b^2 + 6 * b^3)
  | 1, 1, 0, 1 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 1, 1, 0, 2 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 1, 1, 1, 0 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 1, 1, 1, 1 => (-a^3 + 7 * a^2 * b - 19 * a * b^2 + 21 * b^3)
  | 1, 1, 1, 2 => (-a^3 + 7 * a^2 * b - 19 * a * b^2 + 21 * b^3)
  | 1, 1, 2, 0 => (-a^3 + 5 * a^2 * b - 11 * a * b^2 + 15 * b^3)
  | 1, 1, 2, 1 => (-a^3 + 7 * a^2 * b - 19 * a * b^2 + 21 * b^3)
  | 1, 1, 2, 2 => (-a^3 + 5 * a^2 * b - 7 * a * b^2 + 3 * b^3)
  | 1, 2, 0, 0 => (-a^3 + 9 * a^2 * b - 23 * a * b^2 + 23 * b^3)
  | 1, 2, 0, 1 => (-a^3 + 7 * a^2 * b - 23 * a * b^2 + 33 * b^3)
  | 1, 2, 0, 2 => (-a^3 + 5 * a^2 * b - 15 * a * b^2 + 27 * b^3)
  | 1, 2, 1, 0 => (-a^3 + 7 * a^2 * b - 19 * a * b^2 + 21 * b^3)
  | 1, 2, 1, 1 => (-a^3 + 7 * a^2 * b - 19 * a * b^2 + 21 * b^3)
  | 1, 2, 1, 2 => (-a^3 + 3 * a^2 * b + a * b^2 - 3 * b^3)
  | 1, 2, 2, 0 => (-a^3 + 5 * a^2 * b - 7 * a * b^2 + 3 * b^3)
  | 1, 2, 2, 1 => (-a^3 + 5 * a^2 * b - 7 * a * b^2 + 3 * b^3)
  | 1, 2, 2, 2 => (-2 * a^3 + 12 * a^2 * b - 22 * a * b^2 + 12 * b^3)
  | 2, 0, 0, 0 => (-2 * a^3 + 10 * a^2 * b - 14 * a * b^2 + 14 * b^3)
  | 2, 0, 0, 1 => (-a^3 + 9 * a^2 * b - 19 * a * b^2 + 19 * b^3)
  | 2, 0, 0, 2 => (-a^3 + a^2 * b + 9 * a * b^2 - 9 * b^3)
  | 2, 0, 1, 0 => (-a^3 + 9 * a^2 * b - 19 * a * b^2 + 27 * b^3)
  | 2, 0, 1, 1 => (-a^3 + 3 * a^2 * b - 7 * a * b^2 + 21 * b^3)
  | 2, 0, 1, 2 => (-a^3 + 3 * a^2 * b - 3 * a * b^2 + 9 * b^3)
  | 2, 0, 2, 0 => (-a^3 + a^2 * b - 7 * a * b^2 + 39 * b^3)
  | 2, 0, 2, 1 => (-a^3 + a^2 * b + a * b^2 + 15 * b^3)
  | 2, 0, 2, 2 => (-3 * a^3 + 13 * a^2 * b - 13 * a * b^2 + 3 * b^3)
  | 2, 1, 0, 0 => (-a^3 + 9 * a^2 * b - 23 * a * b^2 + 23 * b^3)
  | 2, 1, 0, 1 => (-a^3 + 7 * a^2 * b - 19 * a * b^2 + 21 * b^3)
  | 2, 1, 0, 2 => (-a^3 + 5 * a^2 * b - 7 * a * b^2 + 3 * b^3)
  | 2, 1, 1, 0 => (-a^3 + 7 * a^2 * b - 23 * a * b^2 + 33 * b^3)
  | 2, 1, 1, 1 => (-a^3 + 7 * a^2 * b - 19 * a * b^2 + 21 * b^3)
  | 2, 1, 1, 2 => (-a^3 + 5 * a^2 * b - 7 * a * b^2 + 3 * b^3)
  | 2, 1, 2, 0 => (-a^3 + 5 * a^2 * b - 15 * a * b^2 + 27 * b^3)
  | 2, 1, 2, 1 => (-a^3 + 3 * a^2 * b + a * b^2 - 3 * b^3)
  | 2, 1, 2, 2 => (-2 * a^3 + 12 * a^2 * b - 22 * a * b^2 + 12 * b^3)
  | 2, 2, 0, 0 => (-a^3 + 9 * a^2 * b - 27 * a * b^2 + 27 * b^3)
  | 2, 2, 0, 1 => (-a^3 + 9 * a^2 * b - 27 * a * b^2 + 27 * b^3)
  | 2, 2, 0, 2 => (-a^3 + 5 * a^2 * b - 7 * a * b^2 + 3 * b^3)
  | 2, 2, 1, 0 => (-a^3 + 9 * a^2 * b - 27 * a * b^2 + 27 * b^3)
  | 2, 2, 1, 1 => (-a^3 + 7 * a^2 * b - 15 * a * b^2 + 9 * b^3)
  | 2, 2, 1, 2 => (0)
  | 2, 2, 2, 0 => (-a^3 + 5 * a^2 * b - 7 * a * b^2 + 3 * b^3)
  | 2, 2, 2, 1 => (0)
  | 2, 2, 2, 2 => (0)
  | _, _, _, _ => 0

set_option maxHeartbeats 16000000 in
theorem edge_L3_0 (hb : 0 < b) (h2 : 2 * b ≤ a) (h17 : 7 * a ≤ 17 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 < 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φL3 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μL3 a b) (ℓL3 a b) v0 v1 v2 v3 + φL3 a b (v0 + 1) v1 v2 v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 (by omega) h1 h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φL3, μL3, ℓL3, lamL3, βmid] <;> linarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b)) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg (mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b)) (sub_nonneg.2 h17 : (0:ℝ) ≤ 17 * b - 7 * a), mul_nonneg (mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h17 : (0:ℝ) ≤ 17 * b - 7 * a)) (sub_nonneg.2 h17 : (0:ℝ) ≤ 17 * b - 7 * a), mul_nonneg (mul_nonneg (sub_nonneg.2 h17 : (0:ℝ) ≤ 17 * b - 7 * a) (sub_nonneg.2 h17 : (0:ℝ) ≤ 17 * b - 7 * a)) (sub_nonneg.2 h17 : (0:ℝ) ≤ 17 * b - 7 * a)]

theorem edge_L3_1 (hb : 0 < b) (h2 : 2 * b ≤ a) (h17 : 7 * a ≤ 17 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 < 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φL3 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μL3 a b) (ℓL3 a b) v0 v1 v2 v3 + φL3 a b v0 (v1 + 1) v2 v3 := by
  sorry

theorem edge_L3_2 (hb : 0 < b) (h2 : 2 * b ≤ a) (h17 : 7 * a ≤ 17 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 < 2) (h3' : v3 ≤ 2) :
    φL3 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μL3 a b) (ℓL3 a b) v0 v1 v2 v3 + φL3 a b v0 v1 (v2 + 1) v3 := by
  sorry

theorem edge_L3_3 (hb : 0 < b) (h2 : 2 * b ≤ a) (h17 : 7 * a ≤ 17 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 < 2) :
    φL3 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μL3 a b) (ℓL3 a b) v0 v1 v2 v3 + φL3 a b v0 v1 v2 (v3 + 1) := by
  sorry

theorem edge_L3 (hb : 0 < b) (h2 : 2 * b ≤ a) (h17 : 7 * a ≤ 17 * b) :
    EdgeOK a b (βmid a b) (μL3 a b) (ℓL3 a b) (φL3 a b) := by
  intro v0 v1 v2 v3 e0 e1 e2 e3
  exact ⟨fun h => edge_L3_0 hb h2 h17 v0 v1 v2 v3 h e1 e2 e3, fun h => edge_L3_1 hb h2 h17 v0 v1 v2 v3 e0 h e2 e3,
    fun h => edge_L3_2 hb h2 h17 v0 v1 v2 v3 e0 e1 h e3, fun h => edge_L3_3 hb h2 h17 v0 v1 v2 v3 e0 e1 e2 h⟩

theorem μL3_nonneg (hb : 0 < b) (h2 : 2 * b ≤ a) (h17 : 7 * a ≤ 17 * b) : ∀ k, 0 ≤ μL3 a b k := by
  intro k; unfold μL3; split <;> first | norm_num | nlinarith [mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h17 : (0:ℝ) ≤ 17 * b - 7 * a), mul_nonneg hb.le (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg hb.le (sub_nonneg.2 h17 : (0:ℝ) ≤ 17 * b - 7 * a), mul_pos hb hb, mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg (sub_nonneg.2 h17 : (0:ℝ) ≤ 17 * b - 7 * a) (sub_nonneg.2 h17 : (0:ℝ) ≤ 17 * b - 7 * a)]

theorem lamL3_nonneg (hb : 0 < b) (h2 : 2 * b ≤ a) : 0 ≤ lamL3 a b := by
  have : lamL3 a b = 2 * (a - b) * (3 * b - a) ^ 2 := by unfold lamL3; ring
  rw [this]; exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg _)

theorem ℓL3_sum (hb : 0 < b) (h2 : 2 * b ≤ a) :
    ∑ k ∈ range 8, ∑ τ, |ℓL3 a b k τ| = 4 * lamL3 a b := by
  have hl := lamL3_nonneg hb h2
  simp [ℓL3, Finset.sum_range_succ, Fin.sum_univ_four, abs_neg, abs_of_nonneg hl]
  ring

/-- **The line `L3`.** On `2b ≤ a ≤ 17b/7`, for every band `η ≥ 0`. -/
theorem lower_L3 (hb : 0 < b) (h2 : 2 * b ≤ a) (h17 : 7 * a ≤ 17 * b) (η : ℝ) (hη : 0 ≤ η) :
    (3 * b - a) * (2 * (a ^ 2 - 2 * a * b + 3 * b ^ 2) - η * (a - b) * (3 * b - a))
        / (2 * (a - b) * (10 * b - 3 * a)) / (4 * (a + b))
      ≤ trueValue (g8 a b) η K7 K7_ne := by
  have hab : b < a := by linarith
  have hZ : (0 : ℝ) < 2 * (a - b) * (10 * b - 3 * a) :=
    mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)
  have h := cert8 hb hab _ hZ (βmid a b) (μL3 a b) (ℓL3 a b) (φL3 a b) (μL3_nonneg hb h2 h17)
    (by simp [μL3]) (by simp [μL3]; ring) (fun k hk _ => βmid_eq hb h2 (by linarith) k hk)
    (edge_L3 hb h2 h17) (by simp [φL3]) η hη
  have e0 : φL3 a b 0 0 0 0 = (-2 * a^3 + 10 * a^2 * b - 18 * a * b^2 + 18 * b^3) := by simp [φL3]
  rw [e0, ℓL3_sum hb h2] at h
  refine le_trans (le_of_eq ?_) h
  have hD : 4 * (a + b) ≠ 0 := by apply ne_of_gt; linarith
  have hZ' : 2 * (a - b) * (10 * b - 3 * a) ≠ 0 := hZ.ne'
  rw [div_div, div_eq_div_iff (mul_ne_zero hZ' hD) (mul_ne_zero hZ' hD)]
  unfold lamL3
  ring

#print axioms edge_L3
#print axioms lower_L3

end CIGAMF.P13.PaperCTwoMag2222
