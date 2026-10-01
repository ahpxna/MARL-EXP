import «LeanPaperCTwoMag1122BaseV1»

/-!
# Paper C: counts `(1,1,2,2)` — the certificates of the band frontier

Three more certificates for `cert6`, for the lines of the band frontier that are not already in
`LeanPaperCTwoMag1122CertV1`:

| cert | range | lower bound on `D·V_g(η)` |
|---|---|---|
| `C2` | `2b ≤ a ≤ 7b/3` | `(a-b)(3b-a)/(2b) + (1-η)(3b-a)²/(6b)` |
| `CL2` | `7b/3 ≤ a ≤ 13b/5` | `(a-b)(3b-a)(2a - η(3b-a))/(3(15ab-3a²-16b²))` |
| `AM3` | `5b/2 ≤ a ≤ 13b/5` | `(4b-a)/3 - η(a-b)/6` |

`C2` uses the budget weights of `M1f` and a band multiplier `(3b-a)²` on the two `a`-types at
budgets `2, 4`; `CL2` has quadratic weights and a cubic multiplier, so its edge slacks are cubic
forms, and each is checked on the whole range as a nonnegative combination of the four products
`(3a-7b)^i (13b-5a)^(3-i)` (a Bernstein certificate). `AM3` is the certificate `AM` on the next
range. Generated and checked exactly by `scratchpad/c1122f/gcert2.py` and `emit2.py`.
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

/-! ## Certificate `C2`: the middle line `(a-b)(3b-a)/(2b) + (1-η)(3b-a)²/(6b)` on `2b ≤ a ≤ 7b/3` -/

noncomputable def M_C2 (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (3) * b + (-1) * a else if k = 3 then (-2) * b + (2) * a else if k = 4 then (3) * b + (-1) * a else 0

noncomputable def L_C2 (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (9) * b * b + (-6) * a * b + (1) * a * a else if k = 4 then (-9) * b * b + (6) * a * b + (-1) * a * a else 0

noncomputable def P_C2 (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (4) * a * b + (-4/3) * a * a
  | 0, 0, 0, 1 => (4) * a * b + (-4/3) * a * a
  | 0, 0, 0, 2 => (4) * a * b + (-4/3) * a * a
  | 0, 0, 1, 0 => (4) * a * b + (-4/3) * a * a
  | 0, 0, 1, 1 => (4) * a * b + (-4/3) * a * a
  | 0, 0, 1, 2 => (6) * b * b + (-2/3) * a * a
  | 0, 0, 2, 0 => (4) * a * b + (-4/3) * a * a
  | 0, 0, 2, 1 => (6) * b * b + (-2/3) * a * a
  | 0, 0, 2, 2 => (12) * b * b + (-8) * a * b + (4/3) * a * a
  | 0, 1, 0, 0 => (4) * a * b + (-4/3) * a * a
  | 0, 1, 0, 1 => (-6) * b * b + (12) * a * b + (-10/3) * a * a
  | 0, 1, 0, 2 => (-8) * b * b + (10) * a * b + (-2/3) * a * a
  | 0, 1, 1, 0 => (4) * a * b + (-4/3) * a * a
  | 0, 1, 1, 1 => (-10) * b * b + (8) * a * b + (-2/3) * a * a
  | 0, 1, 1, 2 => (6) * b * b + (-2/3) * a * a
  | 0, 1, 2, 0 => (2) * a * b + (-2/3) * a * a
  | 0, 1, 2, 1 => (2) * a * b + (-2/3) * a * a
  | 0, 1, 2, 2 => 0
  | 1, 0, 0, 0 => (4) * a * b + (-4/3) * a * a
  | 1, 0, 0, 1 => (4) * a * b + (-4/3) * a * a
  | 1, 0, 0, 2 => (2) * a * b + (-2/3) * a * a
  | 1, 0, 1, 0 => (-6) * b * b + (12) * a * b + (-10/3) * a * a
  | 1, 0, 1, 1 => (-10) * b * b + (8) * a * b + (-2/3) * a * a
  | 1, 0, 1, 2 => (2) * a * b + (-2/3) * a * a
  | 1, 0, 2, 0 => (-8) * b * b + (10) * a * b + (-2/3) * a * a
  | 1, 0, 2, 1 => (6) * b * b + (-2/3) * a * a
  | 1, 0, 2, 2 => 0
  | 1, 1, 0, 0 => (4) * a * b + (-4/3) * a * a
  | 1, 1, 0, 1 => (-12) * b * b + (12) * a * b + (-8/3) * a * a
  | 1, 1, 0, 2 => (2) * a * b + (-2/3) * a * a
  | 1, 1, 1, 0 => (-12) * b * b + (12) * a * b + (-8/3) * a * a
  | 1, 1, 1, 1 => (-6) * b * b + (4) * a * b + (-2/3) * a * a
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => (2) * a * b + (-2/3) * a * a
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

set_option maxHeartbeats 16000000 in
theorem edge_C2 (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b) :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_C2 a b) (L_C2 a b) (RM a b) (P_C2 a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_C2, L_C2, RM, P_C2] <;> linarith [mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a)])

theorem cert_C2 (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b) (η : ℝ) (hη : 0 ≤ η) :
    (P_C2 a b 0 0 0 0 - η / 3 * (|L_C2 a b 1| + |L_C2 a b 2| + |L_C2 a b 3|
      + |L_C2 a b 4| + |L_C2 a b 5|)) / ((4 * b) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 4 * b := by linarith
  refine cert6 hb hab _ hq (M_C2 a b) (L_C2 a b) (RM a b) (P_C2 a b)
    (by intro k; simp only [M_C2]; split_ifs <;> linarith) (by simp [M_C2]) (by simp [L_C2])
    (by norm_num [M_C2] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [rawC_M hb h2 (by linarith) _ _ _ _ h0 h1 h2' h3'])
    (edge_C2 hb hab h2 h7) (by simp [P_C2]) η hη

/-! ## Certificate `CL2`: the line `(a-b)(3b-a)(2a - η(3b-a))/(3(15ab-3a²-16b²))` on `7b/3 ≤ a ≤ 13b/5` -/

noncomputable def M_CL2 (a b : ℝ) (k : ℕ) : ℝ := if k = 1 then (-12) * b * b + (10) * a * b + (-2) * a * a else if k = 2 then (-3) * b * b + (4) * a * b + (-1) * a * a else if k = 3 then (-2) * b * b + (2) * a * b else if k = 4 then (-3) * b * b + (4) * a * b + (-1) * a * a else if k = 5 then (-12) * b * b + (10) * a * b + (-2) * a * a else 0

noncomputable def L_CL2 (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (-9) * b * b * b + (15) * a * b * b + (-7) * a * a * b + (1) * a * a * a else if k = 4 then (9) * b * b * b + (-15) * a * b * b + (7) * a * a * b + (-1) * a * a * a else 0

noncomputable def P_CL2 (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (-4) * a * b * b + (16/3) * a * a * b + (-4/3) * a * a * a
  | 0, 0, 0, 1 => (-4) * a * b * b + (16/3) * a * a * b + (-4/3) * a * a * a
  | 0, 0, 0, 2 => (-4) * a * b * b + (16/3) * a * a * b + (-4/3) * a * a * a
  | 0, 0, 1, 0 => (-4) * a * b * b + (16/3) * a * a * b + (-4/3) * a * a * a
  | 0, 0, 1, 1 => (-4) * a * b * b + (16/3) * a * a * b + (-4/3) * a * a * a
  | 0, 0, 1, 2 => (-6) * b * b * b + (6) * a * b * b + (2/3) * a * a * b + (-2/3) * a * a * a
  | 0, 0, 2, 0 => (-4) * a * b * b + (16/3) * a * a * b + (-4/3) * a * a * a
  | 0, 0, 2, 1 => (-6) * b * b * b + (6) * a * b * b + (2/3) * a * a * b + (-2/3) * a * a * a
  | 0, 0, 2, 2 => (-2) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 0, 1, 0, 0 => (-4) * a * b * b + (16/3) * a * a * b + (-4/3) * a * a * a
  | 0, 1, 0, 1 => (-6) * b * b * b + (4) * a * b * b + (10/3) * a * a * b + (-4/3) * a * a * a
  | 0, 1, 0, 2 => (-8) * b * b * b + (6) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 0, 1, 1, 0 => (-4) * a * b * b + (16/3) * a * a * b + (-4/3) * a * a * a
  | 0, 1, 1, 1 => (2) * b * b * b + (-6) * a * b * b + (14/3) * a * a * b + (-2/3) * a * a * a
  | 0, 1, 1, 2 => (-6) * b * b * b + (6) * a * b * b + (2/3) * a * a * b + (-2/3) * a * a * a
  | 0, 1, 2, 0 => (-2) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 0, 1, 2, 1 => (-2) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 0, 1, 2, 2 => (12) * b * b * b + (-22) * a * b * b + (12) * a * a * b + (-2) * a * a * a
  | 1, 0, 0, 0 => (-4) * a * b * b + (16/3) * a * a * b + (-4/3) * a * a * a
  | 1, 0, 0, 1 => (-4) * a * b * b + (16/3) * a * a * b + (-4/3) * a * a * a
  | 1, 0, 0, 2 => (-2) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 1, 0, 1, 0 => (-6) * b * b * b + (4) * a * b * b + (10/3) * a * a * b + (-4/3) * a * a * a
  | 1, 0, 1, 1 => (2) * b * b * b + (-6) * a * b * b + (14/3) * a * a * b + (-2/3) * a * a * a
  | 1, 0, 1, 2 => (-2) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 1, 0, 2, 0 => (-8) * b * b * b + (6) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 1, 0, 2, 1 => (-6) * b * b * b + (6) * a * b * b + (2/3) * a * a * b + (-2/3) * a * a * a
  | 1, 0, 2, 2 => (12) * b * b * b + (-22) * a * b * b + (12) * a * a * b + (-2) * a * a * a
  | 1, 1, 0, 0 => (-12) * b * b * b + (18) * a * b * b + (-20/3) * a * a * b + (2/3) * a * a * a
  | 1, 1, 0, 1 => (-2) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 1, 1, 0, 2 => (-2) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 1, 1, 1, 0 => (-2) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 1, 1, 1, 1 => (6) * b * b * b + (-10) * a * b * b + (14/3) * a * a * b + (-2/3) * a * a * a
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => (-2) * a * b * b + (8/3) * a * a * b + (-2/3) * a * a * a
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

set_option maxHeartbeats 16000000 in
theorem edge_CL2 (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b) :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_CL2 a b) (L_CL2 a b) (RM a b) (P_CL2 a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_CL2, L_CL2, RM, P_CL2] <;> linarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b)) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg (mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b)) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)])

theorem cert_CL2 (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b) (η : ℝ) (hη : 0 ≤ η) :
    (P_CL2 a b 0 0 0 0 - η / 3 * (|L_CL2 a b 1| + |L_CL2 a b 2| + |L_CL2 a b 3|
      + |L_CL2 a b 4| + |L_CL2 a b 5|)) / ((2 * (15 * a * b - 3 * a * a - 16 * b * b)) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 2 * (15 * a * b - 3 * a * a - 16 * b * b) := by nlinarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg hb.le (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg hb.le (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_pos hb hb]
  refine cert6 hb hab _ hq (M_CL2 a b) (L_CL2 a b) (RM a b) (P_CL2 a b)
    (by intro k; simp only [M_CL2]; split_ifs <;> nlinarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg hb.le (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg hb.le (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_pos hb hb]) (by simp [M_CL2]) (by simp [L_CL2])
    (by norm_num [M_CL2] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [rawC_M hb (by linarith) (by linarith) _ _ _ _ h0 h1 h2' h3'])
    (edge_CL2 hb hab h7 h13) (by simp [P_CL2]) η hη

/-! ## Certificate `AM3`: the line `(4b-a)/3 - η(a-b)/6` on `5b/2 ≤ a ≤ 13b/5` -/

noncomputable def M_AM3 (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (1) else if k = 3 then (2) else if k = 4 then (1) else 0

noncomputable def L_AM3 (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (-1) * b + (1) * a else if k = 4 then (1) * b + (-1) * a else 0

noncomputable def P_AM3 (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (16/3) * b + (-4/3) * a
  | 0, 0, 0, 1 => (16/3) * b + (-4/3) * a
  | 0, 0, 0, 2 => (16/3) * b + (-4/3) * a
  | 0, 0, 1, 0 => (16/3) * b + (-4/3) * a
  | 0, 0, 1, 1 => (16/3) * b + (-4/3) * a
  | 0, 0, 1, 2 => (14/3) * b + (-2/3) * a
  | 0, 0, 2, 0 => (16/3) * b + (-4/3) * a
  | 0, 0, 2, 1 => (14/3) * b + (-2/3) * a
  | 0, 0, 2, 2 => (-4/3) * b + (4/3) * a
  | 0, 1, 0, 0 => (16/3) * b + (-4/3) * a
  | 0, 1, 0, 1 => (22/3) * b + (-4/3) * a
  | 0, 1, 0, 2 => (32/3) * b + (-2/3) * a
  | 0, 1, 1, 0 => (16/3) * b + (-4/3) * a
  | 0, 1, 1, 1 => (14/3) * b + (-2/3) * a
  | 0, 1, 1, 2 => (2/3) * b + (4/3) * a
  | 0, 1, 2, 0 => (8/3) * b + (-2/3) * a
  | 0, 1, 2, 1 => (-4/3) * b + (4/3) * a
  | 0, 1, 2, 2 => 0
  | 1, 0, 0, 0 => (16/3) * b + (-4/3) * a
  | 1, 0, 0, 1 => (16/3) * b + (-4/3) * a
  | 1, 0, 0, 2 => (8/3) * b + (-2/3) * a
  | 1, 0, 1, 0 => (22/3) * b + (-4/3) * a
  | 1, 0, 1, 1 => (14/3) * b + (-2/3) * a
  | 1, 0, 1, 2 => (-4/3) * b + (4/3) * a
  | 1, 0, 2, 0 => (32/3) * b + (-2/3) * a
  | 1, 0, 2, 1 => (2/3) * b + (4/3) * a
  | 1, 0, 2, 2 => 0
  | 1, 1, 0, 0 => (16/3) * b + (-4/3) * a
  | 1, 1, 0, 1 => (20/3) * b + (-8/3) * a
  | 1, 1, 0, 2 => (8/3) * b + (-2/3) * a
  | 1, 1, 1, 0 => (20/3) * b + (-8/3) * a
  | 1, 1, 1, 1 => (2/3) * b + (-2/3) * a
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => (8/3) * b + (-2/3) * a
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

set_option maxHeartbeats 16000000 in
theorem edge_AM3 (hb : 0 < b) (hab : b < a) (h5 : 5 * b ≤ 2 * a) (h13 : 5 * a ≤ 13 * b) :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_AM3 a b) (L_AM3 a b) (RM a b) (P_AM3 a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_AM3, L_AM3, RM, P_AM3] <;> linarith)

theorem cert_AM3 (hb : 0 < b) (hab : b < a) (h5 : 5 * b ≤ 2 * a) (h13 : 5 * a ≤ 13 * b) (η : ℝ) (hη : 0 ≤ η) :
    (P_AM3 a b 0 0 0 0 - η / 3 * (|L_AM3 a b 1| + |L_AM3 a b 2| + |L_AM3 a b 3|
      + |L_AM3 a b 4| + |L_AM3 a b 5|)) / ((4) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 4 := by norm_num
  refine cert6 hb hab _ hq (M_AM3 a b) (L_AM3 a b) (RM a b) (P_AM3 a b)
    (by intro k; simp only [M_AM3]; split_ifs <;> linarith) (by simp [M_AM3]) (by simp [L_AM3])
    (by norm_num [M_AM3] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [rawC_M hb (by linarith) (by linarith) _ _ _ _ h0 h1 h2' h3'])
    (edge_AM3 hb hab h5 h13) (by simp [P_AM3]) η hη

#print axioms edge_C2
#print axioms cert_C2
#print axioms edge_CL2
#print axioms cert_CL2
#print axioms edge_AM3
#print axioms cert_AM3

end CIGAMF.P13.PaperCTwoMag1122
