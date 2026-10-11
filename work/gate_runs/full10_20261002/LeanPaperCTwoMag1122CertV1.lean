import «LeanPaperCTwoMag1122BaseV1»

/-!
# Paper C: counts `(1,1,2,2)` — the dual certificates

Eight certificates for `cert6` (`LeanPaperCTwoMag1122BaseV1`), each with budget weights `M`, band
multipliers `L` on the two `a`-types and potentials `P` on the 36 count states, all polynomial in
`a, b`. Each edge inequality is checked on its ratio range by `linarith`; for the two
certificates with weights linear in `a/b` (`M1f`, `M23f`) the edge slacks are quadratic forms and
the check uses the three products of the range constraints (a Bernstein certificate), so it holds
on the whole range, not at sample points.

The generated tables come from `scratchpad/c1122/gencert.py`, which also checks every edge exactly
in rational arithmetic before emitting.

| cert | range | lower bound on `D·V_g(η)` |
|---|---|---|
| `AL` | `a ≤ 2b` | `(a-b)(2/3 - η/6)` |
| `AM` | `2b ≤ a ≤ 5b/2` | `(4b-a)/3 - η(a-b)/6` |
| `Band` | every ratio | `(a-b)(1-η)/3` |
| `Lf` | `a ≤ 2b` | `(a-b)/2` |
| `M1f` | `2b ≤ a ≤ 7b/3` | `(a-b)(3b-a)/(2b)` |
| `M23f` | `7b/3 ≤ a ≤ 13b/5` | `2(a-b)(3b-a)/(11b-3a)` |
| `M4f` | `13b/5 ≤ a ≤ 3b` | `2b/5` |
| `Hf` | `3b ≤ a` | `(a-b)/5` |
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

/-! ## Certificate `AL`: the line `(a-b)(2/3 - η/6)` on `a ≤ 2b` -/

noncomputable def M_AL (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (1) else if k = 3 then (2) else if k = 4 then (1) else 0

noncomputable def L_AL (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (-1) * b + (1) * a else if k = 4 then (1) * b + (-1) * a else 0

noncomputable def P_AL (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (-8/3) * b + (8/3) * a
  | 0, 0, 0, 1 => (-8/3) * b + (8/3) * a
  | 0, 0, 0, 2 => (4/3) * b + (2/3) * a
  | 0, 0, 1, 0 => (-8/3) * b + (8/3) * a
  | 0, 0, 1, 1 => (-8/3) * b + (8/3) * a
  | 0, 0, 1, 2 => (-10/3) * b + (10/3) * a
  | 0, 0, 2, 0 => (4/3) * b + (2/3) * a
  | 0, 0, 2, 1 => (-10/3) * b + (10/3) * a
  | 0, 0, 2, 2 => (-4/3) * b + (4/3) * a
  | 0, 1, 0, 0 => (-8/3) * b + (8/3) * a
  | 0, 1, 0, 1 => (-2/3) * b + (8/3) * a
  | 0, 1, 0, 2 => (8/3) * b + (10/3) * a
  | 0, 1, 1, 0 => (-8/3) * b + (8/3) * a
  | 0, 1, 1, 1 => (-10/3) * b + (10/3) * a
  | 0, 1, 1, 2 => (2/3) * b + (4/3) * a
  | 0, 1, 2, 0 => (-4/3) * b + (4/3) * a
  | 0, 1, 2, 1 => (-4/3) * b + (4/3) * a
  | 0, 1, 2, 2 => 0
  | 1, 0, 0, 0 => (-8/3) * b + (8/3) * a
  | 1, 0, 0, 1 => (-8/3) * b + (8/3) * a
  | 1, 0, 0, 2 => (-4/3) * b + (4/3) * a
  | 1, 0, 1, 0 => (-2/3) * b + (8/3) * a
  | 1, 0, 1, 1 => (-10/3) * b + (10/3) * a
  | 1, 0, 1, 2 => (-4/3) * b + (4/3) * a
  | 1, 0, 2, 0 => (8/3) * b + (10/3) * a
  | 1, 0, 2, 1 => (2/3) * b + (4/3) * a
  | 1, 0, 2, 2 => 0
  | 1, 1, 0, 0 => (-8/3) * b + (8/3) * a
  | 1, 1, 0, 1 => (-4/3) * b + (4/3) * a
  | 1, 1, 0, 2 => (8/3) * b + (-2/3) * a
  | 1, 1, 1, 0 => (-4/3) * b + (4/3) * a
  | 1, 1, 1, 1 => (2/3) * b + (-2/3) * a
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => (8/3) * b + (-2/3) * a
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_AL (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_AL a b) (L_AL a b) (RL a b) (P_AL a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_AL, L_AL, RL, P_AL] <;> linarith)

theorem cert_AL (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (η : ℝ) (hη : 0 ≤ η) :
    (P_AL a b 0 0 0 0 - η / 3 * (|L_AL a b 1| + |L_AL a b 2| + |L_AL a b 3|
      + |L_AL a b 4| + |L_AL a b 5|)) / ((4) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 4 := by linarith
  refine cert6 hb hab _ hq (M_AL a b) (L_AL a b) (RL a b) (P_AL a b)
    (by intro k; simp only [M_AL]; split_ifs <;> linarith) (by simp [M_AL]) (by simp [L_AL]) (by norm_num [M_AL] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [rawC_L hb hab h2 _ _ _ _ h0 h1 h2' h3'])
    (edge_AL hb hab h2) (by simp [P_AL]) η hη

/-! ## Certificate `AM`: the line `(4b-a)/3 - η(a-b)/6` on `2b ≤ a ≤ 5b/2` -/

noncomputable def M_AM (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (1) else if k = 3 then (2) else if k = 4 then (1) else 0

noncomputable def L_AM (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (-1) * b + (1) * a else if k = 4 then (1) * b + (-1) * a else 0

noncomputable def P_AM (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
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

set_option maxHeartbeats 8000000 in
theorem edge_AM (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h5 : 2 * a ≤ 5 * b) :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_AM a b) (L_AM a b) (RM a b) (P_AM a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_AM, L_AM, RM, P_AM] <;> linarith)

theorem cert_AM (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h5 : 2 * a ≤ 5 * b) (η : ℝ) (hη : 0 ≤ η) :
    (P_AM a b 0 0 0 0 - η / 3 * (|L_AM a b 1| + |L_AM a b 2| + |L_AM a b 3|
      + |L_AM a b 4| + |L_AM a b 5|)) / ((4) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 4 := by linarith
  refine cert6 hb hab _ hq (M_AM a b) (L_AM a b) (RM a b) (P_AM a b)
    (by intro k; simp only [M_AM]; split_ifs <;> linarith) (by simp [M_AM]) (by simp [L_AM]) (by norm_num [M_AM] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [rawC_M hb h2 (by linarith) _ _ _ _ h0 h1 h2' h3'])
    (edge_AM hb hab h2 h5) (by simp [P_AM]) η hη

/-! ## Certificate `Band`: the band line `(a-b)(1-η)/3` at every ratio -/

noncomputable def M_Band (a b : ℝ) (k : ℕ) : ℝ := if k = 1 then (1) else if k = 5 then (1) else 0

noncomputable def L_Band (a b : ℝ) (k : ℕ) : ℝ := if k = 1 then (1) * b + (-1) * a else if k = 5 then (-1) * b + (1) * a else 0

noncomputable def P_Band (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (-2/3) * b + (2/3) * a
  | 0, 0, 0, 1 => (-2/3) * b + (2/3) * a
  | 0, 0, 0, 2 => (-1/3) * b + (1/3) * a
  | 0, 0, 1, 0 => (-2/3) * b + (2/3) * a
  | 0, 0, 1, 1 => (-1/3) * b + (1/3) * a
  | 0, 0, 1, 2 => (-1/3) * b + (1/3) * a
  | 0, 0, 2, 0 => (-1/3) * b + (1/3) * a
  | 0, 0, 2, 1 => (-1/3) * b + (1/3) * a
  | 0, 0, 2, 2 => (-1/3) * b + (1/3) * a
  | 0, 1, 0, 0 => (-2/3) * b + (2/3) * a
  | 0, 1, 0, 1 => (-1/3) * b + (1/3) * a
  | 0, 1, 0, 2 => (-1/3) * b + (1/3) * a
  | 0, 1, 1, 0 => (-1/3) * b + (1/3) * a
  | 0, 1, 1, 1 => (-1/3) * b + (1/3) * a
  | 0, 1, 1, 2 => (-1/3) * b + (1/3) * a
  | 0, 1, 2, 0 => (-1/3) * b + (1/3) * a
  | 0, 1, 2, 1 => (-1/3) * b + (1/3) * a
  | 0, 1, 2, 2 => (-1/3) * b + (1/3) * a
  | 1, 0, 0, 0 => (-2/3) * b + (2/3) * a
  | 1, 0, 0, 1 => (-1/3) * b + (1/3) * a
  | 1, 0, 0, 2 => (-1/3) * b + (1/3) * a
  | 1, 0, 1, 0 => (-1/3) * b + (1/3) * a
  | 1, 0, 1, 1 => (-1/3) * b + (1/3) * a
  | 1, 0, 1, 2 => (-1/3) * b + (1/3) * a
  | 1, 0, 2, 0 => (-1/3) * b + (1/3) * a
  | 1, 0, 2, 1 => (-1/3) * b + (1/3) * a
  | 1, 0, 2, 2 => (-1/3) * b + (1/3) * a
  | 1, 1, 0, 0 => (-1/3) * b + (1/3) * a
  | 1, 1, 0, 1 => (-1/3) * b + (1/3) * a
  | 1, 1, 0, 2 => (-1/3) * b + (1/3) * a
  | 1, 1, 1, 0 => (-1/3) * b + (1/3) * a
  | 1, 1, 1, 1 => (-1/3) * b + (1/3) * a
  | 1, 1, 1, 2 => (-1/3) * b + (1/3) * a
  | 1, 1, 2, 0 => (-1/3) * b + (1/3) * a
  | 1, 1, 2, 1 => (-1/3) * b + (1/3) * a
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_Band (hb : 0 < b) (hab : b < a)  :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_Band a b) (L_Band a b) (RL a b) (P_Band a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_Band, L_Band, RL, P_Band] <;> linarith)

theorem cert_Band (hb : 0 < b) (hab : b < a)  (η : ℝ) (hη : 0 ≤ η) :
    (P_Band a b 0 0 0 0 - η / 3 * (|L_Band a b 1| + |L_Band a b 2| + |L_Band a b 3|
      + |L_Band a b 4| + |L_Band a b 5|)) / ((2) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 2 := by linarith
  refine cert6 hb hab _ hq (M_Band a b) (L_Band a b) (RL a b) (P_Band a b)
    (by intro k; simp only [M_Band]; split_ifs <;> linarith) (by simp [M_Band]) (by simp [L_Band]) (by norm_num [M_Band] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    by_cases hk : x0 + x1 + x2 + x3 = 3
    · rw [hk]; simp [M_Band]
    · rw [rawC_off3 hb hab _ _ _ _ h0 h1 h2' h3' hk])
    (edge_Band hb hab ) (by simp [P_Band]) η hη

/-! ## Certificate `Lf`: the free value `(a-b)/2` on `a ≤ 2b` -/

noncomputable def M_Lf (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (1) else if k = 3 then (2) else if k = 4 then (1) else 0

noncomputable def L_Lf (a b : ℝ) (k : ℕ) : ℝ := 0

noncomputable def P_Lf (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (-2) * b + (2) * a
  | 0, 0, 0, 1 => (-2) * b + (2) * a
  | 0, 0, 0, 2 => (1) * b + (1) * a
  | 0, 0, 1, 0 => (-2) * b + (2) * a
  | 0, 0, 1, 1 => (-2) * b + (2) * a
  | 0, 0, 1, 2 => (-2) * b + (2) * a
  | 0, 0, 2, 0 => (1) * b + (1) * a
  | 0, 0, 2, 1 => (-2) * b + (2) * a
  | 0, 0, 2, 2 => 0
  | 0, 1, 0, 0 => (-2) * b + (2) * a
  | 0, 1, 0, 1 => (-1) * b + (3) * a
  | 0, 1, 0, 2 => (2) * b + (4) * a
  | 0, 1, 1, 0 => (-2) * b + (2) * a
  | 0, 1, 1, 1 => (-4) * b + (4) * a
  | 0, 1, 1, 2 => (1) * b + (1) * a
  | 0, 1, 2, 0 => (-1) * b + (1) * a
  | 0, 1, 2, 1 => (-1) * b + (1) * a
  | 0, 1, 2, 2 => 0
  | 1, 0, 0, 0 => (-2) * b + (2) * a
  | 1, 0, 0, 1 => (-2) * b + (2) * a
  | 1, 0, 0, 2 => (-1) * b + (1) * a
  | 1, 0, 1, 0 => (-1) * b + (3) * a
  | 1, 0, 1, 1 => (-4) * b + (4) * a
  | 1, 0, 1, 2 => (-1) * b + (1) * a
  | 1, 0, 2, 0 => (2) * b + (4) * a
  | 1, 0, 2, 1 => (1) * b + (1) * a
  | 1, 0, 2, 2 => 0
  | 1, 1, 0, 0 => (-2) * b + (2) * a
  | 1, 1, 0, 1 => (-2) * b + (2) * a
  | 1, 1, 0, 2 => (2) * b
  | 1, 1, 1, 0 => (-2) * b + (2) * a
  | 1, 1, 1, 1 => 0
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => (2) * b
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_Lf (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_Lf a b) (L_Lf a b) (RL a b) (P_Lf a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_Lf, L_Lf, RL, P_Lf] <;> linarith)

theorem cert_Lf (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (η : ℝ) (hη : 0 ≤ η) :
    (P_Lf a b 0 0 0 0 - η / 3 * (|L_Lf a b 1| + |L_Lf a b 2| + |L_Lf a b 3|
      + |L_Lf a b 4| + |L_Lf a b 5|)) / ((4) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 4 := by linarith
  refine cert6 hb hab _ hq (M_Lf a b) (L_Lf a b) (RL a b) (P_Lf a b)
    (by intro k; simp only [M_Lf]; split_ifs <;> linarith) (by simp [M_Lf]) (by simp [L_Lf]) (by norm_num [M_Lf] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [rawC_L hb hab h2 _ _ _ _ h0 h1 h2' h3'])
    (edge_Lf hb hab h2) (by simp [P_Lf]) η hη

/-! ## Certificate `M1f`: the free value `(a-b)(3b-a)/(2b)` on `2b ≤ a ≤ 7b/3` -/

noncomputable def M_M1f (a b : ℝ) (k : ℕ) : ℝ := if k = 2 then (3) * b + (-1) * a else if k = 3 then (-2) * b + (2) * a else if k = 4 then (3) * b + (-1) * a else 0

noncomputable def L_M1f (a b : ℝ) (k : ℕ) : ℝ := 0

noncomputable def P_M1f (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 0, 1 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 0, 2 => (3) * b * b + (2) * a * b + (-1) * a * a
  | 0, 0, 1, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 1, 1 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 1, 2 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 2, 0 => (3) * b * b + (2) * a * b + (-1) * a * a
  | 0, 0, 2, 1 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 2, 2 => 0
  | 0, 1, 0, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 1, 0, 1 => (-3) * b * b + (10) * a * b + (-3) * a * a
  | 0, 1, 0, 2 => (-2) * b * b + (6) * a * b
  | 0, 1, 1, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 1, 1, 1 => (-4) * b * b + (4) * a * b
  | 0, 1, 1, 2 => (3) * b * b + (2) * a * b + (-1) * a * a
  | 0, 1, 2, 0 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 0, 1, 2, 1 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 0, 1, 2, 2 => 0
  | 1, 0, 0, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 1, 0, 0, 1 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 1, 0, 0, 2 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 1, 0, 1, 0 => (-3) * b * b + (10) * a * b + (-3) * a * a
  | 1, 0, 1, 1 => (-4) * b * b + (4) * a * b
  | 1, 0, 1, 2 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 1, 0, 2, 0 => (-2) * b * b + (6) * a * b
  | 1, 0, 2, 1 => (3) * b * b + (2) * a * b + (-1) * a * a
  | 1, 0, 2, 2 => 0
  | 1, 1, 0, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 1, 1, 0, 1 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 1, 1, 0, 2 => (6) * b * b + (-2) * a * b
  | 1, 1, 1, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 1, 1, 1, 1 => 0
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => (6) * b * b + (-2) * a * b
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_M1f (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b) :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_M1f a b) (L_M1f a b) (RM a b) (P_M1f a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_M1f, L_M1f, RM, P_M1f] <;> linarith [mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a), mul_nonneg (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b) (sub_nonneg.2 h2 : (0:ℝ) ≤ a - 2 * b), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a) (sub_nonneg.2 h7 : (0:ℝ) ≤ 7 * b - 3 * a)])

theorem cert_M1f (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b) (η : ℝ) (hη : 0 ≤ η) :
    (P_M1f a b 0 0 0 0 - η / 3 * (|L_M1f a b 1| + |L_M1f a b 2| + |L_M1f a b 3|
      + |L_M1f a b 4| + |L_M1f a b 5|)) / ((4 * b) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 4 * b := by linarith
  refine cert6 hb hab _ hq (M_M1f a b) (L_M1f a b) (RM a b) (P_M1f a b)
    (by intro k; simp only [M_M1f]; split_ifs <;> linarith) (by simp [M_M1f]) (by simp [L_M1f]) (by norm_num [M_M1f] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [rawC_M hb h2 (by linarith) _ _ _ _ h0 h1 h2' h3'])
    (edge_M1f hb hab h2 h7) (by simp [P_M1f]) η hη

/-! ## Certificate `M23f`: the free value `2(a-b)(3b-a)/(11b-3a)` on `7b/3 ≤ a ≤ 13b/5` -/

noncomputable def M_M23f (a b : ℝ) (k : ℕ) : ℝ := if k = 1 then (3) * b + (-1) * a else if k = 2 then (3) * b + (-1) * a else if k = 3 then (-1) * b + (1) * a else if k = 4 then (3) * b + (-1) * a else if k = 5 then (3) * b + (-1) * a else 0

noncomputable def L_M23f (a b : ℝ) (k : ℕ) : ℝ := 0

noncomputable def P_M23f (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 0, 1 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 0, 2 => (3) * b * b + (2) * a * b + (-1) * a * a
  | 0, 0, 1, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 1, 1 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 1, 2 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 2, 0 => (3) * b * b + (2) * a * b + (-1) * a * a
  | 0, 0, 2, 1 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 0, 2, 2 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 0, 1, 0, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 1, 0, 1 => (6) * a * b + (-2) * a * a
  | 0, 1, 0, 2 => (2) * b * b + (2) * a * b
  | 0, 1, 1, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 0, 1, 1, 1 => (-2) * b * b + (2) * a * b
  | 0, 1, 1, 2 => (3) * b * b + (2) * a * b + (-1) * a * a
  | 0, 1, 2, 0 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 0, 1, 2, 1 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 0, 1, 2, 2 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 1, 0, 0, 0 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 1, 0, 0, 1 => (-6) * b * b + (8) * a * b + (-2) * a * a
  | 1, 0, 0, 2 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 1, 0, 1, 0 => (6) * a * b + (-2) * a * a
  | 1, 0, 1, 1 => (-2) * b * b + (2) * a * b
  | 1, 0, 1, 2 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 1, 0, 2, 0 => (2) * b * b + (2) * a * b
  | 1, 0, 2, 1 => (3) * b * b + (2) * a * b + (-1) * a * a
  | 1, 0, 2, 2 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 1, 1, 0, 0 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 1, 1, 0, 1 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 1, 1, 0, 2 => (6) * b * b + (-2) * a * b
  | 1, 1, 1, 0 => (-3) * b * b + (4) * a * b + (-1) * a * a
  | 1, 1, 1, 1 => 0
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => (6) * b * b + (-2) * a * b
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_M23f (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b) :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_M23f a b) (L_M23f a b) (RM a b) (P_M23f a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_M23f, L_M23f, RM, P_M23f] <;> linarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a), mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b), mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a)])

theorem cert_M23f (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b) (η : ℝ) (hη : 0 ≤ η) :
    (P_M23f a b 0 0 0 0 - η / 3 * (|L_M23f a b 1| + |L_M23f a b 2| + |L_M23f a b 3|
      + |L_M23f a b 4| + |L_M23f a b 5|)) / ((11 * b - 3 * a) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 11 * b - 3 * a := by linarith
  refine cert6 hb hab _ hq (M_M23f a b) (L_M23f a b) (RM a b) (P_M23f a b)
    (by intro k; simp only [M_M23f]; split_ifs <;> linarith) (by simp [M_M23f]) (by simp [L_M23f]) (by norm_num [M_M23f] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [rawC_M hb (by linarith) (by linarith) _ _ _ _ h0 h1 h2' h3'])
    (edge_M23f hb hab h7 h13) (by simp [P_M23f]) η hη

/-! ## Certificate `M4f`: the free value `2b/5` on `13b/5 ≤ a ≤ 3b` -/

noncomputable def M_M4f (a b : ℝ) (k : ℕ) : ℝ := if k = 1 then (1) else if k = 2 then (1) else if k = 3 then (1) else if k = 4 then (1) else if k = 5 then (1) else 0

noncomputable def L_M4f (a b : ℝ) (k : ℕ) : ℝ := 0

noncomputable def P_M4f (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (2) * b
  | 0, 0, 0, 1 => (2) * b
  | 0, 0, 0, 2 => (1) * b + (1) * a
  | 0, 0, 1, 0 => (2) * b
  | 0, 0, 1, 1 => (2) * b
  | 0, 0, 1, 2 => (2) * b
  | 0, 0, 2, 0 => (1) * b + (1) * a
  | 0, 0, 2, 1 => (2) * b
  | 0, 0, 2, 2 => (-1) * b + (1) * a
  | 0, 1, 0, 0 => (2) * b
  | 0, 1, 0, 1 => (4) * b
  | 0, 1, 0, 2 => (6) * b
  | 0, 1, 1, 0 => (2) * b
  | 0, 1, 1, 1 => (2) * b
  | 0, 1, 1, 2 => (1) * b + (1) * a
  | 0, 1, 2, 0 => (-1) * b + (1) * a
  | 0, 1, 2, 1 => (-1) * b + (1) * a
  | 0, 1, 2, 2 => (-1) * b + (1) * a
  | 1, 0, 0, 0 => (2) * b
  | 1, 0, 0, 1 => (2) * b
  | 1, 0, 0, 2 => (-1) * b + (1) * a
  | 1, 0, 1, 0 => (4) * b
  | 1, 0, 1, 1 => (2) * b
  | 1, 0, 1, 2 => (-1) * b + (1) * a
  | 1, 0, 2, 0 => (6) * b
  | 1, 0, 2, 1 => (1) * b + (1) * a
  | 1, 0, 2, 2 => (-1) * b + (1) * a
  | 1, 1, 0, 0 => (3) * b + (-1) * a
  | 1, 1, 0, 1 => (3) * b + (-1) * a
  | 1, 1, 0, 2 => (2) * b
  | 1, 1, 1, 0 => (3) * b + (-1) * a
  | 1, 1, 1, 1 => 0
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => (2) * b
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_M4f (hb : 0 < b) (hab : b < a) (h13 : 13 * b ≤ 5 * a) (h3 : a ≤ 3 * b) :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_M4f a b) (L_M4f a b) (RM a b) (P_M4f a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_M4f, L_M4f, RM, P_M4f] <;> linarith)

theorem cert_M4f (hb : 0 < b) (hab : b < a) (h13 : 13 * b ≤ 5 * a) (h3 : a ≤ 3 * b) (η : ℝ) (hη : 0 ≤ η) :
    (P_M4f a b 0 0 0 0 - η / 3 * (|L_M4f a b 1| + |L_M4f a b 2| + |L_M4f a b 3|
      + |L_M4f a b 4| + |L_M4f a b 5|)) / ((5) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 5 := by linarith
  refine cert6 hb hab _ hq (M_M4f a b) (L_M4f a b) (RM a b) (P_M4f a b)
    (by intro k; simp only [M_M4f]; split_ifs <;> linarith) (by simp [M_M4f]) (by simp [L_M4f]) (by norm_num [M_M4f] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [rawC_M hb (by linarith) h3 _ _ _ _ h0 h1 h2' h3'])
    (edge_M4f hb hab h13 h3) (by simp [P_M4f]) η hη

/-! ## Certificate `Hf`: the free value `(a-b)/5` on `3b ≤ a` -/

noncomputable def M_Hf (a b : ℝ) (k : ℕ) : ℝ := if k = 1 then (1) else if k = 2 then (1) else if k = 3 then (1) else if k = 4 then (1) else if k = 5 then (1) else 0

noncomputable def L_Hf (a b : ℝ) (k : ℕ) : ℝ := 0

noncomputable def P_Hf (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (-1) * b + (1) * a
  | 0, 0, 0, 1 => (-1) * b + (1) * a
  | 0, 0, 0, 2 => (1) * b + (1) * a
  | 0, 0, 1, 0 => (-1) * b + (1) * a
  | 0, 0, 1, 1 => (-1) * b + (1) * a
  | 0, 0, 1, 2 => (-1) * b + (1) * a
  | 0, 0, 2, 0 => (1) * b + (1) * a
  | 0, 0, 2, 1 => (-1) * b + (1) * a
  | 0, 0, 2, 2 => (-1) * b + (1) * a
  | 0, 1, 0, 0 => (-1) * b + (1) * a
  | 0, 1, 0, 1 => (1) * b + (1) * a
  | 0, 1, 0, 2 => (3) * b + (1) * a
  | 0, 1, 1, 0 => (-1) * b + (1) * a
  | 0, 1, 1, 1 => (-1) * b + (1) * a
  | 0, 1, 1, 2 => (1) * b + (1) * a
  | 0, 1, 2, 0 => (-1) * b + (1) * a
  | 0, 1, 2, 1 => (-1) * b + (1) * a
  | 0, 1, 2, 2 => (-1) * b + (1) * a
  | 1, 0, 0, 0 => (-1) * b + (1) * a
  | 1, 0, 0, 1 => (-1) * b + (1) * a
  | 1, 0, 0, 2 => (-1) * b + (1) * a
  | 1, 0, 1, 0 => (1) * b + (1) * a
  | 1, 0, 1, 1 => (-1) * b + (1) * a
  | 1, 0, 1, 2 => (-1) * b + (1) * a
  | 1, 0, 2, 0 => (3) * b + (1) * a
  | 1, 0, 2, 1 => (1) * b + (1) * a
  | 1, 0, 2, 2 => (-1) * b + (1) * a
  | 1, 1, 0, 0 => 0
  | 1, 1, 0, 1 => 0
  | 1, 1, 0, 2 => (2) * b
  | 1, 1, 1, 0 => 0
  | 1, 1, 1, 1 => 0
  | 1, 1, 1, 2 => 0
  | 1, 1, 2, 0 => (2) * b
  | 1, 1, 2, 1 => 0
  | 1, 1, 2, 2 => 0
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_Hf (hb : 0 < b) (hab : b < a) (h3 : 3 * b ≤ a) :
    ∀ x0 x1 x2 x3 : ℕ, x0 ≤ 1 → x1 ≤ 1 → x2 ≤ 2 → x3 ≤ 2 →
      EdgeOK (M_Hf a b) (L_Hf a b) (RH a b) (P_Hf a b) x0 x1 x2 x3 := by
  intro x0 x1 x2 x3 h0 h1 h2' h3'
  unfold EdgeOK
  interval_cases x0 <;> interval_cases x1 <;> interval_cases x2 <;> interval_cases x3 <;>
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
    first
    | (exfalso; omega)
    | (norm_num [M_Hf, L_Hf, RH, P_Hf] <;> linarith)

theorem cert_Hf (hb : 0 < b) (hab : b < a) (h3 : 3 * b ≤ a) (η : ℝ) (hη : 0 ≤ η) :
    (P_Hf a b 0 0 0 0 - η / 3 * (|L_Hf a b 1| + |L_Hf a b 2| + |L_Hf a b 3|
      + |L_Hf a b 4| + |L_Hf a b 5|)) / ((5) * (2 * a + 4 * b))
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  have hq : (0 : ℝ) < 5 := by linarith
  refine cert6 hb hab _ hq (M_Hf a b) (L_Hf a b) (RH a b) (P_Hf a b)
    (by intro k; simp only [M_Hf]; split_ifs <;> linarith) (by simp [M_Hf]) (by simp [L_Hf]) (by norm_num [M_Hf] <;> ring)
    (by
    intro x0 x1 x2 x3 h0 h1 h2' h3'
    rw [rawC_H hb h3 _ _ _ _ h0 h1 h2' h3'])
    (edge_Hf hb hab h3) (by simp [P_Hf]) η hη

#print axioms edge_AL
#print axioms cert_AL
#print axioms edge_AM
#print axioms cert_AM
#print axioms edge_Band
#print axioms cert_Band
#print axioms edge_Lf
#print axioms cert_Lf
#print axioms edge_M1f
#print axioms cert_M1f
#print axioms edge_M23f
#print axioms cert_M23f
#print axioms edge_M4f
#print axioms cert_M4f
#print axioms edge_Hf
#print axioms cert_Hf

end CIGAMF.P13.PaperCTwoMag1122