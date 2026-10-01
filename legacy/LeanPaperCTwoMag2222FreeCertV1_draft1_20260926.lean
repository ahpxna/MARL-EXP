import «LeanPaperCTwoMag2222CertV1»

/-!
# Paper C: counts `(2,2,2,2)` — lower bounds on the free value

`g = (a, a, -a, -a, b, b, -b, -b)`, `D = 4(a+b)`, at `η = 8` (the band is vacuous). Five dual
certificates for `cert8`, with no band terms:

| cert | range | bound on `D·V_g^free` | budget weights (scaled) | `Z` |
|---|---|---|---|---|
| `T13` | `a ≤ 2b` | `2(a-b)/3` | `1/3` on `3,4,5` | `1` |
| `F1` | `2b ≤ a ≤ 3b` | `2b(3b-a)/(5b-a)` | `(b, 3b-a, b)` on `3,4,5` | `5b-a` |
| `F2` | `2b ≤ a ≤ 3b` | `2a(3b-a)/(17b-5a)` | `(3b-a,3b-a,b,3b-a,b,3b-a,3b-a)` | `17b-5a` |
| `Um` | `2b ≤ a ≤ 3b` | `4b/7` | `1/7` on `1..7` | `1` |
| `Uh` | `3b ≤ a` | `2(a-b)/7` | `1/7` on `1..7` | `1` |

The potentials are an exact shortest-path computation in rational arithmetic
(`scratchpad/me2222/gen_freecert.py`, via `c2222/gen.py`), and every edge inequality is checked
here on its whole ratio range; for `F1` and `F2` the edge slacks are quadratic in `(a, b)` and
the check uses the products of the range constraints.
-/

namespace CIGAMF.P13.PaperCTwoMag2222

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFlowCert

variable {a b : ℝ}

/-- No band terms. -/
noncomputable def ℓ0 : ℕ → Fin 4 → ℝ := fun _ _ => 0

/-! ## Certificate `T13` -/

noncomputable def μT13 (a b : ℝ) : ℕ → ℝ
  | 3 => ((1/3))
  | 4 => ((1/3))
  | 5 => ((1/3))
  | _ => 0

noncomputable def φT13 (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => ((2/3) * a - (2/3) * b)
  | 0, 0, 0, 1 => ((2/3) * a - (2/3) * b)
  | 0, 0, 0, 2 => ((2/3) * a - (2/3) * b)
  | 0, 0, 1, 0 => ((2/3) * a - (2/3) * b)
  | 0, 0, 1, 1 => (a - b)
  | 0, 0, 1, 2 => (a - b)
  | 0, 0, 2, 0 => ((2/3) * a - (2/3) * b)
  | 0, 0, 2, 1 => (a - b)
  | 0, 0, 2, 2 => ((2/3) * a - (2/3) * b)
  | 0, 1, 0, 0 => ((2/3) * a - (2/3) * b)
  | 0, 1, 0, 1 => ((2/3) * a - (2/3) * b)
  | 0, 1, 0, 2 => ((2/3) * a + (2/3) * b)
  | 0, 1, 1, 0 => ((2/3) * a - (2/3) * b)
  | 0, 1, 1, 1 => (a - b)
  | 0, 1, 1, 2 => ((2/3) * a)
  | 0, 1, 2, 0 => ((2/3) * a - (2/3) * b)
  | 0, 1, 2, 1 => ((2/3) * a - (2/3) * b)
  | 0, 1, 2, 2 => ((2/3) * a - (2/3) * b)
  | 0, 2, 0, 0 => (a - b)
  | 0, 2, 0, 1 => ((5/3) * a - (1/3) * b)
  | 0, 2, 0, 2 => ((4/3) * a + (2/3) * b)
  | 0, 2, 1, 0 => ((4/3) * a - (4/3) * b)
  | 0, 2, 1, 1 => ((4/3) * a - (2/3) * b)
  | 0, 2, 1, 2 => (a - (1/3) * b)
  | 0, 2, 2, 0 => ((2/3) * a - (2/3) * b)
  | 0, 2, 2, 1 => (a - b)
  | 0, 2, 2, 2 => (0)
  | 1, 0, 0, 0 => ((2/3) * a - (2/3) * b)
  | 1, 0, 0, 1 => ((2/3) * a - (2/3) * b)
  | 1, 0, 0, 2 => ((2/3) * a - (2/3) * b)
  | 1, 0, 1, 0 => ((2/3) * a - (2/3) * b)
  | 1, 0, 1, 1 => (a - b)
  | 1, 0, 1, 2 => ((2/3) * a - (2/3) * b)
  | 1, 0, 2, 0 => ((2/3) * a + (2/3) * b)
  | 1, 0, 2, 1 => ((2/3) * a)
  | 1, 0, 2, 2 => ((2/3) * a - (2/3) * b)
  | 1, 1, 0, 0 => ((2/3) * a - (2/3) * b)
  | 1, 1, 0, 1 => ((2/3) * a - (2/3) * b)
  | 1, 1, 0, 2 => ((2/3) * b)
  | 1, 1, 1, 0 => ((2/3) * a - (2/3) * b)
  | 1, 1, 1, 1 => ((1/3) * a - (1/3) * b)
  | 1, 1, 1, 2 => ((1/3) * a - (1/3) * b)
  | 1, 1, 2, 0 => ((2/3) * b)
  | 1, 1, 2, 1 => ((1/3) * a - (1/3) * b)
  | 1, 1, 2, 2 => (0)
  | 1, 2, 0, 0 => (a - b)
  | 1, 2, 0, 1 => ((2/3) * a)
  | 1, 2, 0, 2 => ((2/3) * a)
  | 1, 2, 1, 0 => ((1/3) * a - (1/3) * b)
  | 1, 2, 1, 1 => ((2/3) * a - (2/3) * b)
  | 1, 2, 1, 2 => (0)
  | 1, 2, 2, 0 => (0)
  | 1, 2, 2, 1 => (0)
  | 1, 2, 2, 2 => (0)
  | 2, 0, 0, 0 => (a - b)
  | 2, 0, 0, 1 => ((4/3) * a - (4/3) * b)
  | 2, 0, 0, 2 => ((2/3) * a - (2/3) * b)
  | 2, 0, 1, 0 => ((5/3) * a - (1/3) * b)
  | 2, 0, 1, 1 => ((4/3) * a - (2/3) * b)
  | 2, 0, 1, 2 => (a - b)
  | 2, 0, 2, 0 => ((4/3) * a + (2/3) * b)
  | 2, 0, 2, 1 => (a - (1/3) * b)
  | 2, 0, 2, 2 => (0)
  | 2, 1, 0, 0 => (a - b)
  | 2, 1, 0, 1 => ((1/3) * a - (1/3) * b)
  | 2, 1, 0, 2 => (0)
  | 2, 1, 1, 0 => ((2/3) * a)
  | 2, 1, 1, 1 => ((2/3) * a - (2/3) * b)
  | 2, 1, 1, 2 => (0)
  | 2, 1, 2, 0 => ((2/3) * a)
  | 2, 1, 2, 1 => (0)
  | 2, 1, 2, 2 => (0)
  | 2, 2, 0, 0 => ((1/3) * a - (1/3) * b)
  | 2, 2, 0, 1 => ((1/3) * a - (1/3) * b)
  | 2, 2, 0, 2 => (0)
  | 2, 2, 1, 0 => ((1/3) * a - (1/3) * b)
  | 2, 2, 1, 1 => (0)
  | 2, 2, 1, 2 => (0)
  | 2, 2, 2, 0 => (0)
  | 2, 2, 2, 1 => (0)
  | 2, 2, 2, 2 => (0)
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_T13_0 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 < 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φT13 a b v0 v1 v2 v3 ≤ nodeN a b (βlo a b) (μT13 a b) ℓ0 v0 v1 v2 v3 + φT13 a b (v0 + 1) v1 v2 v3 := by
  have habs := abs_sN_lo hb hab h2 v0 v1 v2 v3 (by omega) h1 h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgLo, sgHi, sN, φT13, μT13, ℓ0, βlo] <;> linarith

set_option maxHeartbeats 8000000 in
theorem edge_T13_1 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 < 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φT13 a b v0 v1 v2 v3 ≤ nodeN a b (βlo a b) (μT13 a b) ℓ0 v0 v1 v2 v3 + φT13 a b v0 (v1 + 1) v2 v3 := by
  have habs := abs_sN_lo hb hab h2 v0 v1 v2 v3 h0 (by omega) h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgLo, sgHi, sN, φT13, μT13, ℓ0, βlo] <;> linarith

set_option maxHeartbeats 8000000 in
theorem edge_T13_2 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 < 2) (h3' : v3 ≤ 2) :
    φT13 a b v0 v1 v2 v3 ≤ nodeN a b (βlo a b) (μT13 a b) ℓ0 v0 v1 v2 v3 + φT13 a b v0 v1 (v2 + 1) v3 := by
  have habs := abs_sN_lo hb hab h2 v0 v1 v2 v3 h0 h1 (by omega) h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgLo, sgHi, sN, φT13, μT13, ℓ0, βlo] <;> linarith

set_option maxHeartbeats 8000000 in
theorem edge_T13_3 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 < 2) :
    φT13 a b v0 v1 v2 v3 ≤ nodeN a b (βlo a b) (μT13 a b) ℓ0 v0 v1 v2 v3 + φT13 a b v0 v1 v2 (v3 + 1) := by
  have habs := abs_sN_lo hb hab h2 v0 v1 v2 v3 h0 h1 h2' (by omega)
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgLo, sgHi, sN, φT13, μT13, ℓ0, βlo] <;> linarith

theorem edge_T13 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) : EdgeOK a b (βlo a b) (μT13 a b) ℓ0 (φT13 a b) := by
  intro v0 v1 v2 v3 e0 e1 e2 e3
  exact ⟨fun h => edge_T13_0 hb hab h2 v0 v1 v2 v3 h e1 e2 e3, fun h => edge_T13_1 hb hab h2 v0 v1 v2 v3 e0 h e2 e3,
    fun h => edge_T13_2 hb hab h2 v0 v1 v2 v3 e0 e1 h e3, fun h => edge_T13_3 hb hab h2 v0 v1 v2 v3 e0 e1 e2 h⟩

theorem μT13_nonneg (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) : ∀ k, 0 ≤ μT13 a b k := by
  intro k; unfold μT13; split <;> first | norm_num | linarith

/-- **Free-value lower bound `T13`.** -/
theorem lower_T13 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    2 * (a - b) / 3 / (4 * (a + b)) ≤ trueValue (g8 a b) 8 K7 K7_ne := by
  have hZ : (0 : ℝ) < (1) := by first | norm_num | linarith
  have h := cert8 hb hab _ hZ (βlo a b) (μT13 a b) ℓ0 (φT13 a b) (μT13_nonneg hb hab h2)
    (by simp [μT13]) (by simp [μT13]; try ring) (fun k hk _ => βlo_eq hb hab h2 k hk)
    (edge_T13 hb hab h2) (by simp [φT13]) 8 (by norm_num)
  have e0 : φT13 a b 0 0 0 0 = ((2/3) * a - (2/3) * b) := by simp [φT13]
  have e1 : ∑ k ∈ range 8, ∑ τ, |ℓ0 k τ| = 0 := by simp [ℓ0]
  rw [e0, e1, mul_zero, sub_zero] at h
  refine le_trans (le_of_eq ?_) h
  field_simp
  ring

/-! ## Certificate `F1` -/

noncomputable def μF1 (a b : ℝ) : ℕ → ℝ
  | 3 => (b)
  | 4 => (-a + 3 * b)
  | 5 => (b)
  | _ => 0

noncomputable def φF1 (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (-2 * a * b + 6 * b^2)
  | 0, 0, 0, 1 => (-2 * a * b + 6 * b^2)
  | 0, 0, 0, 2 => (-2 * a * b + 6 * b^2)
  | 0, 0, 1, 0 => (-2 * a * b + 6 * b^2)
  | 0, 0, 1, 1 => (-a^2 + 2 * a * b + 3 * b^2)
  | 0, 0, 1, 2 => (-a^2 + 2 * a * b + 3 * b^2)
  | 0, 0, 2, 0 => (-2 * a * b + 6 * b^2)
  | 0, 0, 2, 1 => (-a^2 + 2 * a * b + 3 * b^2)
  | 0, 0, 2, 2 => (2 * b^2)
  | 0, 1, 0, 0 => (-2 * a * b + 6 * b^2)
  | 0, 1, 0, 1 => (-2 * a * b + 6 * b^2)
  | 0, 1, 0, 2 => (-2 * a * b + 10 * b^2)
  | 0, 1, 1, 0 => (-2 * a * b + 6 * b^2)
  | 0, 1, 1, 1 => (-a * b + 5 * b^2)
  | 0, 1, 1, 2 => (-a^2 + a * b + 6 * b^2)
  | 0, 1, 2, 0 => (-2 * a * b + 6 * b^2)
  | 0, 1, 2, 1 => (-a^2 + 3 * a * b)
  | 0, 1, 2, 2 => (2 * b^2)
  | 0, 2, 0, 0 => (-a * b + 5 * b^2)
  | 0, 2, 0, 1 => (-a^2 + 2 * a * b + 9 * b^2)
  | 0, 2, 0, 2 => (-2 * a^2 + 4 * a * b + 10 * b^2)
  | 0, 2, 1, 0 => (-a^2 + 5 * a * b - 2 * b^2)
  | 0, 2, 1, 1 => (-2 * a^2 + 6 * a * b + 2 * b^2)
  | 0, 2, 1, 2 => (a * b + 3 * b^2)
  | 0, 2, 2, 0 => (-2 * a^2 + 8 * a * b - 6 * b^2)
  | 0, 2, 2, 1 => (a * b + b^2)
  | 0, 2, 2, 2 => (0)
  | 1, 0, 0, 0 => (-2 * a * b + 6 * b^2)
  | 1, 0, 0, 1 => (-2 * a * b + 6 * b^2)
  | 1, 0, 0, 2 => (-2 * a * b + 6 * b^2)
  | 1, 0, 1, 0 => (-2 * a * b + 6 * b^2)
  | 1, 0, 1, 1 => (-a * b + 5 * b^2)
  | 1, 0, 1, 2 => (-a^2 + 3 * a * b)
  | 1, 0, 2, 0 => (-2 * a * b + 10 * b^2)
  | 1, 0, 2, 1 => (-a^2 + a * b + 6 * b^2)
  | 1, 0, 2, 2 => (2 * b^2)
  | 1, 1, 0, 0 => (-2 * a * b + 6 * b^2)
  | 1, 1, 0, 1 => (-2 * a * b + 6 * b^2)
  | 1, 1, 0, 2 => (-2 * a * b + 6 * b^2)
  | 1, 1, 1, 0 => (-2 * a * b + 6 * b^2)
  | 1, 1, 1, 1 => (-a * b + 3 * b^2)
  | 1, 1, 1, 2 => (-a * b + 3 * b^2)
  | 1, 1, 2, 0 => (-2 * a * b + 6 * b^2)
  | 1, 1, 2, 1 => (-a * b + 3 * b^2)
  | 1, 1, 2, 2 => (0)
  | 1, 2, 0, 0 => (-a * b + 5 * b^2)
  | 1, 2, 0, 1 => (-a^2 + a * b + 6 * b^2)
  | 1, 2, 0, 2 => (4 * b^2)
  | 1, 2, 1, 0 => (-a^2 + 4 * a * b - 3 * b^2)
  | 1, 2, 1, 1 => (2 * b^2)
  | 1, 2, 1, 2 => (0)
  | 1, 2, 2, 0 => (0)
  | 1, 2, 2, 1 => (0)
  | 1, 2, 2, 2 => (0)
  | 2, 0, 0, 0 => (-a * b + 5 * b^2)
  | 2, 0, 0, 1 => (-a^2 + 5 * a * b - 2 * b^2)
  | 2, 0, 0, 2 => (-2 * a^2 + 8 * a * b - 6 * b^2)
  | 2, 0, 1, 0 => (-a^2 + 2 * a * b + 9 * b^2)
  | 2, 0, 1, 1 => (-2 * a^2 + 6 * a * b + 2 * b^2)
  | 2, 0, 1, 2 => (a * b + b^2)
  | 2, 0, 2, 0 => (-2 * a^2 + 4 * a * b + 10 * b^2)
  | 2, 0, 2, 1 => (a * b + 3 * b^2)
  | 2, 0, 2, 2 => (0)
  | 2, 1, 0, 0 => (-a * b + 5 * b^2)
  | 2, 1, 0, 1 => (-a^2 + 4 * a * b - 3 * b^2)
  | 2, 1, 0, 2 => (0)
  | 2, 1, 1, 0 => (-a^2 + a * b + 6 * b^2)
  | 2, 1, 1, 1 => (2 * b^2)
  | 2, 1, 1, 2 => (0)
  | 2, 1, 2, 0 => (4 * b^2)
  | 2, 1, 2, 1 => (0)
  | 2, 1, 2, 2 => (0)
  | 2, 2, 0, 0 => (-a * b + 3 * b^2)
  | 2, 2, 0, 1 => (-a * b + 3 * b^2)
  | 2, 2, 0, 2 => (0)
  | 2, 2, 1, 0 => (-a * b + 3 * b^2)
  | 2, 2, 1, 1 => (0)
  | 2, 2, 1, 2 => (0)
  | 2, 2, 2, 0 => (0)
  | 2, 2, 2, 1 => (0)
  | 2, 2, 2, 2 => (0)
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_F1_0 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 < 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φF1 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μF1 a b) ℓ0 v0 v1 v2 v3 + φF1 a b (v0 + 1) v1 v2 v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 (by omega) h1 h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φF1, μF1, ℓ0, βmid] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h2) hb.le, mul_nonneg (sub_nonneg.2 h3) hb.le, mul_pos hb hb, mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h3)]

set_option maxHeartbeats 8000000 in
theorem edge_F1_1 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 < 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φF1 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μF1 a b) ℓ0 v0 v1 v2 v3 + φF1 a b v0 (v1 + 1) v2 v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 (by omega) h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φF1, μF1, ℓ0, βmid] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h2) hb.le, mul_nonneg (sub_nonneg.2 h3) hb.le, mul_pos hb hb, mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h3)]

set_option maxHeartbeats 8000000 in
theorem edge_F1_2 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 < 2) (h3' : v3 ≤ 2) :
    φF1 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μF1 a b) ℓ0 v0 v1 v2 v3 + φF1 a b v0 v1 (v2 + 1) v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 h1 (by omega) h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φF1, μF1, ℓ0, βmid] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h2) hb.le, mul_nonneg (sub_nonneg.2 h3) hb.le, mul_pos hb hb, mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h3)]

set_option maxHeartbeats 8000000 in
theorem edge_F1_3 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 < 2) :
    φF1 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μF1 a b) ℓ0 v0 v1 v2 v3 + φF1 a b v0 v1 v2 (v3 + 1) := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 h1 h2' (by omega)
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φF1, μF1, ℓ0, βmid] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h2) hb.le, mul_nonneg (sub_nonneg.2 h3) hb.le, mul_pos hb hb, mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h3)]

theorem edge_F1 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) : EdgeOK a b (βmid a b) (μF1 a b) ℓ0 (φF1 a b) := by
  intro v0 v1 v2 v3 e0 e1 e2 e3
  exact ⟨fun h => edge_F1_0 hb h2 h3 v0 v1 v2 v3 h e1 e2 e3, fun h => edge_F1_1 hb h2 h3 v0 v1 v2 v3 e0 h e2 e3,
    fun h => edge_F1_2 hb h2 h3 v0 v1 v2 v3 e0 e1 h e3, fun h => edge_F1_3 hb h2 h3 v0 v1 v2 v3 e0 e1 e2 h⟩

theorem μF1_nonneg (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) : ∀ k, 0 ≤ μF1 a b k := by
  intro k; unfold μF1; split <;> first | norm_num | linarith

/-- **Free-value lower bound `F1`.** -/
theorem lower_F1 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    2 * b * (3 * b - a) / (5 * b - a) / (4 * (a + b)) ≤ trueValue (g8 a b) 8 K7 K7_ne := by
  have hab : b < a := by linarith
  have hZ : (0 : ℝ) < (-a + 5 * b) := by first | norm_num | linarith
  have h := cert8 hb hab _ hZ (βmid a b) (μF1 a b) ℓ0 (φF1 a b) (μF1_nonneg hb h2 h3)
    (by simp [μF1]) (by simp [μF1]; try ring) (fun k hk _ => βmid_eq hb h2 h3 k hk)
    (edge_F1 hb h2 h3) (by simp [φF1]) 8 (by norm_num)
  have e0 : φF1 a b 0 0 0 0 = (-2 * a * b + 6 * b^2) := by simp [φF1]
  have e1 : ∑ k ∈ range 8, ∑ τ, |ℓ0 k τ| = 0 := by simp [ℓ0]
  rw [e0, e1, mul_zero, sub_zero] at h
  refine le_trans (le_of_eq ?_) h
  field_simp
  ring

/-! ## Certificate `F2` -/

noncomputable def μF2 (a b : ℝ) : ℕ → ℝ
  | 1 => (-a + 3 * b)
  | 2 => (-a + 3 * b)
  | 3 => (b)
  | 4 => (-a + 3 * b)
  | 5 => (b)
  | 6 => (-a + 3 * b)
  | 7 => (-a + 3 * b)
  | _ => 0

noncomputable def φF2 (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => (-2 * a^2 + 6 * a * b)
  | 0, 0, 0, 1 => (-2 * a^2 + 6 * a * b)
  | 0, 0, 0, 2 => (-a^2 + 9 * b^2)
  | 0, 0, 1, 0 => (-2 * a^2 + 6 * a * b)
  | 0, 0, 1, 1 => (-2 * a^2 + 6 * a * b)
  | 0, 0, 1, 2 => (-2 * a^2 + 6 * a * b)
  | 0, 0, 2, 0 => (-a^2 + 9 * b^2)
  | 0, 0, 2, 1 => (-2 * a^2 + 6 * a * b)
  | 0, 0, 2, 2 => (-a^2 + 4 * a * b - b^2)
  | 0, 1, 0, 0 => (-2 * a^2 + 6 * a * b)
  | 0, 1, 0, 1 => (-2 * a^2 + 4 * a * b + 6 * b^2)
  | 0, 1, 0, 2 => (-a^2 + 2 * a * b + 7 * b^2)
  | 0, 1, 1, 0 => (-2 * a^2 + 6 * a * b)
  | 0, 1, 1, 1 => (-a^2 + 3 * a * b + 2 * b^2)
  | 0, 1, 1, 2 => (-2 * a^2 + 5 * a * b + 3 * b^2)
  | 0, 1, 2, 0 => (-a^2 + 2 * a * b + 3 * b^2)
  | 0, 1, 2, 1 => (-2 * a^2 + 7 * a * b - 3 * b^2)
  | 0, 1, 2, 2 => (-a^2 + 4 * a * b - b^2)
  | 0, 2, 0, 0 => (-2 * a^2 + 5 * a * b + 5 * b^2)
  | 0, 2, 0, 1 => (-a^2 + 2 * a * b + 9 * b^2)
  | 0, 2, 0, 2 => (-2 * a^2 + 2 * a * b + 16 * b^2)
  | 0, 2, 1, 0 => (-a^2 + 4 * a * b + b^2)
  | 0, 2, 1, 1 => (-2 * a^2 + 6 * a * b + 2 * b^2)
  | 0, 2, 1, 2 => (-a^2 + 3 * a * b + 6 * b^2)
  | 0, 2, 2, 0 => (-3 * a^2 + 12 * a * b - 9 * b^2)
  | 0, 2, 2, 1 => (-a^2 + 5 * a * b - 2 * b^2)
  | 0, 2, 2, 2 => (-3 * a^2 + 10 * a * b - 3 * b^2)
  | 1, 0, 0, 0 => (-2 * a^2 + 6 * a * b)
  | 1, 0, 0, 1 => (-2 * a^2 + 6 * a * b)
  | 1, 0, 0, 2 => (-a^2 + 2 * a * b + 3 * b^2)
  | 1, 0, 1, 0 => (-2 * a^2 + 4 * a * b + 6 * b^2)
  | 1, 0, 1, 1 => (-a^2 + 3 * a * b + 2 * b^2)
  | 1, 0, 1, 2 => (-2 * a^2 + 7 * a * b - 3 * b^2)
  | 1, 0, 2, 0 => (-a^2 + 2 * a * b + 7 * b^2)
  | 1, 0, 2, 1 => (-2 * a^2 + 5 * a * b + 3 * b^2)
  | 1, 0, 2, 2 => (-a^2 + 4 * a * b - b^2)
  | 1, 1, 0, 0 => (-a^2 + 2 * a * b + 3 * b^2)
  | 1, 1, 0, 1 => (-a^2 + 2 * a * b + 3 * b^2)
  | 1, 1, 0, 2 => (-a^2 + 2 * a * b + 3 * b^2)
  | 1, 1, 1, 0 => (-a^2 + 2 * a * b + 3 * b^2)
  | 1, 1, 1, 1 => (-a^2 + 3 * a * b)
  | 1, 1, 1, 2 => (-a^2 + 3 * a * b)
  | 1, 1, 2, 0 => (-a^2 + 2 * a * b + 3 * b^2)
  | 1, 1, 2, 1 => (-a^2 + 3 * a * b)
  | 1, 1, 2, 2 => (-a^2 + 4 * a * b - 3 * b^2)
  | 1, 2, 0, 0 => (-a * b + 5 * b^2)
  | 1, 2, 0, 1 => (-a^2 + a * b + 6 * b^2)
  | 1, 2, 0, 2 => (-2 * a * b + 10 * b^2)
  | 1, 2, 1, 0 => (-a^2 + 3 * a * b)
  | 1, 2, 1, 1 => (2 * b^2)
  | 1, 2, 1, 2 => (-a^2 + 2 * a * b + 3 * b^2)
  | 1, 2, 2, 0 => (-a^2 + 4 * a * b - 3 * b^2)
  | 1, 2, 2, 1 => (-a^2 + 4 * a * b - 3 * b^2)
  | 1, 2, 2, 2 => (-a^2 + 4 * a * b - 3 * b^2)
  | 2, 0, 0, 0 => (-2 * a^2 + 5 * a * b + 5 * b^2)
  | 2, 0, 0, 1 => (-a^2 + 4 * a * b + b^2)
  | 2, 0, 0, 2 => (-3 * a^2 + 12 * a * b - 9 * b^2)
  | 2, 0, 1, 0 => (-a^2 + 2 * a * b + 9 * b^2)
  | 2, 0, 1, 1 => (-2 * a^2 + 6 * a * b + 2 * b^2)
  | 2, 0, 1, 2 => (-a^2 + 5 * a * b - 2 * b^2)
  | 2, 0, 2, 0 => (-2 * a^2 + 2 * a * b + 16 * b^2)
  | 2, 0, 2, 1 => (-a^2 + 3 * a * b + 6 * b^2)
  | 2, 0, 2, 2 => (-3 * a^2 + 10 * a * b - 3 * b^2)
  | 2, 1, 0, 0 => (-a * b + 5 * b^2)
  | 2, 1, 0, 1 => (-a^2 + 3 * a * b)
  | 2, 1, 0, 2 => (-a^2 + 4 * a * b - 3 * b^2)
  | 2, 1, 1, 0 => (-a^2 + a * b + 6 * b^2)
  | 2, 1, 1, 1 => (2 * b^2)
  | 2, 1, 1, 2 => (-a^2 + 4 * a * b - 3 * b^2)
  | 2, 1, 2, 0 => (-2 * a * b + 10 * b^2)
  | 2, 1, 2, 1 => (-a^2 + 2 * a * b + 3 * b^2)
  | 2, 1, 2, 2 => (-a^2 + 4 * a * b - 3 * b^2)
  | 2, 2, 0, 0 => (-a * b + 3 * b^2)
  | 2, 2, 0, 1 => (-a * b + 3 * b^2)
  | 2, 2, 0, 2 => (-2 * a * b + 6 * b^2)
  | 2, 2, 1, 0 => (-a * b + 3 * b^2)
  | 2, 2, 1, 1 => (0)
  | 2, 2, 1, 2 => (0)
  | 2, 2, 2, 0 => (-2 * a * b + 6 * b^2)
  | 2, 2, 2, 1 => (0)
  | 2, 2, 2, 2 => (0)
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_F2_0 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 < 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φF2 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μF2 a b) ℓ0 v0 v1 v2 v3 + φF2 a b (v0 + 1) v1 v2 v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 (by omega) h1 h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φF2, μF2, ℓ0, βmid] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h2) hb.le, mul_nonneg (sub_nonneg.2 h3) hb.le, mul_pos hb hb, mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h3)]

set_option maxHeartbeats 8000000 in
theorem edge_F2_1 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 < 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φF2 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μF2 a b) ℓ0 v0 v1 v2 v3 + φF2 a b v0 (v1 + 1) v2 v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 (by omega) h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φF2, μF2, ℓ0, βmid] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h2) hb.le, mul_nonneg (sub_nonneg.2 h3) hb.le, mul_pos hb hb, mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h3)]

set_option maxHeartbeats 8000000 in
theorem edge_F2_2 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 < 2) (h3' : v3 ≤ 2) :
    φF2 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μF2 a b) ℓ0 v0 v1 v2 v3 + φF2 a b v0 v1 (v2 + 1) v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 h1 (by omega) h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φF2, μF2, ℓ0, βmid] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h2) hb.le, mul_nonneg (sub_nonneg.2 h3) hb.le, mul_pos hb hb, mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h3)]

set_option maxHeartbeats 8000000 in
theorem edge_F2_3 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 < 2) :
    φF2 a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μF2 a b) ℓ0 v0 v1 v2 v3 + φF2 a b v0 v1 v2 (v3 + 1) := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 h1 h2' (by omega)
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φF2, μF2, ℓ0, βmid] <;> nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3), mul_nonneg (sub_nonneg.2 h2) hb.le, mul_nonneg (sub_nonneg.2 h3) hb.le, mul_pos hb hb, mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h3)]

theorem edge_F2 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) : EdgeOK a b (βmid a b) (μF2 a b) ℓ0 (φF2 a b) := by
  intro v0 v1 v2 v3 e0 e1 e2 e3
  exact ⟨fun h => edge_F2_0 hb h2 h3 v0 v1 v2 v3 h e1 e2 e3, fun h => edge_F2_1 hb h2 h3 v0 v1 v2 v3 e0 h e2 e3,
    fun h => edge_F2_2 hb h2 h3 v0 v1 v2 v3 e0 e1 h e3, fun h => edge_F2_3 hb h2 h3 v0 v1 v2 v3 e0 e1 e2 h⟩

theorem μF2_nonneg (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) : ∀ k, 0 ≤ μF2 a b k := by
  intro k; unfold μF2; split <;> first | norm_num | linarith

/-- **Free-value lower bound `F2`.** -/
theorem lower_F2 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    2 * a * (3 * b - a) / (17 * b - 5 * a) / (4 * (a + b)) ≤ trueValue (g8 a b) 8 K7 K7_ne := by
  have hab : b < a := by linarith
  have hZ : (0 : ℝ) < (-5 * a + 17 * b) := by first | norm_num | linarith
  have h := cert8 hb hab _ hZ (βmid a b) (μF2 a b) ℓ0 (φF2 a b) (μF2_nonneg hb h2 h3)
    (by simp [μF2]) (by simp [μF2]; try ring) (fun k hk _ => βmid_eq hb h2 h3 k hk)
    (edge_F2 hb h2 h3) (by simp [φF2]) 8 (by norm_num)
  have e0 : φF2 a b 0 0 0 0 = (-2 * a^2 + 6 * a * b) := by simp [φF2]
  have e1 : ∑ k ∈ range 8, ∑ τ, |ℓ0 k τ| = 0 := by simp [ℓ0]
  rw [e0, e1, mul_zero, sub_zero] at h
  refine le_trans (le_of_eq ?_) h
  field_simp
  ring

/-! ## Certificate `Um` -/

noncomputable def μUm (a b : ℝ) : ℕ → ℝ
  | 1 => ((1/7))
  | 2 => ((1/7))
  | 3 => ((1/7))
  | 4 => ((1/7))
  | 5 => ((1/7))
  | 6 => ((1/7))
  | 7 => ((1/7))
  | _ => 0

noncomputable def φUm (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => ((4/7) * b)
  | 0, 0, 0, 1 => ((4/7) * b)
  | 0, 0, 0, 2 => ((1/7) * a + (3/7) * b)
  | 0, 0, 1, 0 => ((4/7) * b)
  | 0, 0, 1, 1 => ((4/7) * b)
  | 0, 0, 1, 2 => ((4/7) * b)
  | 0, 0, 2, 0 => ((1/7) * a + (3/7) * b)
  | 0, 0, 2, 1 => ((4/7) * b)
  | 0, 0, 2, 2 => ((1/7) * a + (1/7) * b)
  | 0, 1, 0, 0 => ((4/7) * b)
  | 0, 1, 0, 1 => ((6/7) * b)
  | 0, 1, 0, 2 => ((1/7) * a + (5/7) * b)
  | 0, 1, 1, 0 => ((4/7) * b)
  | 0, 1, 1, 1 => ((4/7) * b)
  | 0, 1, 1, 2 => ((1/7) * a + (3/7) * b)
  | 0, 1, 2, 0 => ((1/7) * a + (1/7) * b)
  | 0, 1, 2, 1 => ((1/7) * a + (1/7) * b)
  | 0, 1, 2, 2 => ((1/7) * a + (1/7) * b)
  | 0, 2, 0, 0 => ((1/7) * a + (5/7) * b)
  | 0, 2, 0, 1 => ((1/7) * a + b)
  | 0, 2, 0, 2 => ((2/7) * a + (8/7) * b)
  | 0, 2, 1, 0 => ((1/7) * a + (3/7) * b)
  | 0, 2, 1, 1 => ((2/7) * a + (2/7) * b)
  | 0, 2, 1, 2 => ((2/7) * a + (4/7) * b)
  | 0, 2, 2, 0 => ((3/7) * a - (3/7) * b)
  | 0, 2, 2, 1 => ((2/7) * a)
  | 0, 2, 2, 2 => ((3/7) * a - (1/7) * b)
  | 1, 0, 0, 0 => ((4/7) * b)
  | 1, 0, 0, 1 => ((4/7) * b)
  | 1, 0, 0, 2 => ((1/7) * a + (1/7) * b)
  | 1, 0, 1, 0 => ((6/7) * b)
  | 1, 0, 1, 1 => ((4/7) * b)
  | 1, 0, 1, 2 => ((1/7) * a + (1/7) * b)
  | 1, 0, 2, 0 => ((1/7) * a + (5/7) * b)
  | 1, 0, 2, 1 => ((1/7) * a + (3/7) * b)
  | 1, 0, 2, 2 => ((1/7) * a + (1/7) * b)
  | 1, 1, 0, 0 => (-(1/7) * a + (5/7) * b)
  | 1, 1, 0, 1 => (-(1/7) * a + (5/7) * b)
  | 1, 1, 0, 2 => ((1/7) * a + (1/7) * b)
  | 1, 1, 1, 0 => (-(1/7) * a + (5/7) * b)
  | 1, 1, 1, 1 => ((2/7) * b)
  | 1, 1, 1, 2 => ((2/7) * b)
  | 1, 1, 2, 0 => ((1/7) * a + (1/7) * b)
  | 1, 1, 2, 1 => ((2/7) * b)
  | 1, 1, 2, 2 => ((1/7) * a - (1/7) * b)
  | 1, 2, 0, 0 => (-(1/7) * a + (5/7) * b)
  | 1, 2, 0, 1 => ((4/7) * b)
  | 1, 2, 0, 2 => ((6/7) * b)
  | 1, 2, 1, 0 => ((2/7) * b)
  | 1, 2, 1, 1 => ((2/7) * b)
  | 1, 2, 1, 2 => ((1/7) * a + (1/7) * b)
  | 1, 2, 2, 0 => ((1/7) * a - (1/7) * b)
  | 1, 2, 2, 1 => ((1/7) * a - (1/7) * b)
  | 1, 2, 2, 2 => ((1/7) * a - (1/7) * b)
  | 2, 0, 0, 0 => ((1/7) * a + (5/7) * b)
  | 2, 0, 0, 1 => ((1/7) * a + (3/7) * b)
  | 2, 0, 0, 2 => ((3/7) * a - (3/7) * b)
  | 2, 0, 1, 0 => ((1/7) * a + b)
  | 2, 0, 1, 1 => ((2/7) * a + (2/7) * b)
  | 2, 0, 1, 2 => ((2/7) * a)
  | 2, 0, 2, 0 => ((2/7) * a + (8/7) * b)
  | 2, 0, 2, 1 => ((2/7) * a + (4/7) * b)
  | 2, 0, 2, 2 => ((3/7) * a - (1/7) * b)
  | 2, 1, 0, 0 => (-(1/7) * a + (5/7) * b)
  | 2, 1, 0, 1 => ((2/7) * b)
  | 2, 1, 0, 2 => ((1/7) * a - (1/7) * b)
  | 2, 1, 1, 0 => ((4/7) * b)
  | 2, 1, 1, 1 => ((2/7) * b)
  | 2, 1, 1, 2 => ((1/7) * a - (1/7) * b)
  | 2, 1, 2, 0 => ((6/7) * b)
  | 2, 1, 2, 1 => ((1/7) * a + (1/7) * b)
  | 2, 1, 2, 2 => ((1/7) * a - (1/7) * b)
  | 2, 2, 0, 0 => (-(1/7) * a + (3/7) * b)
  | 2, 2, 0, 1 => (-(1/7) * a + (3/7) * b)
  | 2, 2, 0, 2 => ((2/7) * b)
  | 2, 2, 1, 0 => (-(1/7) * a + (3/7) * b)
  | 2, 2, 1, 1 => (0)
  | 2, 2, 1, 2 => (0)
  | 2, 2, 2, 0 => ((2/7) * b)
  | 2, 2, 2, 1 => (0)
  | 2, 2, 2, 2 => (0)
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_Um_0 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 < 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φUm a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μUm a b) ℓ0 v0 v1 v2 v3 + φUm a b (v0 + 1) v1 v2 v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 (by omega) h1 h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φUm, μUm, ℓ0, βmid] <;> linarith

set_option maxHeartbeats 8000000 in
theorem edge_Um_1 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 < 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φUm a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μUm a b) ℓ0 v0 v1 v2 v3 + φUm a b v0 (v1 + 1) v2 v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 (by omega) h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φUm, μUm, ℓ0, βmid] <;> linarith

set_option maxHeartbeats 8000000 in
theorem edge_Um_2 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 < 2) (h3' : v3 ≤ 2) :
    φUm a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μUm a b) ℓ0 v0 v1 v2 v3 + φUm a b v0 v1 (v2 + 1) v3 := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 h1 (by omega) h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φUm, μUm, ℓ0, βmid] <;> linarith

set_option maxHeartbeats 8000000 in
theorem edge_Um_3 (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 < 2) :
    φUm a b v0 v1 v2 v3 ≤ nodeN a b (βmid a b) (μUm a b) ℓ0 v0 v1 v2 v3 + φUm a b v0 v1 v2 (v3 + 1) := by
  have habs := abs_sN_hi hb h2 v0 v1 v2 v3 h0 h1 h2' (by omega)
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φUm, μUm, ℓ0, βmid] <;> linarith

theorem edge_Um (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) : EdgeOK a b (βmid a b) (μUm a b) ℓ0 (φUm a b) := by
  intro v0 v1 v2 v3 e0 e1 e2 e3
  exact ⟨fun h => edge_Um_0 hb h2 h3 v0 v1 v2 v3 h e1 e2 e3, fun h => edge_Um_1 hb h2 h3 v0 v1 v2 v3 e0 h e2 e3,
    fun h => edge_Um_2 hb h2 h3 v0 v1 v2 v3 e0 e1 h e3, fun h => edge_Um_3 hb h2 h3 v0 v1 v2 v3 e0 e1 e2 h⟩

theorem μUm_nonneg (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) : ∀ k, 0 ≤ μUm a b k := by
  intro k; unfold μUm; split <;> first | norm_num | linarith

/-- **Free-value lower bound `Um`.** -/
theorem lower_Um (hb : 0 < b) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b) :
    4 * b / 7 / (4 * (a + b)) ≤ trueValue (g8 a b) 8 K7 K7_ne := by
  have hab : b < a := by linarith
  have hZ : (0 : ℝ) < (1) := by first | norm_num | linarith
  have h := cert8 hb hab _ hZ (βmid a b) (μUm a b) ℓ0 (φUm a b) (μUm_nonneg hb h2 h3)
    (by simp [μUm]) (by simp [μUm]; try ring) (fun k hk _ => βmid_eq hb h2 h3 k hk)
    (edge_Um hb h2 h3) (by simp [φUm]) 8 (by norm_num)
  have e0 : φUm a b 0 0 0 0 = ((4/7) * b) := by simp [φUm]
  have e1 : ∑ k ∈ range 8, ∑ τ, |ℓ0 k τ| = 0 := by simp [ℓ0]
  rw [e0, e1, mul_zero, sub_zero] at h
  refine le_trans (le_of_eq ?_) h
  field_simp
  ring

/-! ## Certificate `Uh` -/

noncomputable def μUh (a b : ℝ) : ℕ → ℝ
  | 1 => ((1/7))
  | 2 => ((1/7))
  | 3 => ((1/7))
  | 4 => ((1/7))
  | 5 => ((1/7))
  | 6 => ((1/7))
  | 7 => ((1/7))
  | _ => 0

noncomputable def φUh (a b : ℝ) : ℕ → ℕ → ℕ → ℕ → ℝ
  | 0, 0, 0, 0 => ((2/7) * a - (2/7) * b)
  | 0, 0, 0, 1 => ((2/7) * a - (2/7) * b)
  | 0, 0, 0, 2 => ((2/7) * a)
  | 0, 0, 1, 0 => ((2/7) * a - (2/7) * b)
  | 0, 0, 1, 1 => ((2/7) * a - (2/7) * b)
  | 0, 0, 1, 2 => ((2/7) * a - (2/7) * b)
  | 0, 0, 2, 0 => ((2/7) * a)
  | 0, 0, 2, 1 => ((2/7) * a - (2/7) * b)
  | 0, 0, 2, 2 => ((2/7) * a - (2/7) * b)
  | 0, 1, 0, 0 => ((2/7) * a - (2/7) * b)
  | 0, 1, 0, 1 => ((2/7) * a)
  | 0, 1, 0, 2 => ((2/7) * a + (2/7) * b)
  | 0, 1, 1, 0 => ((2/7) * a - (2/7) * b)
  | 0, 1, 1, 1 => ((2/7) * a - (2/7) * b)
  | 0, 1, 1, 2 => ((2/7) * a)
  | 0, 1, 2, 0 => ((2/7) * a - (2/7) * b)
  | 0, 1, 2, 1 => ((2/7) * a - (2/7) * b)
  | 0, 1, 2, 2 => ((2/7) * a - (2/7) * b)
  | 0, 2, 0, 0 => ((3/7) * a - (1/7) * b)
  | 0, 2, 0, 1 => ((3/7) * a + (1/7) * b)
  | 0, 2, 0, 2 => ((3/7) * a + (5/7) * b)
  | 0, 2, 1, 0 => ((3/7) * a - (3/7) * b)
  | 0, 2, 1, 1 => ((3/7) * a - (1/7) * b)
  | 0, 2, 1, 2 => ((3/7) * a + (1/7) * b)
  | 0, 2, 2, 0 => ((3/7) * a - (3/7) * b)
  | 0, 2, 2, 1 => ((3/7) * a - (3/7) * b)
  | 0, 2, 2, 2 => ((3/7) * a - (1/7) * b)
  | 1, 0, 0, 0 => ((2/7) * a - (2/7) * b)
  | 1, 0, 0, 1 => ((2/7) * a - (2/7) * b)
  | 1, 0, 0, 2 => ((2/7) * a - (2/7) * b)
  | 1, 0, 1, 0 => ((2/7) * a)
  | 1, 0, 1, 1 => ((2/7) * a - (2/7) * b)
  | 1, 0, 1, 2 => ((2/7) * a - (2/7) * b)
  | 1, 0, 2, 0 => ((2/7) * a + (2/7) * b)
  | 1, 0, 2, 1 => ((2/7) * a)
  | 1, 0, 2, 2 => ((2/7) * a - (2/7) * b)
  | 1, 1, 0, 0 => ((1/7) * a - (1/7) * b)
  | 1, 1, 0, 1 => ((1/7) * a - (1/7) * b)
  | 1, 1, 0, 2 => ((1/7) * a + (1/7) * b)
  | 1, 1, 1, 0 => ((1/7) * a - (1/7) * b)
  | 1, 1, 1, 1 => ((1/7) * a - (1/7) * b)
  | 1, 1, 1, 2 => ((1/7) * a - (1/7) * b)
  | 1, 1, 2, 0 => ((1/7) * a + (1/7) * b)
  | 1, 1, 2, 1 => ((1/7) * a - (1/7) * b)
  | 1, 1, 2, 2 => ((1/7) * a - (1/7) * b)
  | 1, 2, 0, 0 => ((1/7) * a - (1/7) * b)
  | 1, 2, 0, 1 => ((1/7) * a + (1/7) * b)
  | 1, 2, 0, 2 => ((1/7) * a + (3/7) * b)
  | 1, 2, 1, 0 => ((1/7) * a - (1/7) * b)
  | 1, 2, 1, 1 => ((1/7) * a - (1/7) * b)
  | 1, 2, 1, 2 => ((1/7) * a + (1/7) * b)
  | 1, 2, 2, 0 => ((1/7) * a - (1/7) * b)
  | 1, 2, 2, 1 => ((1/7) * a - (1/7) * b)
  | 1, 2, 2, 2 => ((1/7) * a - (1/7) * b)
  | 2, 0, 0, 0 => ((3/7) * a - (1/7) * b)
  | 2, 0, 0, 1 => ((3/7) * a - (3/7) * b)
  | 2, 0, 0, 2 => ((3/7) * a - (3/7) * b)
  | 2, 0, 1, 0 => ((3/7) * a + (1/7) * b)
  | 2, 0, 1, 1 => ((3/7) * a - (1/7) * b)
  | 2, 0, 1, 2 => ((3/7) * a - (3/7) * b)
  | 2, 0, 2, 0 => ((3/7) * a + (5/7) * b)
  | 2, 0, 2, 1 => ((3/7) * a + (1/7) * b)
  | 2, 0, 2, 2 => ((3/7) * a - (1/7) * b)
  | 2, 1, 0, 0 => ((1/7) * a - (1/7) * b)
  | 2, 1, 0, 1 => ((1/7) * a - (1/7) * b)
  | 2, 1, 0, 2 => ((1/7) * a - (1/7) * b)
  | 2, 1, 1, 0 => ((1/7) * a + (1/7) * b)
  | 2, 1, 1, 1 => ((1/7) * a - (1/7) * b)
  | 2, 1, 1, 2 => ((1/7) * a - (1/7) * b)
  | 2, 1, 2, 0 => ((1/7) * a + (3/7) * b)
  | 2, 1, 2, 1 => ((1/7) * a + (1/7) * b)
  | 2, 1, 2, 2 => ((1/7) * a - (1/7) * b)
  | 2, 2, 0, 0 => (0)
  | 2, 2, 0, 1 => (0)
  | 2, 2, 0, 2 => ((2/7) * b)
  | 2, 2, 1, 0 => (0)
  | 2, 2, 1, 1 => (0)
  | 2, 2, 1, 2 => (0)
  | 2, 2, 2, 0 => ((2/7) * b)
  | 2, 2, 2, 1 => (0)
  | 2, 2, 2, 2 => (0)
  | _, _, _, _ => 0

set_option maxHeartbeats 8000000 in
theorem edge_Uh_0 (hb : 0 < b) (h3 : 3 * b ≤ a) (v0 v1 v2 v3 : ℕ) (h0 : v0 < 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φUh a b v0 v1 v2 v3 ≤ nodeN a b (βhi a b) (μUh a b) ℓ0 v0 v1 v2 v3 + φUh a b (v0 + 1) v1 v2 v3 := by
  have habs := abs_sN_hi hb (by linarith) v0 v1 v2 v3 (by omega) h1 h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φUh, μUh, ℓ0, βhi] <;> linarith

set_option maxHeartbeats 8000000 in
theorem edge_Uh_1 (hb : 0 < b) (h3 : 3 * b ≤ a) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 < 2) (h2' : v2 ≤ 2) (h3' : v3 ≤ 2) :
    φUh a b v0 v1 v2 v3 ≤ nodeN a b (βhi a b) (μUh a b) ℓ0 v0 v1 v2 v3 + φUh a b v0 (v1 + 1) v2 v3 := by
  have habs := abs_sN_hi hb (by linarith) v0 v1 v2 v3 h0 (by omega) h2' h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φUh, μUh, ℓ0, βhi] <;> linarith

set_option maxHeartbeats 8000000 in
theorem edge_Uh_2 (hb : 0 < b) (h3 : 3 * b ≤ a) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 < 2) (h3' : v3 ≤ 2) :
    φUh a b v0 v1 v2 v3 ≤ nodeN a b (βhi a b) (μUh a b) ℓ0 v0 v1 v2 v3 + φUh a b v0 v1 (v2 + 1) v3 := by
  have habs := abs_sN_hi hb (by linarith) v0 v1 v2 v3 h0 h1 (by omega) h3'
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φUh, μUh, ℓ0, βhi] <;> linarith

set_option maxHeartbeats 8000000 in
theorem edge_Uh_3 (hb : 0 < b) (h3 : 3 * b ≤ a) (v0 v1 v2 v3 : ℕ) (h0 : v0 ≤ 2) (h1 : v1 ≤ 2) (h2' : v2 ≤ 2) (h3' : v3 < 2) :
    φUh a b v0 v1 v2 v3 ≤ nodeN a b (βhi a b) (μUh a b) ℓ0 v0 v1 v2 v3 + φUh a b v0 v1 v2 (v3 + 1) := by
  have habs := abs_sN_hi hb (by linarith) v0 v1 v2 v3 h0 h1 h2' (by omega)
  unfold nodeN
  rw [habs]
  interval_cases v0 <;> interval_cases v1 <;> interval_cases v2 <;> interval_cases v3 <;>
  norm_num [sgHi, sN, φUh, μUh, ℓ0, βhi] <;> linarith

theorem edge_Uh (hb : 0 < b) (h3 : 3 * b ≤ a) : EdgeOK a b (βhi a b) (μUh a b) ℓ0 (φUh a b) := by
  intro v0 v1 v2 v3 e0 e1 e2 e3
  exact ⟨fun h => edge_Uh_0 hb h3 v0 v1 v2 v3 h e1 e2 e3, fun h => edge_Uh_1 hb h3 v0 v1 v2 v3 e0 h e2 e3,
    fun h => edge_Uh_2 hb h3 v0 v1 v2 v3 e0 e1 h e3, fun h => edge_Uh_3 hb h3 v0 v1 v2 v3 e0 e1 e2 h⟩

theorem μUh_nonneg (hb : 0 < b) (h3 : 3 * b ≤ a) : ∀ k, 0 ≤ μUh a b k := by
  intro k; unfold μUh; split <;> first | norm_num | linarith

/-- **Free-value lower bound `Uh`.** -/
theorem lower_Uh (hb : 0 < b) (h3 : 3 * b ≤ a) :
    2 * (a - b) / 7 / (4 * (a + b)) ≤ trueValue (g8 a b) 8 K7 K7_ne := by
  have hab : b < a := by linarith
  have hZ : (0 : ℝ) < (1) := by first | norm_num | linarith
  have h := cert8 hb hab _ hZ (βhi a b) (μUh a b) ℓ0 (φUh a b) (μUh_nonneg hb h3)
    (by simp [μUh]) (by simp [μUh]; try ring) (fun k hk _ => βhi_eq hb h3 k hk)
    (edge_Uh hb h3) (by simp [φUh]) 8 (by norm_num)
  have e0 : φUh a b 0 0 0 0 = ((2/7) * a - (2/7) * b) := by simp [φUh]
  have e1 : ∑ k ∈ range 8, ∑ τ, |ℓ0 k τ| = 0 := by simp [ℓ0]
  rw [e0, e1, mul_zero, sub_zero] at h
  refine le_trans (le_of_eq ?_) h
  field_simp
  ring

#print axioms lower_T13
#print axioms lower_F1
#print axioms lower_F2
#print axioms lower_Um
#print axioms lower_Uh

end CIGAMF.P13.PaperCTwoMag2222
