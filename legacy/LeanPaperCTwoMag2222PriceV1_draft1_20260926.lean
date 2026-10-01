import «LeanPaperCTwoMag2222ZeroV1»
import «LeanPaperCTwoMag2222FreeV1»

/-!
# Paper C: counts `(2,2,2,2)` — the price law in the ratio

`g = (a, a, -a, -a, b, b, -b, -b)`, `q = a² - 10ab + 17b²` (smaller root `a/b = 5 - 2√2`).
With `r = a/b`, the price `V_g(0)/V_g^free` is

| region | price |
|---|---|
| `r ≤ 2` | `9/8` |
| `2 ≤ r`, `q ≥ 0`, `r ≤ 3` (i.e. `r ≤ 5-2√2`) | `(5b-a)²/(8b(3b-a))` |
| `2 ≤ r`, `q ≤ 0`, `r ≤ 7/3` | `(5b-a)(17b-5a)/(8a(3b-a))` |
| `7/3 ≤ r ≤ 17/7` | `(a-b)(17b-5a)/(4a(3b-a))` |
| `17/7 ≤ r ≤ 3` | `7(a-b)/(8b)` |
| `r ≥ 3` | `7/4` |

It rises from `9/8` to a local maximum `(1+√2)/2` at `r = 5-2√2`, where the two branches meet
exactly because `q = 0`, dips to `8/7` at `7/3`, and rises through `5/4` at `17/7` to `7/4` at
`3`. The zero-band value is `LeanPaperCTwoMag2222ZeroV1`, the free value
`LeanPaperCTwoMag2222FreeV1`.
-/

namespace CIGAMF.P13.PaperCTwoMag2222

open Finset
open CIGAMF.P13.CFinal CIGAMF.P13.PaperCHorizon CIGAMF.P13.PaperCStabilityEndgame
open CIGAMF.P13.PaperCTypedFlow CIGAMF.P13.PaperCFreeBand

variable {a b : ℝ}

theorem vfree8 : Vfree (g8 a b) K7 K7_ne = trueValue (g8 a b) 8 K7 K7_ne := by
  unfold Vfree; norm_num

/-- `(N₀/N_f)·(N_f/D) = N₀/D`. -/
theorem ratio_mul8 (N0 Nf D : ℝ) (hNf : Nf ≠ 0) : N0 / Nf * (Nf / D) = N0 / D := by
  rw [div_mul_div_comm, mul_comm Nf D, mul_div_mul_right _ _ hNf]

theorem price2222_1 (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    trueValue (g8 a b) 0 K7 K7_ne = 9 / 8 * Vfree (g8 a b) K7 K7_ne := by
  have hNf : 2 * (a - b) / 3 ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero (by linarith)) (by norm_num)
  rw [vfree8, zero2222_L hb hab h2, free2222_R1 hb hab h2]
  rw [show (9 : ℝ) / 8 = (3 * (a - b) / 4) / (2 * (a - b) / 3) by
    field_simp; ring, ratio_mul8 _ _ _ hNf]

theorem price2222_2 (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h3 : a ≤ 3 * b)
    (hq : 0 ≤ a ^ 2 - 10 * a * b + 17 * b ^ 2) :
    trueValue (g8 a b) 0 K7 K7_ne
      = (5 * b - a) ^ 2 / (8 * b * (3 * b - a)) * Vfree (g8 a b) K7 K7_ne := by
  -- `q ≥ 0` with `2b ≤ a ≤ 3b` forces `a ≤ 7b/3`
  have h7 : 3 * a ≤ 7 * b := by nlinarith
  have h3' : 0 < 3 * b - a := by nlinarith
  have h5 : 0 < 5 * b - a := by linarith
  have hNf : 2 * b * (3 * b - a) / (5 * b - a) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hb.ne') h3'.ne') h5.ne'
  rw [vfree8, zero2222_M hb hab h2 h7, free2222_R2 hb hab h2 h3 hq]
  rw [show (5 * b - a) ^ 2 / (8 * b * (3 * b - a))
      = ((5 * b - a) / 4) / (2 * b * (3 * b - a) / (5 * b - a)) by
    field_simp; ring, ratio_mul8 _ _ _ hNf]

theorem price2222_3 (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a)
    (hq : a ^ 2 - 10 * a * b + 17 * b ^ 2 ≤ 0) (h7 : 3 * a ≤ 7 * b) :
    trueValue (g8 a b) 0 K7 K7_ne
      = (5 * b - a) * (17 * b - 5 * a) / (8 * a * (3 * b - a)) * Vfree (g8 a b) K7 K7_ne := by
  have h3' : 0 < 3 * b - a := by linarith
  have h17 : 0 < 17 * b - 5 * a := by linarith
  have ha : 0 < a := by linarith
  have hNf : 2 * a * (3 * b - a) / (17 * b - 5 * a) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ha.ne') h3'.ne') h17.ne'
  rw [vfree8, zero2222_M hb hab h2 h7, free2222_R3 hb hab h2 hq (by linarith)]
  rw [show (5 * b - a) * (17 * b - 5 * a) / (8 * a * (3 * b - a))
      = ((5 * b - a) / 4) / (2 * a * (3 * b - a) / (17 * b - 5 * a)) by
    field_simp; ring, ratio_mul8 _ _ _ hNf]

theorem price2222_4 (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h17 : 7 * a ≤ 17 * b) :
    trueValue (g8 a b) 0 K7 K7_ne
      = (a - b) * (17 * b - 5 * a) / (4 * a * (3 * b - a)) * Vfree (g8 a b) K7 K7_ne := by
  have h3' : 0 < 3 * b - a := by linarith
  have h17' : 0 < 17 * b - 5 * a := by linarith
  have ha : 0 < a := by linarith
  -- on `7/3 ≤ r ≤ 17/7` the quadratic `q` is negative
  have hq : a ^ 2 - 10 * a * b + 17 * b ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 h7) (sub_nonneg.2 h17), mul_nonneg hb.le (sub_nonneg.2 h7)]
  have hNf : 2 * a * (3 * b - a) / (17 * b - 5 * a) ≠ 0 :=
    div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ha.ne') h3'.ne') h17'.ne'
  rw [vfree8, zero2222_H hb hab h7, free2222_R3 hb hab (by linarith) hq h17]
  rw [show (a - b) * (17 * b - 5 * a) / (4 * a * (3 * b - a))
      = ((a - b) / 2) / (2 * a * (3 * b - a) / (17 * b - 5 * a)) by
    field_simp; ring, ratio_mul8 _ _ _ hNf]

theorem price2222_5 (hb : 0 < b) (hab : b < a) (h17 : 17 * b ≤ 7 * a) (h3 : a ≤ 3 * b) :
    trueValue (g8 a b) 0 K7 K7_ne = 7 * (a - b) / (8 * b) * Vfree (g8 a b) K7 K7_ne := by
  have hNf : 4 * b / 7 ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hb.ne') (by norm_num)
  rw [vfree8, zero2222_H hb hab (by linarith), free2222_R4 hb hab h17 h3]
  rw [show 7 * (a - b) / (8 * b) = ((a - b) / 2) / (4 * b / 7) by
    field_simp; ring, ratio_mul8 _ _ _ hNf]

theorem price2222_6 (hb : 0 < b) (hab : b < a) (h3 : 3 * b ≤ a) :
    trueValue (g8 a b) 0 K7 K7_ne = 7 / 4 * Vfree (g8 a b) K7 K7_ne := by
  have hNf : 2 * (a - b) / 7 ≠ 0 := div_ne_zero (mul_ne_zero two_ne_zero (by linarith)) (by norm_num)
  rw [vfree8, zero2222_H hb hab (by linarith), free2222_R5 hb hab h3]
  rw [show (7 : ℝ) / 4 = ((a - b) / 2) / (2 * (a - b) / 7) by
    field_simp; ring, ratio_mul8 _ _ _ hNf]

#print axioms price2222_1
#print axioms price2222_2
#print axioms price2222_3
#print axioms price2222_4
#print axioms price2222_5
#print axioms price2222_6

end CIGAMF.P13.PaperCTwoMag2222
