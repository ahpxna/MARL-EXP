import «LeanPaperCTwoMag1122CertV1»
import «LeanPaperCTwoMag1122FlowV1»

/-!
# Paper C: counts `(1,1,2,2)` — the zero-band value, the free value and the price, at every ratio

`g = (a, -a, b, b, -b, -b)` with `0 < b < a`, `D = ‖g‖₁ = 2a + 4b`, interior budgets
`K5 = {1,…,5}`. Each value below is pinned by a dual certificate of `LeanPaperCTwoMag1122CertV1`
(lower side) and a banded count flow of `LeanPaperCTwoMag1122FlowV1` (upper side).

| ratio `r = a/b` | `D·V_g(0)` | `D·V_g^free` | price `V_g(0)/V_g^free` |
|---|---|---|---|
| `r ≤ 2` | `2(a-b)/3` | `(a-b)/2` | `4/3` |
| `2 ≤ r ≤ 7/3` | `(4b-a)/3` | `(a-b)(3b-a)/(2b)` | `2b(4b-a)/(3(a-b)(3b-a))` |
| `7/3 ≤ r ≤ 5/2` | `(4b-a)/3` | `2(a-b)(3b-a)/(11b-3a)` | `(4b-a)(11b-3a)/(6(a-b)(3b-a))` |
| `5/2 ≤ r ≤ 13/5` | `(a-b)/3` | `2(a-b)(3b-a)/(11b-3a)` | `(11b-3a)/(6(3b-a))` |
| `13/5 ≤ r ≤ 3` | `(a-b)/3` | `2b/5` | `5(a-b)/(6b)` |
| `r ≥ 3` | `(a-b)/3` | `(a-b)/5` | `5/3` |

The price is `4/3` up to `r = 2`, falls to `7/6` at `r = 5/2`, rises to `4/3` at `r = 13/5`,
then linearly to `5/3` at `r = 3`, and stays there: a non-monotone law in the ratio, with the
free value, not the zero-band value, carrying the non-monotonicity.
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

/-- A flow whose band is at most `η` and whose budget costs are at most `T` bounds the value. -/
theorem value_le_of (hb : 0 < b) (hab : b < a) (η e T : ℝ) (he : e ≤ η)
    (hfl : ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F e
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ T) :
    trueValue (g6 a b) η K5 K5_ne ≤ T := by
  obtain ⟨F, hF, hB, hk⟩ := hfl
  exact (value_le_flow hb hab η F hF (band_mono ty6 F e η hB he (by norm_num))).trans
    (Finset.sup'_le _ _ hk)

/-! ## 1. The zero-band value -/

theorem zero_L (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    trueValue (g6 a b) 0 K5 K5_ne = 2 * (a - b) / 3 / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  apply le_antisymm
  · exact value_le_of hb hab 0 0 _ le_rfl (flow_L0 hb hab h2)
  · refine le_trans (le_of_eq ?_) (cert_AL hb hab h2 0 le_rfl)
    simp only [zero_div, zero_mul, sub_zero, P_AL]
    field_simp
    ring

theorem zero_M (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h5 : 2 * a ≤ 5 * b) :
    trueValue (g6 a b) 0 K5 K5_ne = (4 * b - a) / 3 / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  apply le_antisymm
  · exact value_le_of hb hab 0 0 _ le_rfl (flow_M0 hb hab h2 h5)
  · refine le_trans (le_of_eq ?_) (cert_AM hb hab h2 h5 0 le_rfl)
    simp only [zero_div, zero_mul, sub_zero, P_AM]
    field_simp
    ring

theorem zero_H (hb : 0 < b) (hab : b < a) (h5 : 5 * b ≤ 2 * a) :
    trueValue (g6 a b) 0 K5 K5_ne = (a - b) / 3 / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  apply le_antisymm
  · rcases le_total a (3 * b) with h3 | h3
    · exact value_le_of hb hab 0 0 _ le_rfl (flow_H0M hb hab h5 h3)
    · exact value_le_of hb hab 0 0 _ le_rfl (flow_H0H hb hab h3)
  · refine le_trans (le_of_eq ?_) (cert_Band hb hab 0 le_rfl)
    simp only [zero_div, zero_mul, sub_zero, P_Band]
    field_simp
    ring

/-! ## 2. The free value (the band at `η = m = 6` is vacuous) -/

theorem free_L (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    trueValue (g6 a b) 6 K5 K5_ne = (a - b) / 2 / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  apply le_antisymm
  · exact value_le_of hb hab 6 1 _ (by norm_num) (flow_Lf hb hab h2)
  · refine le_trans (le_of_eq ?_) (cert_Lf hb hab h2 6 (by norm_num))
    simp only [L_Lf, abs_zero, add_zero, mul_zero, sub_zero, P_Lf]
    field_simp
    ring

theorem free_M1 (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b) :
    trueValue (g6 a b) 6 K5 K5_ne = (a - b) * (3 * b - a) / (2 * b) / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  apply le_antisymm
  · exact value_le_of hb hab 6 1 _ (by norm_num) (flow_M1f hb hab h2 h7)
  · refine le_trans (le_of_eq ?_) (cert_M1f hb hab h2 h7 6 (by norm_num))
    simp only [L_M1f, abs_zero, add_zero, mul_zero, sub_zero, P_M1f]
    field_simp
    ring

theorem free_M23 (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b) :
    trueValue (g6 a b) 6 K5 K5_ne
      = 2 * (a - b) * (3 * b - a) / (11 * b - 3 * a) / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  have hq : 0 < 11 * b - 3 * a := by linarith
  apply le_antisymm
  · refine value_le_of hb hab 6 _ _ ?_ (flow_M23f hb hab h7 h13)
    rw [div_le_iff₀ hq]; linarith
  · refine le_trans (le_of_eq ?_) (cert_M23f hb hab h7 h13 6 (by norm_num))
    simp only [L_M23f, abs_zero, add_zero, mul_zero, sub_zero, P_M23f]
    field_simp
    ring

theorem free_M4 (hb : 0 < b) (hab : b < a) (h13 : 13 * b ≤ 5 * a) (h3 : a ≤ 3 * b) :
    trueValue (g6 a b) 6 K5 K5_ne = 2 * b / 5 / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  have hq : 0 < 5 * (a - b) := by linarith
  apply le_antisymm
  · refine value_le_of hb hab 6 _ _ ?_ (flow_M4f hb hab h13 h3)
    rw [div_le_iff₀ hq]; linarith
  · refine le_trans (le_of_eq ?_) (cert_M4f hb hab h13 h3 6 (by norm_num))
    simp only [L_M4f, abs_zero, add_zero, mul_zero, sub_zero, P_M4f]
    field_simp
    ring

theorem free_H (hb : 0 < b) (hab : b < a) (h3 : 3 * b ≤ a) :
    trueValue (g6 a b) 6 K5 K5_ne = (a - b) / 5 / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  apply le_antisymm
  · exact value_le_of hb hab 6 (2 / 5) _ (by norm_num) (flow_Hf hb hab h3)
  · refine le_trans (le_of_eq ?_) (cert_Hf hb hab h3 6 (by norm_num))
    simp only [L_Hf, abs_zero, add_zero, mul_zero, sub_zero, P_Hf]
    field_simp
    ring

/-- The free value is `trueValue` at `η = m = 6`. -/
theorem vfree_eq : Vfree (g6 a b) K5 K5_ne = trueValue (g6 a b) 6 K5 K5_ne := by
  unfold Vfree
  norm_num

/-! ## 3. The price law in the ratio -/

theorem price_L (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) :
    trueValue (g6 a b) 0 K5 K5_ne = 4 / 3 * Vfree (g6 a b) K5 K5_ne := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  rw [vfree_eq, zero_L hb hab h2, free_L hb hab h2]
  field_simp
  ring

theorem price_M1 (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b) :
    trueValue (g6 a b) 0 K5 K5_ne
      = 2 * b * (4 * b - a) / (3 * (a - b) * (3 * b - a)) * Vfree (g6 a b) K5 K5_ne := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  have h1 : 0 < a - b := by linarith
  have h3 : 0 < 3 * b - a := by linarith
  rw [vfree_eq, zero_M hb hab h2 (by linarith), free_M1 hb hab h2 h7]
  field_simp
  ring

theorem price_M2 (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h5 : 2 * a ≤ 5 * b) :
    trueValue (g6 a b) 0 K5 K5_ne
      = (4 * b - a) * (11 * b - 3 * a) / (6 * (a - b) * (3 * b - a)) * Vfree (g6 a b) K5 K5_ne := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  have h1 : 0 < a - b := by linarith
  have h3 : 0 < 3 * b - a := by linarith
  have hq : 0 < 11 * b - 3 * a := by linarith
  rw [vfree_eq, zero_M hb hab (by linarith) h5, free_M23 hb hab h7 (by linarith)]
  field_simp
  ring

theorem price_M3 (hb : 0 < b) (hab : b < a) (h5 : 5 * b ≤ 2 * a) (h13 : 5 * a ≤ 13 * b) :
    trueValue (g6 a b) 0 K5 K5_ne
      = (11 * b - 3 * a) / (6 * (3 * b - a)) * Vfree (g6 a b) K5 K5_ne := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  have h1 : 0 < a - b := by linarith
  have h3 : 0 < 3 * b - a := by linarith
  have hq : 0 < 11 * b - 3 * a := by linarith
  rw [vfree_eq, zero_H hb hab h5, free_M23 hb hab (by linarith) h13]
  field_simp
  ring

theorem price_M4 (hb : 0 < b) (hab : b < a) (h13 : 13 * b ≤ 5 * a) (h3 : a ≤ 3 * b) :
    trueValue (g6 a b) 0 K5 K5_ne = 5 * (a - b) / (6 * b) * Vfree (g6 a b) K5 K5_ne := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  rw [vfree_eq, zero_H hb hab (by linarith), free_M4 hb hab h13 h3]
  field_simp
  ring

theorem price_H (hb : 0 < b) (hab : b < a) (h3 : 3 * b ≤ a) :
    trueValue (g6 a b) 0 K5 K5_ne = 5 / 3 * Vfree (g6 a b) K5 K5_ne := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  rw [vfree_eq, zero_H hb hab (by linarith), free_H hb hab h3]
  field_simp
  ring

/-- **The price is not monotone in the ratio**: `4/3` at `a = 2b`, `7/6` at `2a = 5b`, `5/3` at
`a = 3b`. -/
theorem price_nonmonotone (hb : 0 < b) :
    trueValue (g6 (2 * b) b) 0 K5 K5_ne = 4 / 3 * Vfree (g6 (2 * b) b) K5 K5_ne
      ∧ trueValue (g6 (5 * b / 2) b) 0 K5 K5_ne = 7 / 6 * Vfree (g6 (5 * b / 2) b) K5 K5_ne
      ∧ trueValue (g6 (3 * b) b) 0 K5 K5_ne = 5 / 3 * Vfree (g6 (3 * b) b) K5 K5_ne := by
  refine ⟨price_L hb (by linarith) le_rfl, ?_, price_H hb (by linarith) le_rfl⟩
  have h := price_M3 (a := 5 * b / 2) hb (by linarith) (by linarith) (by linarith)
  rw [h]
  congr 1
  field_simp
  ring

#print axioms zero_L
#print axioms zero_M
#print axioms zero_H
#print axioms free_L
#print axioms free_M1
#print axioms free_M23
#print axioms free_M4
#print axioms free_H
#print axioms price_L
#print axioms price_M1
#print axioms price_M2
#print axioms price_M3
#print axioms price_M4
#print axioms price_H
#print axioms price_nonmonotone

end CIGAMF.P13.PaperCTwoMag1122
