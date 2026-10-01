import «LeanPaperCTwoMag1122PriceV1»
import «LeanPaperCTwoMag1122CertV2»
import «LeanPaperCTwoMag1122KinkV1»

/-!
# Paper C: counts `(1,1,2,2)` — the band frontier at every ratio and every band

`g = (a, -a, b, b, -b, -b)`, `0 < b < a`, `D = 2a + 4b`. For every `η ≥ 0`, `D·V_g(η)` is the
maximum of the lines below (`r = a/b`):

| region | lines | theorem |
|---|---|---|
| `r ≤ 2` | `(a-b)(2/3 - η/6)`, `(a-b)/2` | `frontier_L` |
| `2 < r ≤ 7/3` | `A`, `M`, `(a-b)(3b-a)/(2b)` | `frontier_M1` |
| `7/3 ≤ r ≤ 5/2` | `A`, `L2`, `2(a-b)(3b-a)/(11b-3a)` | `frontier_M2` |
| `5/2 < r < 13/5` | `B`, `A`, `L2`, `2(a-b)(3b-a)/(11b-3a)` | `frontier_M3` |
| `13/5 ≤ r ≤ 3` | `B`, `2b/5` | `frontier_M4` |
| `3 ≤ r` | `B`, `(a-b)/5` | `frontier_H` |

with `A = (4b-a)/3 - η(a-b)/6`, `B = (a-b)(1-η)/3`,
`M = (a-b)(3b-a)/(2b) + (1-η)(3b-a)²/(6b)`,
`L2 = (a-b)(3b-a)(2a - η(3b-a))/(3(15ab-3a²-16b²))`.

Lower sides: one certificate per line, each valid at every `η ≥ 0`
(`LeanPaperCTwoMag1122CertV1`, `LeanPaperCTwoMag1122CertV2`). Upper sides: between two
consecutive kinks, the mixture of the flows at its ends (`up_seg`, via `mixTwo`), whose band and
budget costs interpolate linearly; past the last kink, the free flow. The kinks are
`η = 2(a-2b)/(5b-a)` and `1` on the second region; `2(5a²-25ab+32b²)/((a-b)(17b-5a))` and
`4(8b-3a)/(11b-3a)` on the third; `2(2a-5b)/(a-b)` and the same two on the fourth;
`(5a-11b)/(5(a-b))` on the fifth; `2/5` on the last.
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

/-! ## The lines -/

/-- The line `A`. -/
noncomputable def lineA (a b η : ℝ) : ℝ := (4 * b - a) / 3 - η * (a - b) / 6

/-- The band line `B`. -/
noncomputable def lineB (a b η : ℝ) : ℝ := (a - b) * (1 - η) / 3

/-- The middle line `M` of `2b ≤ a ≤ 7b/3`. -/
noncomputable def lineM (a b η : ℝ) : ℝ :=
  (a - b) * (3 * b - a) / (2 * b) + (1 - η) * (3 * b - a) ^ 2 / (6 * b)

/-- The line `L2` of `7b/3 ≤ a ≤ 13b/5`. -/
noncomputable def lineL2 (a b η : ℝ) : ℝ :=
  (a - b) * (3 * b - a) * (2 * a - η * (3 * b - a)) / (3 * (15 * a * b - 3 * a * a - 16 * b * b))

/-! ## Upper sides: the segment between two flows -/

/-- Two flows with bands `e₀ < e₁` whose budget costs lie on the affine line `α - βη` at their
bands give that line on the whole segment `[e₀, e₁]`. -/
theorem up_seg (hb : 0 < b) (hab : b < a) (α β e0 e1 X0 X1 η : ℝ) (he : e0 < e1)
    (h0 : e0 ≤ η) (h1 : η ≤ e1) (hX0 : X0 = α - β * e0) (hX1 : X1 = α - β * e1)
    (F0 : ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F e0
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ X0 / (2 * a + 4 * b))
    (F1 : ∃ F : LayeredFlow (CState 4 6), CountFeasibleH ty6 F ∧ FlowBand ty6 F e1
      ∧ ∀ k ∈ K5, flowObj (typedCost ty6 (wt a b)) F k ≤ X1 / (2 * a + 4 * b)) :
    trueValue (g6 a b) η K5 K5_ne ≤ (α - β * η) / (2 * a + 4 * b) := by
  obtain ⟨F, hF, hFb, hFk⟩ := F0
  obtain ⟨G, hG, hGb, hGk⟩ := F1
  have hd : 0 < e1 - e0 := sub_pos.2 he
  have hd' : e1 - e0 ≠ 0 := hd.ne'
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  have hθ0 : 0 ≤ (η - e0) / (e1 - e0) := div_nonneg (by linarith) hd.le
  have hθ1 : (η - e0) / (e1 - e0) ≤ 1 := (div_le_one hd).2 (by linarith)
  have hθ' : 0 ≤ 1 - (η - e0) / (e1 - e0) := by linarith
  refine value_le_of hb hab η η _ le_rfl ⟨mixTwo _ hθ0 hθ1 F G,
    mixTwo_feasible ty6 _ hθ0 hθ1 F G hF hG, ?_, fun k hk => ?_⟩
  · have hB := mixTwo_band ty6 _ hθ0 hθ1 F G hF hG e0 e1 hFb hGb
    convert hB using 1
    field_simp
    try ring
  · rw [mixTwo_obj]
    calc (1 - (η - e0) / (e1 - e0)) * flowObj (typedCost ty6 (wt a b)) F k
          + (η - e0) / (e1 - e0) * flowObj (typedCost ty6 (wt a b)) G k
        ≤ (1 - (η - e0) / (e1 - e0)) * (X0 / (2 * a + 4 * b))
          + (η - e0) / (e1 - e0) * (X1 / (2 * a + 4 * b)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hFk k hk) hθ')
            (mul_le_mul_of_nonneg_left (hGk k hk) hθ0)
      _ = (α - β * η) / (2 * a + 4 * b) := by
          rw [hX0, hX1]
          field_simp
          try ring

/-! ## Lower sides: one certificate per line, at every band -/

theorem low_AL (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (η : ℝ) (hη : 0 ≤ η) :
    (a - b) * (2 / 3 - η / 6) / (2 * a + 4 * b) ≤ trueValue (g6 a b) η K5 K5_ne := by
  have h := cert_AL hb hab h2 η hη
  have e1 : L_AL a b 1 = 0 := by simp [L_AL]
  have e2 : L_AL a b 2 = a - b := by simp [L_AL]; try ring
  have e3 : L_AL a b 3 = 0 := by simp [L_AL]
  have e4 : L_AL a b 4 = -(a - b) := by simp [L_AL]; try ring
  have e5 : L_AL a b 5 = 0 := by simp [L_AL]
  rw [e1, e2, e3, e4, e5, abs_zero, abs_neg, abs_of_pos (sub_pos.2 hab)] at h
  refine le_trans (le_of_eq ?_) h
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  simp only [P_AL]
  field_simp
  try ring

theorem low_Lf (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (η : ℝ) (hη : 0 ≤ η) :
    (a - b) / 2 / (2 * a + 4 * b) ≤ trueValue (g6 a b) η K5 K5_ne := by
  refine le_trans (le_of_eq ?_) (cert_Lf hb hab h2 η hη)
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  simp only [L_Lf, abs_zero, add_zero, mul_zero, sub_zero, P_Lf]
  field_simp
  try ring

theorem low_A (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h5 : 2 * a ≤ 5 * b) (η : ℝ)
    (hη : 0 ≤ η) : lineA a b η / (2 * a + 4 * b) ≤ trueValue (g6 a b) η K5 K5_ne := by
  have h := cert_AM hb hab h2 h5 η hη
  have e1 : L_AM a b 1 = 0 := by simp [L_AM]
  have e2 : L_AM a b 2 = a - b := by simp [L_AM]; try ring
  have e3 : L_AM a b 3 = 0 := by simp [L_AM]
  have e4 : L_AM a b 4 = -(a - b) := by simp [L_AM]; try ring
  have e5 : L_AM a b 5 = 0 := by simp [L_AM]
  rw [e1, e2, e3, e4, e5, abs_zero, abs_neg, abs_of_pos (sub_pos.2 hab)] at h
  refine le_trans (le_of_eq ?_) h
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  simp only [P_AM, lineA]
  field_simp
  try ring

theorem low_A3 (hb : 0 < b) (hab : b < a) (h5 : 5 * b ≤ 2 * a) (h13 : 5 * a ≤ 13 * b) (η : ℝ)
    (hη : 0 ≤ η) : lineA a b η / (2 * a + 4 * b) ≤ trueValue (g6 a b) η K5 K5_ne := by
  have h := cert_AM3 hb hab h5 h13 η hη
  have e1 : L_AM3 a b 1 = 0 := by simp [L_AM3]
  have e2 : L_AM3 a b 2 = a - b := by simp [L_AM3]; try ring
  have e3 : L_AM3 a b 3 = 0 := by simp [L_AM3]
  have e4 : L_AM3 a b 4 = -(a - b) := by simp [L_AM3]; try ring
  have e5 : L_AM3 a b 5 = 0 := by simp [L_AM3]
  rw [e1, e2, e3, e4, e5, abs_zero, abs_neg, abs_of_pos (sub_pos.2 hab)] at h
  refine le_trans (le_of_eq ?_) h
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  simp only [P_AM3, lineA]
  field_simp
  try ring

theorem low_B (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) :
    lineB a b η / (2 * a + 4 * b) ≤ trueValue (g6 a b) η K5 K5_ne := by
  have h := cert_Band hb hab η hη
  have e1 : L_Band a b 1 = -(a - b) := by simp [L_Band]; try ring
  have e2 : L_Band a b 2 = 0 := by simp [L_Band]
  have e3 : L_Band a b 3 = 0 := by simp [L_Band]
  have e4 : L_Band a b 4 = 0 := by simp [L_Band]
  have e5 : L_Band a b 5 = a - b := by simp [L_Band]; try ring
  rw [e1, e2, e3, e4, e5, abs_zero, abs_neg, abs_of_pos (sub_pos.2 hab)] at h
  refine le_trans (le_of_eq ?_) h
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  simp only [P_Band, lineB]
  field_simp
  try ring

theorem low_M (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b) (η : ℝ)
    (hη : 0 ≤ η) : lineM a b η / (2 * a + 4 * b) ≤ trueValue (g6 a b) η K5 K5_ne := by
  have h := cert_C2 hb hab h2 h7 η hη
  have e1 : L_C2 a b 1 = 0 := by simp [L_C2]
  have e2 : L_C2 a b 2 = (3 * b - a) ^ 2 := by simp [L_C2]; try ring
  have e3 : L_C2 a b 3 = 0 := by simp [L_C2]
  have e4 : L_C2 a b 4 = -((3 * b - a) ^ 2) := by simp [L_C2]; try ring
  have e5 : L_C2 a b 5 = 0 := by simp [L_C2]
  rw [e1, e2, e3, e4, e5, abs_zero, abs_neg, abs_of_nonneg (sq_nonneg (3 * b - a))] at h
  refine le_trans (le_of_eq ?_) h
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  have hb' : b ≠ 0 := hb.ne'
  simp only [P_C2, lineM]
  field_simp
  try ring

theorem low_L2 (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b) (η : ℝ)
    (hη : 0 ≤ η) : lineL2 a b η / (2 * a + 4 * b) ≤ trueValue (g6 a b) η K5 K5_ne := by
  have h := cert_CL2 hb hab h7 h13 η hη
  have e1 : L_CL2 a b 1 = 0 := by simp [L_CL2]
  have e2 : L_CL2 a b 2 = (a - b) * (3 * b - a) ^ 2 := by simp [L_CL2]; try ring
  have e3 : L_CL2 a b 3 = 0 := by simp [L_CL2]
  have e4 : L_CL2 a b 4 = -((a - b) * (3 * b - a) ^ 2) := by simp [L_CL2]; try ring
  have e5 : L_CL2 a b 5 = 0 := by simp [L_CL2]
  rw [e1, e2, e3, e4, e5, abs_zero, abs_neg,
    abs_of_nonneg (mul_nonneg (sub_nonneg.2 hab.le) (sq_nonneg (3 * b - a)))] at h
  refine le_trans (le_of_eq ?_) h
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  have hq : 15 * a * b - 3 * a * a - 16 * b * b ≠ 0 := by
    apply ne_of_gt
    nlinarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a),
      mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b),
      mul_nonneg (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13 : (0:ℝ) ≤ 13 * b - 5 * a),
      mul_pos hb hb]
  simp only [P_CL2, lineL2]
  field_simp
  try ring

theorem low_M1f (hb : 0 < b) (hab : b < a) (h2 : 2 * b ≤ a) (h7 : 3 * a ≤ 7 * b) (η : ℝ)
    (hη : 0 ≤ η) :
    (a - b) * (3 * b - a) / (2 * b) / (2 * a + 4 * b) ≤ trueValue (g6 a b) η K5 K5_ne := by
  refine le_trans (le_of_eq ?_) (cert_M1f hb hab h2 h7 η hη)
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  have hb' : b ≠ 0 := hb.ne'
  simp only [L_M1f, abs_zero, add_zero, mul_zero, sub_zero, P_M1f]
  field_simp
  try ring

theorem low_M23f (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h13 : 5 * a ≤ 13 * b) (η : ℝ)
    (hη : 0 ≤ η) :
    2 * (a - b) * (3 * b - a) / (11 * b - 3 * a) / (2 * a + 4 * b)
      ≤ trueValue (g6 a b) η K5 K5_ne := by
  refine le_trans (le_of_eq ?_) (cert_M23f hb hab h7 h13 η hη)
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  have h11 : 11 * b - 3 * a ≠ 0 := by apply ne_of_gt; linarith
  simp only [L_M23f, abs_zero, add_zero, mul_zero, sub_zero, P_M23f]
  field_simp
  try ring

theorem low_M4f (hb : 0 < b) (hab : b < a) (h13 : 13 * b ≤ 5 * a) (h3 : a ≤ 3 * b) (η : ℝ)
    (hη : 0 ≤ η) : 2 * b / 5 / (2 * a + 4 * b) ≤ trueValue (g6 a b) η K5 K5_ne := by
  refine le_trans (le_of_eq ?_) (cert_M4f hb hab h13 h3 η hη)
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  simp only [L_M4f, abs_zero, add_zero, mul_zero, sub_zero, P_M4f]
  field_simp
  try ring

theorem low_Hf (hb : 0 < b) (hab : b < a) (h3 : 3 * b ≤ a) (η : ℝ) (hη : 0 ≤ η) :
    (a - b) / 5 / (2 * a + 4 * b) ≤ trueValue (g6 a b) η K5 K5_ne := by
  refine le_trans (le_of_eq ?_) (cert_Hf hb hab h3 η hη)
  have hD : 2 * a + 4 * b ≠ 0 := by apply ne_of_gt; linarith
  simp only [L_Hf, abs_zero, add_zero, mul_zero, sub_zero, P_Hf]
  field_simp
  try ring

/-! ## The kinks -/

theorem kinkK2_pos (hb : 0 < b) (hab : b < a) (h13 : 5 * a < 13 * b) :
    0 < 2 * (5 * a * a - 25 * a * b + 32 * b * b) / ((a - b) * (17 * b - 5 * a)) := by
  apply div_pos
  · nlinarith [sq_nonneg (2 * a - 5 * b), mul_pos hb hb]
  · exact mul_pos (by linarith) (by linarith)

/-- `L2` meets the free value strictly after it meets `A`: the difference of the two kinks,
cross-multiplied, is `6(13b-5a)(15ab-3a²-16b²)`. -/
theorem kinkK2_lt_F (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h13 : 5 * a < 13 * b) :
    2 * (5 * a * a - 25 * a * b + 32 * b * b) / ((a - b) * (17 * b - 5 * a))
      < 4 * (8 * b - 3 * a) / (11 * b - 3 * a) := by
  have hq : 0 < 15 * a * b - 3 * a * a - 16 * b * b := by
    nlinarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13.le : (0:ℝ) ≤ 13 * b - 5 * a),
      mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b),
      mul_nonneg (sub_nonneg.2 h13.le : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13.le : (0:ℝ) ≤ 13 * b - 5 * a),
      mul_pos hb hb]
  rw [div_lt_div_iff₀ (mul_pos (by linarith) (by linarith)) (by linarith)]
  nlinarith [mul_pos (sub_pos.2 h13) hq]

/-- The band line meets `A` strictly before `L2` does: cross-multiplied, the difference is
`6(a-b)(13b-5a)(3b-a)`. -/
theorem kink0_lt_K2 (hb : 0 < b) (hab : b < a) (h5 : 5 * b < 2 * a) (h13 : 5 * a < 13 * b) :
    2 * (2 * a - 5 * b) / (a - b)
      < 2 * (5 * a * a - 25 * a * b + 32 * b * b) / ((a - b) * (17 * b - 5 * a)) := by
  rw [div_lt_div_iff₀ (by linarith) (mul_pos (by linarith) (by linarith))]
  nlinarith [mul_pos (mul_pos (sub_pos.2 hab) (sub_pos.2 h13)) (by linarith : (0:ℝ) < 3 * b - a)]

/-! ## The frontier, region by region -/

theorem frontier_L (hb : 0 < b) (hab : b < a) (h2 : a ≤ 2 * b) (η : ℝ) (hη : 0 ≤ η) :
    trueValue (g6 a b) η K5 K5_ne
      = max ((a - b) * (2 / 3 - η / 6)) ((a - b) / 2) / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  apply le_antisymm
  · rcases le_or_gt η 1 with h1 | h1
    · refine (up_seg hb hab (2 * (a - b) / 3) ((a - b) / 6) 0 1 (2 * (a - b) / 3) ((a - b) / 2) η
        (by norm_num) hη h1 (by ring) (by ring) (flow_L0 hb hab h2) (flow_Lf hb hab h2)).trans ?_
      refine div_le_div_of_nonneg_right ?_ hD.le
      exact le_trans (le_of_eq (by ring)) (le_max_left _ _)
    · refine (value_le_of hb hab η 1 _ h1.le (flow_Lf hb hab h2)).trans ?_
      exact div_le_div_of_nonneg_right (le_max_right _ _) hD.le
  · rw [div_le_iff₀ hD]
    refine max_le ?_ ?_
    · have := low_AL hb hab h2 η hη; rwa [div_le_iff₀ hD] at this
    · have := low_Lf hb hab h2 η hη; rwa [div_le_iff₀ hD] at this

theorem frontier_M1 (hb : 0 < b) (hab : b < a) (h2 : 2 * b < a) (h7 : 3 * a ≤ 7 * b)
    (η : ℝ) (hη : 0 ≤ η) :
    trueValue (g6 a b) η K5 K5_ne
      = max (max (lineA a b η) (lineM a b η)) ((a - b) * (3 * b - a) / (2 * b))
        / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  have hb' : b ≠ 0 := hb.ne'
  have h5b : 5 * b - a ≠ 0 := by apply ne_of_gt; linarith
  have h5b' : b * 5 - a ≠ 0 := fun h => h5b (by linear_combination h)
  have he1p : 0 < 2 * (a - 2 * b) / (5 * b - a) := div_pos (by linarith) (by linarith)
  have he1l : 2 * (a - 2 * b) / (5 * b - a) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  apply le_antisymm
  · rcases le_or_gt η (2 * (a - 2 * b) / (5 * b - a)) with hA | hA
    · refine (up_seg hb hab ((4 * b - a) / 3) ((a - b) / 6) 0 _ ((4 * b - a) / 3)
        (2 * b * (3 * b - a) / (5 * b - a)) η he1p hη hA (by ring) (by field_simp; ring)
        (flow_M0 hb hab h2.le (by linarith)) (flow_K1 hb hab h2.le h7)).trans ?_
      refine div_le_div_of_nonneg_right ?_ hD.le
      exact le_trans (le_of_eq (by unfold lineA; ring))
        (le_trans (le_max_left _ _) (le_max_left _ _))
    · rcases le_or_gt η 1 with hM | hM
      · refine (up_seg hb hab ((a - b) * (3 * b - a) / (2 * b) + (3 * b - a) ^ 2 / (6 * b))
          ((3 * b - a) ^ 2 / (6 * b)) _ 1 (2 * b * (3 * b - a) / (5 * b - a))
          ((a - b) * (3 * b - a) / (2 * b)) η he1l hA.le hM (by field_simp; ring) (by ring)
          (flow_K1 hb hab h2.le h7) (flow_M1f hb hab h2.le h7)).trans ?_
        refine div_le_div_of_nonneg_right ?_ hD.le
        exact le_trans (le_of_eq (by unfold lineM; ring))
          (le_trans (le_max_right _ _) (le_max_left _ _))
      · refine (value_le_of hb hab η 1 _ hM.le (flow_M1f hb hab h2.le h7)).trans ?_
        exact div_le_div_of_nonneg_right (le_max_right _ _) hD.le
  · rw [div_le_iff₀ hD]
    refine max_le (max_le ?_ ?_) ?_
    · have := low_A hb hab h2.le (by linarith) η hη; rwa [div_le_iff₀ hD] at this
    · have := low_M hb hab h2.le h7 η hη; rwa [div_le_iff₀ hD] at this
    · have := low_M1f hb hab h2.le h7 η hη; rwa [div_le_iff₀ hD] at this

theorem frontier_M2 (hb : 0 < b) (hab : b < a) (h7 : 7 * b ≤ 3 * a) (h5 : 2 * a ≤ 5 * b)
    (η : ℝ) (hη : 0 ≤ η) :
    trueValue (g6 a b) η K5 K5_ne
      = max (max (lineA a b η) (lineL2 a b η)) (2 * (a - b) * (3 * b - a) / (11 * b - 3 * a))
        / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have h17 : 17 * b - 5 * a ≠ 0 := by apply ne_of_gt; linarith
  have h11 : 11 * b - 3 * a ≠ 0 := by apply ne_of_gt; linarith
  have hq : 15 * a * b - 3 * a * a - 16 * b * b ≠ 0 := by
    apply ne_of_gt
    nlinarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (by linarith : (0:ℝ) ≤ 13 * b - 5 * a),
      mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b),
      mul_nonneg (by linarith : (0:ℝ) ≤ 13 * b - 5 * a) (by linarith : (0:ℝ) ≤ 13 * b - 5 * a),
      mul_pos hb hb]
  have h17' : b * 17 - a * 5 ≠ 0 := fun h => h17 (by linear_combination h)
  have h11' : b * 11 - a * 3 ≠ 0 := fun h => h11 (by linear_combination h)
  have hq' : b * a * 15 - b ^ 2 * 16 - a ^ 2 * 3 ≠ 0 := fun h => hq (by linear_combination h)
  have h3q : 3 * (15 * a * b - 3 * a * a - 16 * b * b) ≠ 0 := mul_ne_zero (by norm_num) hq
  have hK := kinkK2_pos hb hab (by linarith)
  have hKF := kinkK2_lt_F hb hab h7 (by linarith)
  apply le_antisymm
  · rcases le_or_gt η (2 * (5 * a * a - 25 * a * b + 32 * b * b) / ((a - b) * (17 * b - 5 * a)))
      with hA | hA
    · refine (up_seg hb hab ((4 * b - a) / 3) ((a - b) / 6) 0 _ ((4 * b - a) / 3)
        (4 * b * (3 * b - a) / (17 * b - 5 * a)) η hK hη hA (by ring) (by field_simp; ring)
        (flow_M0 hb hab (by linarith) h5) (flow_K2 hb hab h7 (by linarith))).trans ?_
      refine div_le_div_of_nonneg_right ?_ hD.le
      exact le_trans (le_of_eq (by unfold lineA; ring))
        (le_trans (le_max_left _ _) (le_max_left _ _))
    · rcases le_or_gt η (4 * (8 * b - 3 * a) / (11 * b - 3 * a)) with hL | hL
      · refine (up_seg hb hab
          (2 * a * (a - b) * (3 * b - a) / (3 * (15 * a * b - 3 * a * a - 16 * b * b)))
          ((a - b) * (3 * b - a) ^ 2 / (3 * (15 * a * b - 3 * a * a - 16 * b * b))) _ _
          (4 * b * (3 * b - a) / (17 * b - 5 * a)) (2 * (a - b) * (3 * b - a) / (11 * b - 3 * a)) η
          hKF hA.le hL
          (by rw [div_mul_div_comm, div_sub_div _ _ h3q (mul_ne_zero h3q (mul_ne_zero hab' h17)),
                div_eq_div_iff h17 (mul_ne_zero h3q (mul_ne_zero h3q (mul_ne_zero hab' h17)))]
              ring)
          (by rw [div_mul_div_comm, div_sub_div _ _ h3q (mul_ne_zero h3q h11),
                div_eq_div_iff h11 (mul_ne_zero h3q (mul_ne_zero h3q h11))]
              ring)
          (flow_K2 hb hab h7 (by linarith)) (flow_M23f hb hab h7 (by linarith))).trans ?_
        refine div_le_div_of_nonneg_right ?_ hD.le
        exact le_trans (le_of_eq (by unfold lineL2; ring))
          (le_trans (le_max_right _ _) (le_max_left _ _))
      · refine (value_le_of hb hab η _ _ hL.le (flow_M23f hb hab h7 (by linarith))).trans ?_
        exact div_le_div_of_nonneg_right (le_max_right _ _) hD.le
  · rw [div_le_iff₀ hD]
    refine max_le (max_le ?_ ?_) ?_
    · have := low_A hb hab (by linarith) h5 η hη; rwa [div_le_iff₀ hD] at this
    · have := low_L2 hb hab h7 (by linarith) η hη; rwa [div_le_iff₀ hD] at this
    · have := low_M23f hb hab h7 (by linarith) η hη; rwa [div_le_iff₀ hD] at this

theorem frontier_M3 (hb : 0 < b) (hab : b < a) (h5 : 5 * b < 2 * a) (h13 : 5 * a < 13 * b)
    (η : ℝ) (hη : 0 ≤ η) :
    trueValue (g6 a b) η K5 K5_ne
      = max (max (max (lineB a b η) (lineA a b η)) (lineL2 a b η))
          (2 * (a - b) * (3 * b - a) / (11 * b - 3 * a)) / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have h17 : 17 * b - 5 * a ≠ 0 := by apply ne_of_gt; linarith
  have h11 : 11 * b - 3 * a ≠ 0 := by apply ne_of_gt; linarith
  have h7 : 7 * b ≤ 3 * a := by linarith
  have hq : 15 * a * b - 3 * a * a - 16 * b * b ≠ 0 := by
    apply ne_of_gt
    nlinarith [mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h13.le : (0:ℝ) ≤ 13 * b - 5 * a),
      mul_nonneg (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b) (sub_nonneg.2 h7 : (0:ℝ) ≤ 3 * a - 7 * b),
      mul_nonneg (sub_nonneg.2 h13.le : (0:ℝ) ≤ 13 * b - 5 * a) (sub_nonneg.2 h13.le : (0:ℝ) ≤ 13 * b - 5 * a),
      mul_pos hb hb]
  have h17' : b * 17 - a * 5 ≠ 0 := fun h => h17 (by linear_combination h)
  have h11' : b * 11 - a * 3 ≠ 0 := fun h => h11 (by linear_combination h)
  have hq' : b * a * 15 - b ^ 2 * 16 - a ^ 2 * 3 ≠ 0 := fun h => hq (by linear_combination h)
  have h3q : 3 * (15 * a * b - 3 * a * a - 16 * b * b) ≠ 0 := mul_ne_zero (by norm_num) hq
  have h0p : 0 < 2 * (2 * a - 5 * b) / (a - b) := div_pos (by linarith) (by linarith)
  have h0K := kink0_lt_K2 hb hab h5 h13
  have hKF := kinkK2_lt_F hb hab h7 h13
  apply le_antisymm
  · rcases le_or_gt η (2 * (2 * a - 5 * b) / (a - b)) with hB | hB
    · refine (up_seg hb hab ((a - b) / 3) ((a - b) / 3) 0 _ ((a - b) / 3) (3 * b - a) η h0p hη hB
        (by ring) (by field_simp; ring)
        (flow_H0M hb hab h5.le (by linarith)) (flow_K3 hb hab h5.le h13.le)).trans ?_
      refine div_le_div_of_nonneg_right ?_ hD.le
      exact le_trans (le_of_eq (by unfold lineB; ring))
        (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
    · rcases le_or_gt η (2 * (5 * a * a - 25 * a * b + 32 * b * b) / ((a - b) * (17 * b - 5 * a)))
        with hA | hA
      · refine (up_seg hb hab ((4 * b - a) / 3) ((a - b) / 6) _ _ (3 * b - a)
          (4 * b * (3 * b - a) / (17 * b - 5 * a)) η h0K hB.le hA (by field_simp; ring)
          (by field_simp; ring)
          (flow_K3 hb hab h5.le h13.le) (flow_K2 hb hab h7 h13.le)).trans ?_
        refine div_le_div_of_nonneg_right ?_ hD.le
        exact le_trans (le_of_eq (by unfold lineA; ring))
          (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
      · rcases le_or_gt η (4 * (8 * b - 3 * a) / (11 * b - 3 * a)) with hL | hL
        · refine (up_seg hb hab
            (2 * a * (a - b) * (3 * b - a) / (3 * (15 * a * b - 3 * a * a - 16 * b * b)))
            ((a - b) * (3 * b - a) ^ 2 / (3 * (15 * a * b - 3 * a * a - 16 * b * b))) _ _
            (4 * b * (3 * b - a) / (17 * b - 5 * a)) (2 * (a - b) * (3 * b - a) / (11 * b - 3 * a))
            η hKF hA.le hL
          (by rw [div_mul_div_comm, div_sub_div _ _ h3q (mul_ne_zero h3q (mul_ne_zero hab' h17)),
                div_eq_div_iff h17 (mul_ne_zero h3q (mul_ne_zero h3q (mul_ne_zero hab' h17)))]
              ring)
          (by rw [div_mul_div_comm, div_sub_div _ _ h3q (mul_ne_zero h3q h11),
                div_eq_div_iff h11 (mul_ne_zero h3q (mul_ne_zero h3q h11))]
              ring)
            (flow_K2 hb hab h7 h13.le) (flow_M23f hb hab h7 h13.le)).trans ?_
          refine div_le_div_of_nonneg_right ?_ hD.le
          exact le_trans (le_of_eq (by unfold lineL2; ring))
            (le_trans (le_max_right _ _) (le_max_left _ _))
        · refine (value_le_of hb hab η _ _ hL.le (flow_M23f hb hab h7 h13.le)).trans ?_
          exact div_le_div_of_nonneg_right (le_max_right _ _) hD.le
  · rw [div_le_iff₀ hD]
    refine max_le (max_le (max_le ?_ ?_) ?_) ?_
    · have := low_B hb hab η hη; rwa [div_le_iff₀ hD] at this
    · have := low_A3 hb hab h5.le h13.le η hη; rwa [div_le_iff₀ hD] at this
    · have := low_L2 hb hab h7 h13.le η hη; rwa [div_le_iff₀ hD] at this
    · have := low_M23f hb hab h7 h13.le η hη; rwa [div_le_iff₀ hD] at this

theorem frontier_M4 (hb : 0 < b) (hab : b < a) (h13 : 13 * b ≤ 5 * a) (h3 : a ≤ 3 * b)
    (η : ℝ) (hη : 0 ≤ η) :
    trueValue (g6 a b) η K5 K5_ne = max (lineB a b η) (2 * b / 5) / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  have hab' : a - b ≠ 0 := sub_ne_zero.2 hab.ne'
  have hp : 0 < (5 * a - 11 * b) / (5 * (a - b)) := div_pos (by linarith) (by linarith)
  apply le_antisymm
  · rcases le_or_gt η ((5 * a - 11 * b) / (5 * (a - b))) with hB | hB
    · refine (up_seg hb hab ((a - b) / 3) ((a - b) / 3) 0 _ ((a - b) / 3) (2 * b / 5) η hp hη hB
        (by ring) (by field_simp; ring)
        (flow_H0M hb hab (by linarith) h3) (flow_M4f hb hab h13 h3)).trans ?_
      refine div_le_div_of_nonneg_right ?_ hD.le
      exact le_trans (le_of_eq (by unfold lineB; ring)) (le_max_left _ _)
    · refine (value_le_of hb hab η _ _ hB.le (flow_M4f hb hab h13 h3)).trans ?_
      exact div_le_div_of_nonneg_right (le_max_right _ _) hD.le
  · rw [div_le_iff₀ hD]
    refine max_le ?_ ?_
    · have := low_B hb hab η hη; rwa [div_le_iff₀ hD] at this
    · have := low_M4f hb hab h13 h3 η hη; rwa [div_le_iff₀ hD] at this

theorem frontier_H (hb : 0 < b) (hab : b < a) (h3 : 3 * b ≤ a) (η : ℝ) (hη : 0 ≤ η) :
    trueValue (g6 a b) η K5 K5_ne = max (lineB a b η) ((a - b) / 5) / (2 * a + 4 * b) := by
  have hD : 0 < 2 * a + 4 * b := by linarith
  apply le_antisymm
  · rcases le_or_gt η (2 / 5) with hB | hB
    · refine (up_seg hb hab ((a - b) / 3) ((a - b) / 3) 0 (2 / 5) ((a - b) / 3) ((a - b) / 5) η
        (by norm_num) hη hB (by ring) (by ring)
        (flow_H0H hb hab h3) (flow_Hf hb hab h3)).trans ?_
      refine div_le_div_of_nonneg_right ?_ hD.le
      exact le_trans (le_of_eq (by unfold lineB; ring)) (le_max_left _ _)
    · refine (value_le_of hb hab η _ _ hB.le (flow_Hf hb hab h3)).trans ?_
      exact div_le_div_of_nonneg_right (le_max_right _ _) hD.le
  · rw [div_le_iff₀ hD]
    refine max_le ?_ ?_
    · have := low_B hb hab η hη; rwa [div_le_iff₀ hD] at this
    · have := low_Hf hb hab h3 η hη; rwa [div_le_iff₀ hD] at this

/-- The six regions cover every ratio `a/b > 1`, and each is nonempty. -/
theorem regions_cover (hb : 0 < b) (hab : b < a) :
    a ≤ 2 * b ∨ (2 * b < a ∧ 3 * a ≤ 7 * b) ∨ (7 * b ≤ 3 * a ∧ 2 * a ≤ 5 * b)
      ∨ (5 * b < 2 * a ∧ 5 * a < 13 * b) ∨ (13 * b ≤ 5 * a ∧ a ≤ 3 * b) ∨ 3 * b ≤ a := by
  by_cases h1 : a ≤ 2 * b; · exact Or.inl h1
  by_cases h2 : 3 * a ≤ 7 * b; · exact Or.inr (Or.inl ⟨by linarith, h2⟩)
  by_cases h3 : 2 * a ≤ 5 * b; · exact Or.inr (Or.inr (Or.inl ⟨by linarith, h3⟩))
  by_cases h4 : 5 * a < 13 * b; · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, h4⟩)))
  by_cases h5 : a ≤ 3 * b
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, h5⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))

theorem regions_nonempty :
    ((1 : ℝ) < 3 / 2 ∧ (3 / 2 : ℝ) ≤ 2 * 1) ∧ (2 * 1 < (11 / 5 : ℝ) ∧ 3 * (11 / 5 : ℝ) ≤ 7 * 1)
      ∧ (7 * 1 ≤ 3 * (12 / 5 : ℝ) ∧ 2 * (12 / 5 : ℝ) ≤ 5 * 1)
      ∧ (5 * 1 < 2 * (51 / 20 : ℝ) ∧ 5 * (51 / 20 : ℝ) < 13 * 1)
      ∧ (13 * 1 ≤ 5 * (14 / 5 : ℝ) ∧ (14 / 5 : ℝ) ≤ 3 * 1) ∧ 3 * 1 ≤ (4 : ℝ) := by
  norm_num

#print axioms up_seg
#print axioms kinkK2_lt_F
#print axioms kink0_lt_K2
#print axioms frontier_L
#print axioms frontier_M1
#print axioms frontier_M2
#print axioms frontier_M3
#print axioms frontier_M4
#print axioms frontier_H
#print axioms regions_cover

end CIGAMF.P13.PaperCTwoMag1122
