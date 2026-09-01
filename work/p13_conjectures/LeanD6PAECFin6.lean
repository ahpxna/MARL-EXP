import Mathlib
import «LeanD6PAECCanonical»
import «LeanD6CycleDual»

/-! # The canonical binary `m=6` five-cycle PAEC branch. -/

namespace CIGAMF.P13.D6PAECFin6

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry

def a6 (a b c d e f : Fin 2) : Fin 6 → Fin 2 := ![a,b,c,d,e,f]
def z6 := a6 0 0 0 0 0 0
def o6 := a6 1 1 1 1 1 1
def s6 := a6 1 1 1 0 0 0
def t6 := a6 0 0 0 1 1 1
def e60 := a6 1 0 0 0 0 0
def e61 := a6 0 1 0 0 0 0
def e62 := a6 0 0 1 0 0 0
def e63 := a6 0 0 0 1 0 0
def e64 := a6 0 0 0 0 1 0
def e65 := a6 0 0 0 0 0 1
def p62 := a6 1 1 0 0 0 0
def b60 := a6 1 0 0 1 1 1
def b61 := a6 1 1 0 1 1 1

def selected6 : Finset (Fin 6) := {0, 1, 2}
def rejected6 : Finset (Fin 6) := {3, 4, 5}

def pointMass6 (_i : Fin 6) (u : Fin 2) : ℝ :=
  if u = 0 then 1 else 0

private theorem fin2_zero_or_one (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

theorem pointMass6_jointWeight (c : Fin 6 → Fin 2) :
    jointWeight pointMass6 c = if c = z6 then 1 else 0 := by
  classical
  by_cases h : c = z6
  · subst c
    simp [jointWeight, pointMass6, z6, a6, Fin.prod_univ_six]
  · have hc : c 0 ≠ z6 0 ∨ c 1 ≠ z6 1 ∨ c 2 ≠ z6 2 ∨
        c 3 ≠ z6 3 ∨ c 4 ≠ z6 4 ∨ c 5 ≠ z6 5 := by
      by_contra hn
      push_neg at hn
      apply h
      funext i
      fin_cases i <;>
        simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1,
          hn.2.2.2.2.1, hn.2.2.2.2.2]
    rcases hc with hc | hc | hc | hc | hc | hc
    · have hc' : c 0 ≠ 0 := by simpa [z6, a6] using hc
      simp [jointWeight, pointMass6, Fin.prod_univ_six, hc', h]
    · have hc' : c 1 ≠ 0 := by simpa [z6, a6] using hc
      simp [jointWeight, pointMass6, Fin.prod_univ_six, hc', h]
    · have hc' : c 2 ≠ 0 := by simpa [z6, a6] using hc
      simp [jointWeight, pointMass6, Fin.prod_univ_six, hc', h]
    · have hc' : c 3 ≠ 0 := by simpa [z6, a6] using hc
      simp [jointWeight, pointMass6, Fin.prod_univ_six, hc', h]
    · have hc' : c 4 ≠ 0 := by simpa [z6, a6] using hc
      simp [jointWeight, pointMass6, Fin.prod_univ_six, hc', h]
    · have hc' : c 5 ≠ 0 := by simpa [z6, a6] using hc
      simp [jointWeight, pointMass6, Fin.prod_univ_six, hc', h]

theorem pointMass6_expectation (G : (Fin 6 → Fin 2) → ℝ) :
    productExpectation pointMass6 G = G z6 := by
  classical
  unfold productExpectation
  simp_rw [pointMass6_jointWeight]
  rw [Finset.sum_eq_single z6]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

theorem pointMass6_response (F : (Fin 6 → Fin 2) → ℝ)
    (i : Fin 6) (u : Fin 2) :
    productResponse pointMass6 F i u = F (Function.update z6 i u) := by
  unfold productResponse
  rw [pointMass6_expectation]

@[simp] theorem pointMass6_response_zero
    (F : (Fin 6 → Fin 2) → ℝ) (i : Fin 6) :
    productResponse pointMass6 F i 0 = F z6 := by
  rw [pointMass6_response]
  congr 1
  funext j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem pointMass6_response_one
    (F : (Fin 6 → Fin 2) → ℝ) (i : Fin 6) :
    productResponse pointMass6 F i 1 =
      ![F e60, F e61, F e62, F e63, F e64, F e65] i := by
  rw [pointMass6_response]
  fin_cases i <;> congr 1 <;> funext j <;> fin_cases j <;> rfl

noncomputable def rS6 (F : (Fin 6 → Fin 2) → ℝ)
    (x : Fin 6 → Fin 2) : ℝ :=
  F x - (if x 0 = 0 then F z6 else F e60) -
    (if x 1 = 0 then F z6 else F e61) -
    (if x 2 = 0 then F z6 else F e62)

noncomputable def rT6 (F : (Fin 6 → Fin 2) → ℝ)
    (x : Fin 6 → Fin 2) : ℝ :=
  F x - (if x 3 = 0 then F z6 else F e63) -
    (if x 4 = 0 then F z6 else F e64) -
    (if x 5 = 0 then F z6 else F e65)

theorem rS6_eq_retained (F : (Fin 6 → Fin 2) → ℝ) :
    rS6 F = fun x ↦ F x - selected6.sum
      (fun j ↦ productResponse pointMass6 F j (x j)) := by
  funext x
  rw [show selected6.sum
      (fun j ↦ productResponse pointMass6 F j (x j)) =
        productResponse pointMass6 F 0 (x 0) +
        productResponse pointMass6 F 1 (x 1) +
        productResponse pointMass6 F 2 (x 2) by
          simp [selected6]; ring]
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    simp [rS6, h0, h1, h2] <;> ring

theorem rT6_eq_retained (F : (Fin 6 → Fin 2) → ℝ) :
    rT6 F = fun x ↦ F x - rejected6.sum
      (fun j ↦ productResponse pointMass6 F j (x j)) := by
  funext x
  rw [show rejected6.sum
      (fun j ↦ productResponse pointMass6 F j (x j)) =
        productResponse pointMass6 F 3 (x 3) +
        productResponse pointMass6 F 4 (x 4) +
        productResponse pointMass6 F 5 (x 5) by
          simp [rejected6]; ring]
  rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    rcases fin2_zero_or_one (x 4) with h4 | h4 <;>
    rcases fin2_zero_or_one (x 5) with h5 | h5 <;>
    simp [rT6, h3, h4, h5] <;> ring

noncomputable def topCorrection6 (F : (Fin 6 → Fin 2) → ℝ) : ℝ :=
  ((F z6 - F e65) - (F z6 - F e60)) +
  ((F z6 - F e64) - (F z6 - F e61)) +
  ((F z6 - F e63) - (F z6 - F e62))

noncomputable def cycleSum6 (F : (Fin 6 → Fin 2) → ℝ) : ℝ :=
  mixedDifference F 1 p62 z6 + mixedDifference F 2 s6 z6 +
  mixedDifference F 0 b60 z6 + mixedDifference F 1 b61 z6 +
  mixedDifference F 2 o6 z6

theorem five_cycle_identity (F : (Fin 6 → Fin 2) → ℝ) :
    rS6 F s6 - rS6 F t6 - (rT6 F z6 - rT6 F o6) =
      cycleSum6 F + topCorrection6 F := by

  -- Anchor / endpoint coordinate values used by mixedDifference.
  have hz6v0 : z6 (0 : Fin 6) = (0 : Fin 2) := by rfl
  have hz6v1 : z6 (1 : Fin 6) = (0 : Fin 2) := by rfl
  have hz6v2 : z6 (2 : Fin 6) = (0 : Fin 2) := by rfl

  have hp62v1 : p62 (1 : Fin 6) = (1 : Fin 2) := by rfl
  have hs6v2  : s6  (2 : Fin 6) = (1 : Fin 2) := by rfl
  have hb60v0 : b60 (0 : Fin 6) = (1 : Fin 2) := by rfl
  have hb61v1 : b61 (1 : Fin 6) = (1 : Fin 2) := by rfl
  have ho6v2  : o6  (2 : Fin 6) = (1 : Fin 2) := by rfl

  -- Concrete updates for the five PAEC cycle atoms.
  have hp62_1 :
      Function.update p62 (1 : Fin 6) (0 : Fin 2) = e60 := by
    funext i
    fin_cases i <;> rfl

  have hz6_1 :
      Function.update z6 (1 : Fin 6) (1 : Fin 2) = e61 := by
    funext i
    fin_cases i <;> rfl

  have hs6_2 :
      Function.update s6 (2 : Fin 6) (0 : Fin 2) = p62 := by
    funext i
    fin_cases i <;> rfl

  have hz6_2 :
      Function.update z6 (2 : Fin 6) (1 : Fin 2) = e62 := by
    funext i
    fin_cases i <;> rfl

  have hb60_0 :
      Function.update b60 (0 : Fin 6) (0 : Fin 2) = t6 := by
    funext i
    fin_cases i <;> rfl

  have hz6_0 :
      Function.update z6 (0 : Fin 6) (1 : Fin 2) = e60 := by
    funext i
    fin_cases i <;> rfl

  have hb61_1 :
      Function.update b61 (1 : Fin 6) (0 : Fin 2) = b60 := by
    funext i
    fin_cases i <;> rfl

  have ho6_2 :
      Function.update o6 (2 : Fin 6) (0 : Fin 2) = b61 := by
    funext i
    fin_cases i <;> rfl

  -- Expose the five mixed differences, but keep action aliases intact.
  unfold cycleSum6
  unfold mixedDifference

  -- First normalize the values supplied to Function.update.
  rw [hz6v0, hz6v1, hz6v2,
      hp62v1, hs6v2, hb60v0, hb61v1, ho6v2]

  -- Then normalize the actual updated actions.
  rw [hp62_1, hz6_1,
      hs6_2, hz6_2,
      hb60_0, hz6_0,
      hb61_1,
      ho6_2]

  simp [rS6, rT6, topCorrection6,
    s6, t6, z6, o6,
    e60, e61, e62, e63, e64, e65,
    p62, b60, b61, a6] <;> ring

theorem topCorrection6_nonpos
    (F : (Fin 6 → Fin 2) → ℝ)
    (h05 : F z6 - F e65 ≤ F z6 - F e60)
    (h14 : F z6 - F e64 ≤ F z6 - F e61)
    (h23 : F z6 - F e63 ≤ F z6 - F e62) :
    topCorrection6 F ≤ 0 := by
  unfold topCorrection6
  linarith

theorem cycleSum6_le
    (F : (Fin 6 → Fin 2) → ℝ) (delta : ℝ)
    (hdelta : ∀ i x c, |mixedDifference F i x c| ≤ delta) :
    cycleSum6 F ≤ 5 * delta := by
  have h0 := hdelta 1 p62 z6
  have h1 := hdelta 2 s6 z6
  have h2 := hdelta 0 b60 z6
  have h3 := hdelta 1 b61 z6
  have h4 := hdelta 2 o6 z6
  unfold cycleSum6
  have h0' := le_trans (le_abs_self _) h0
  have h1' := le_trans (le_abs_self _) h1
  have h2' := le_trans (le_abs_self _) h2
  have h3' := le_trans (le_abs_self _) h3
  have h4' := le_trans (le_abs_self _) h4
  linarith

private theorem point_sub_point_le_osc
    {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (a b : A) : f a - f b ≤ osc f := by
  have ha := le_maxVal f a
  have hb := minVal_le f b
  simp only [osc]
  linarith

theorem balanced_direct_fin6_from_five_cycles
    (F : (Fin 6 → Fin 2) → ℝ) (delta : ℝ)
    (hdelta : ∀ i x c, |mixedDifference F i x c| ≤ delta)
    (h05 : F z6 - F e65 ≤ F z6 - F e60)
    (h14 : F z6 - F e64 ≤ F z6 - F e61)
    (h23 : F z6 - F e63 ≤ F z6 - F e62)
    (hActive : osc (rS6 F) = rS6 F s6 - rS6 F t6) :
    osc (rS6 F) / 2 - osc (rT6 F) / 2 ≤ 5 * delta / 2 := by
  have hId := five_cycle_identity F
  have hCycle := cycleSum6_le F delta hdelta
  have hTop := topCorrection6_nonpos F h05 h14 h23
  have hT := point_sub_point_le_osc (rT6 F) z6 o6
  rw [hActive]
  linarith

theorem productCompressionLoss_fin6_from_five_cycles
    (F : (Fin 6 → Fin 2) → ℝ) (delta : ℝ)
    (hdelta : ∀ i x c, |mixedDifference F i x c| ≤ delta)
    (h05 : F z6 - F e65 ≤ F z6 - F e60)
    (h14 : F z6 - F e64 ≤ F z6 - F e61)
    (h23 : F z6 - F e63 ≤ F z6 - F e62)
    (hActive : osc (rS6 F) = rS6 F s6 - rS6 F t6) :
    productCompressionLoss F (productResponse pointMass6 F) selected6 -
        productCompressionLoss F (productResponse pointMass6 F) rejected6 ≤
      5 * delta / 2 := by
  have h := balanced_direct_fin6_from_five_cycles F delta hdelta
    h05 h14 h23 hActive
  change
    osc (fun x ↦ F x - selected6.sum
      (fun j ↦ productResponse pointMass6 F j (x j))) / 2 -
      osc (fun x ↦ F x - rejected6.sum
      (fun j ↦ productResponse pointMass6 F j (x j))) / 2 ≤ _
  rw [← rS6_eq_retained F, ← rT6_eq_retained F]
  exact h

end CIGAMF.P13.D6PAECFin6
