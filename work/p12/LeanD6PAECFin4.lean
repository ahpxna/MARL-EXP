import Mathlib
import «LeanD6PAECCanonical»
import «LeanD6CycleDual»

/-!
# The canonical binary `m=4` three-cycle PAEC branch

This is a symbolic certificate over an arbitrary world `F`, not a numerical
witness.  It covers the canonical branch reconstructed from the sparse LP
dual: all point-mass response contrasts are nonpositive, the selected
residual has active endpoints `0011` and `1100`, and the rejected residual is
lower-bounded by endpoints `0000` and `1111`.
-/

namespace CIGAMF.P13.D6PAECFin4

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6CycleDual

def a4 (a b c d : Fin 2) : Fin 4 → Fin 2 := ![a,b,c,d]
def z4 := a4 0 0 0 0
def o4 := a4 1 1 1 1
def s4 := a4 1 1 0 0
def t4 := a4 0 0 1 1
def e40 := a4 1 0 0 0
def e41 := a4 0 1 0 0
def e42 := a4 0 0 1 0
def e43 := a4 0 0 0 1
def x4b := a4 1 0 1 1

def selected4 : Finset (Fin 4) := {0, 1}
def rejected4 : Finset (Fin 4) := {2, 3}

def pointMass4 (_i : Fin 4) (u : Fin 2) : ℝ :=
  if u = 0 then 1 else 0

private theorem fin2_zero_or_one (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

theorem pointMass4_jointWeight (c : Fin 4 → Fin 2) :
    jointWeight pointMass4 c = if c = z4 then 1 else 0 := by
  classical
  by_cases h : c = z4
  · subst c
    simp [jointWeight, pointMass4, z4, a4, Fin.prod_univ_four]
  · have hc : c 0 ≠ z4 0 ∨ c 1 ≠ z4 1 ∨
        c 2 ≠ z4 2 ∨ c 3 ≠ z4 3 := by
      by_contra hn
      push_neg at hn
      apply h
      funext i
      fin_cases i <;> simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]
    rcases hc with hc | hc | hc | hc
    · have hc' : c 0 ≠ 0 := by simpa [z4, a4] using hc
      simp [jointWeight, pointMass4, Fin.prod_univ_four, hc', h]
    · have hc' : c 1 ≠ 0 := by simpa [z4, a4] using hc
      simp [jointWeight, pointMass4, Fin.prod_univ_four, hc', h]
    · have hc' : c 2 ≠ 0 := by simpa [z4, a4] using hc
      simp [jointWeight, pointMass4, Fin.prod_univ_four, hc', h]
    · have hc' : c 3 ≠ 0 := by simpa [z4, a4] using hc
      simp [jointWeight, pointMass4, Fin.prod_univ_four, hc', h]

theorem pointMass4_expectation (G : (Fin 4 → Fin 2) → ℝ) :
    productExpectation pointMass4 G = G z4 := by
  classical
  unfold productExpectation
  simp_rw [pointMass4_jointWeight]
  rw [Finset.sum_eq_single z4]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

theorem pointMass4_response (F : (Fin 4 → Fin 2) → ℝ)
    (i : Fin 4) (u : Fin 2) :
    productResponse pointMass4 F i u = F (Function.update z4 i u) := by
  unfold productResponse
  rw [pointMass4_expectation]

@[simp] theorem pointMass4_response_zero
    (F : (Fin 4 → Fin 2) → ℝ) (i : Fin 4) :
    productResponse pointMass4 F i 0 = F z4 := by
  rw [pointMass4_response]
  congr 1
  funext j
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem pointMass4_response_one
    (F : (Fin 4 → Fin 2) → ℝ) (i : Fin 4) :
    productResponse pointMass4 F i 1 = ![F e40, F e41, F e42, F e43] i := by
  rw [pointMass4_response]
  fin_cases i <;> congr 1 <;> funext j <;> fin_cases j <;> rfl

noncomputable def rS4 (F : (Fin 4 → Fin 2) → ℝ)
    (x : Fin 4 → Fin 2) : ℝ :=
  F x - (if x 0 = 0 then F z4 else F e40) -
    (if x 1 = 0 then F z4 else F e41)

noncomputable def rT4 (F : (Fin 4 → Fin 2) → ℝ)
    (x : Fin 4 → Fin 2) : ℝ :=
  F x - (if x 2 = 0 then F z4 else F e42) -
    (if x 3 = 0 then F z4 else F e43)

theorem rS4_eq_retained (F : (Fin 4 → Fin 2) → ℝ) :
    rS4 F = fun x ↦ F x - selected4.sum
      (fun j ↦ productResponse pointMass4 F j (x j)) := by
  funext x
  rw [show selected4.sum
      (fun j ↦ productResponse pointMass4 F j (x j)) =
        productResponse pointMass4 F 0 (x 0) +
          productResponse pointMass4 F 1 (x 1) by
    simp [selected4]]
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    simp [rS4, h0, h1] <;> ring

theorem rT4_eq_retained (F : (Fin 4 → Fin 2) → ℝ) :
    rT4 F = fun x ↦ F x - rejected4.sum
      (fun j ↦ productResponse pointMass4 F j (x j)) := by
  funext x
  rw [show rejected4.sum
      (fun j ↦ productResponse pointMass4 F j (x j)) =
        productResponse pointMass4 F 2 (x 2) +
          productResponse pointMass4 F 3 (x 3) by
    simp [rejected4]]
  rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [rT4, h2, h3] <;> ring

noncomputable def topCorrection4 (F : (Fin 4 → Fin 2) → ℝ) : ℝ :=
  ((F z4 - F e43) - (F z4 - F e40)) +
    ((F z4 - F e42) - (F z4 - F e41))

noncomputable def cycleSum4 (F : (Fin 4 → Fin 2) → ℝ) : ℝ :=
  mixedDifference F 1 s4 z4 +
    mixedDifference F 0 x4b z4 +
    mixedDifference F 1 o4 z4

theorem three_cycle_identity (F : (Fin 4 → Fin 2) → ℝ) :
    rS4 F s4 - rS4 F t4 - (rT4 F z4 - rT4 F o4) =
      cycleSum4 F + topCorrection4 F := by
  have hz4v1 : z4 (1 : Fin 4) = (0 : Fin 2) := by rfl
  have hs4v1 : s4 (1 : Fin 4) = (1 : Fin 2) := by rfl
  have hz4v0 : z4 (0 : Fin 4) = (0 : Fin 2) := by rfl
  have hx4bv0 : x4b (0 : Fin 4) = (1 : Fin 2) := by rfl
  have ho4v1 : o4 (1 : Fin 4) = (1 : Fin 2) := by rfl

  have hs4_1 :
      Function.update s4 (1 : Fin 4) (0 : Fin 2) = e40 := by
    funext i
    fin_cases i <;> rfl
  have hz4_1 :
      Function.update z4 (1 : Fin 4) (1 : Fin 2) = e41 := by
    funext i
    fin_cases i <;> rfl
  have hx4b_0 :
      Function.update x4b (0 : Fin 4) (0 : Fin 2) = t4 := by
    funext i
    fin_cases i <;> rfl
  have hz4_0 :
      Function.update z4 (0 : Fin 4) (1 : Fin 2) = e40 := by
    funext i
    fin_cases i <;> rfl
  have ho4_1 :
      Function.update o4 (1 : Fin 4) (0 : Fin 2) = x4b := by
    funext i
    fin_cases i <;> rfl

  unfold cycleSum4
  unfold mixedDifference

  -- First turn anchor lookups into literal 0/1.
  rw [hz4v1, hs4v1, hz4v0, hx4bv0, ho4v1]

  -- Now the concrete Function.update identities match.
  rw [hs4_1, hz4_1, hx4b_0, hz4_0, ho4_1]

  simp [rS4, rT4, topCorrection4,
    s4, t4, z4, o4, e40, e41, e42, e43, x4b, a4] <;> ring

theorem topCorrection4_nonpos
    (F : (Fin 4 → Fin 2) → ℝ)
    (h03 : F z4 - F e43 ≤ F z4 - F e40)
    (h12 : F z4 - F e42 ≤ F z4 - F e41) :
    topCorrection4 F ≤ 0 := by
  unfold topCorrection4
  linarith

theorem cycleSum4_le
    (F : (Fin 4 → Fin 2) → ℝ) (delta : ℝ)
    (hdelta : ∀ i x c, |mixedDifference F i x c| ≤ delta) :
    cycleSum4 F ≤ 3 * delta := by
  have h1 := hdelta 1 s4 z4
  have h2 := hdelta 0 x4b z4
  have h3 := hdelta 1 o4 z4
  unfold cycleSum4
  have h1' := le_trans (le_abs_self (mixedDifference F 1 s4 z4)) h1
  have h2' := le_trans (le_abs_self (mixedDifference F 0 x4b z4)) h2
  have h3' := le_trans (le_abs_self (mixedDifference F 1 o4 z4)) h3
  linarith

private theorem point_sub_point_le_osc
    {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (a b : A) : f a - f b ≤ osc f := by
  have ha := le_maxVal f a
  have hb := minVal_le f b
  simp only [osc]
  linarith

theorem balanced_direct_fin4_from_three_cycles
    (F : (Fin 4 → Fin 2) → ℝ) (delta : ℝ)
    (hdelta : ∀ i x c, |mixedDifference F i x c| ≤ delta)
    (h03 : F z4 - F e43 ≤ F z4 - F e40)
    (h12 : F z4 - F e42 ≤ F z4 - F e41)
    (hActive : osc (rS4 F) = rS4 F s4 - rS4 F t4) :
    osc (rS4 F) / 2 - osc (rT4 F) / 2 ≤ 3 * delta / 2 := by
  have hId := three_cycle_identity F
  have hCycle := cycleSum4_le F delta hdelta
  have hTop := topCorrection4_nonpos F h03 h12
  have hT := point_sub_point_le_osc (rT4 F) z4 o4
  rw [hActive]
  linarith

/- Scientific-object connector for the canonical branch: the symbolic
residual oscillations above are exactly the D6 product-compression losses for
the all-zero product reference. -/
theorem productCompressionLoss_fin4_from_three_cycles
    (F : (Fin 4 → Fin 2) → ℝ) (delta : ℝ)
    (hdelta : ∀ i x c, |mixedDifference F i x c| ≤ delta)
    (h03 : F z4 - F e43 ≤ F z4 - F e40)
    (h12 : F z4 - F e42 ≤ F z4 - F e41)
    (hActive : osc (rS4 F) = rS4 F s4 - rS4 F t4) :
    productCompressionLoss F (productResponse pointMass4 F) selected4 -
        productCompressionLoss F (productResponse pointMass4 F) rejected4 ≤
      3 * delta / 2 := by
  have h := balanced_direct_fin4_from_three_cycles F delta hdelta h03 h12 hActive
  change
    osc (fun x ↦ F x - selected4.sum
      (fun j ↦ productResponse pointMass4 F j (x j))) / 2 -
      osc (fun x ↦ F x - rejected4.sum
      (fun j ↦ productResponse pointMass4 F j (x j))) / 2 ≤ _
  rw [← rS4_eq_retained F, ← rT4_eq_retained F]
  exact h

end CIGAMF.P13.D6PAECFin4
