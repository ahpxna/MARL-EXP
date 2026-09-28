import «LeanD6M6SharpnessBridgeV1»
import «LeanSupportFibreSufficiencyV1»
import «LeanFunctionalResidualMaintenanceV2»
import «LeanStructuralStaircaseExactPrefixCoverV1»

namespace CIGAMF.P13.D6MarginSensitiveExchange

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6H3Exchange

variable {U : Type*} [Fintype U] [Nonempty U]

private theorem point_sub_point_le_osc
    {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (a b : A) : f a - f b ≤ osc f := by
  have ha := le_maxVal f a
  have hb := minVal_le f b
  simp only [osc]
  linarith

private theorem retainedResidual_sdiff_identity {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (S T : Finset (Fin (n + 1))) (z : Fin (n + 1) → U) :
    retainedResidual q F T z = retainedResidual q F S z +
        (S \ T).sum (fun j ↦ productResponse q F j (z j)) -
        (T \ S).sum (fun j ↦ productResponse q F j (z j)) := by
  classical
  unfold retainedResidual
  have hcancel :
      S.sum (fun j ↦ productResponse q F j (z j)) -
          T.sum (fun j ↦ productResponse q F j (z j)) =
        (S \ T).sum (fun j ↦ productResponse q F j (z j)) -
          (T \ S).sum (fun j ↦ productResponse q F j (z j)) := by
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
  rw [show F z - T.sum (fun j ↦ productResponse q F j (z j)) =
      (F z - S.sum (fun j ↦ productResponse q F j (z j))) +
        (S.sum (fun j ↦ productResponse q F j (z j)) -
          T.sum (fun j ↦ productResponse q F j (z j))) by ring,
    hcancel]
  ring

private theorem directed_response_sum_le_spans {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (A : Finset (Fin (n + 1))) (x y : Fin (n + 1) → U) :
    A.sum (fun j ↦ productResponse q F j (x j)) -
        A.sum (fun j ↦ productResponse q F j (y j)) ≤
      A.sum (fun j ↦ osc (productResponse q F j)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  exact point_sub_point_le_osc (productResponse q F j) (x j) (y j)

private theorem patched_extrema_sum {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (A : Finset (Fin (n + 1)))
    (x y p m : Fin (n + 1) → U)
    (hp : ∀ j, productResponse q F j (p j) =
      maxVal (productResponse q F j))
    (hm : ∀ j, productResponse q F j (m j) =
      minVal (productResponse q F j)) :
    A.sum (fun j ↦ productResponse q F j
        (patchCoordinates x p A j)) -
      A.sum (fun j ↦ productResponse q F j
        (patchCoordinates y m A j)) =
      A.sum (fun j ↦ osc (productResponse q F j)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [patchCoordinates, if_pos hj, hp, hm, osc]

/-- Preserve the score surplus discarded by the earlier endpoint-patch bound. -/
theorem pair_loss_le_sdiff_card_sub_score_surplus {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected competitor : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore
      (fun j ↦ osc (productResponse q F j)) selected k)
    (hCompetitorCard : competitor.card = k) :
    productCompressionLoss F (productResponse q F) selected -
        productCompressionLoss F (productResponse q F) competitor ≤
      ((selected \ competitor).card : ℝ) * delta -
        ((selected \ competitor).sum (fun j ↦ osc (productResponse q F j)) -
         (competitor \ selected).sum (fun j ↦ osc (productResponse q F j))) / 2 := by
  classical
  let RS := retainedResidual q F selected
  let RT := retainedResidual q F competitor
  let A := selected \ competitor
  let B := competitor \ selected
  rcases exists_eq_maxVal RS with ⟨xplus, hxplus⟩
  rcases exists_eq_minVal RS with ⟨xminus, hxminus⟩
  let p : Fin (n + 1) → U := fun j ↦
    Classical.choose (exists_eq_maxVal (productResponse q F j))
  let m : Fin (n + 1) → U := fun j ↦
    Classical.choose (exists_eq_minVal (productResponse q F j))
  have hp : ∀ j, productResponse q F j (p j) =
      maxVal (productResponse q F j) := by
    intro j
    exact Classical.choose_spec (exists_eq_maxVal (productResponse q F j))
  have hm : ∀ j, productResponse q F j (m j) =
      minVal (productResponse q F j) := by
    intro j
    exact Classical.choose_spec (exists_eq_minVal (productResponse q F j))
  let u := patchCoordinates xplus p A
  let v := patchCoordinates xminus m A
  have hAsub : A ⊆ selected := by
    intro j hj
    exact (Finset.mem_sdiff.mp hj).1
  have hplusAbs := retainedResidual_patch_bound q F delta hWeight hNorm
    hDeltaNonneg hdelta selected A hAsub xplus p
  have hminusAbs := retainedResidual_patch_bound q F delta hWeight hNorm
    hDeltaNonneg hdelta selected A hAsub xminus m
  have hplus : RS xplus - RS u ≤ (A.card : ℝ) * delta := by
    have hle : RS xplus - RS u ≤ |RS xplus - RS u| := le_abs_self _
    have habs : |RS xplus - RS u| ≤ (A.card : ℝ) * delta := by
      simpa [RS, u, abs_sub_comm] using hplusAbs
    exact le_trans hle habs
  have hminus : RS v - RS xminus ≤ (A.card : ℝ) * delta := by
    have hle : RS v - RS xminus ≤ |RS v - RS xminus| := le_abs_self _
    have habs : |RS v - RS xminus| ≤ (A.card : ℝ) * delta := by
      simpa [RS, v] using hminusAbs
    exact le_trans hle habs
  have hoscT : RT u - RT v ≤ osc RT :=
    point_sub_point_le_osc RT u v
  have hRTu : RT u = RS u +
      A.sum (fun j ↦ productResponse q F j (u j)) -
      B.sum (fun j ↦ productResponse q F j (u j)) := by
    simpa [RS, RT, A, B] using
      retainedResidual_sdiff_identity q F selected competitor u
  have hRTv : RT v = RS v +
      A.sum (fun j ↦ productResponse q F j (v j)) -
      B.sum (fun j ↦ productResponse q F j (v j)) := by
    simpa [RS, RT, A, B] using
      retainedResidual_sdiff_identity q F selected competitor v
  have hAdiff :
      A.sum (fun j ↦ productResponse q F j (u j)) -
        A.sum (fun j ↦ productResponse q F j (v j)) =
      A.sum (fun j ↦ osc (productResponse q F j)) := by
    simpa [u, v] using patched_extrema_sum q F A xplus xminus p m hp hm
  have hBdiff :
      B.sum (fun j ↦ productResponse q F j (u j)) -
        B.sum (fun j ↦ productResponse q F j (v j)) ≤
      B.sum (fun j ↦ osc (productResponse q F j)) :=
    directed_response_sum_le_spans q F B u v
  have hTopTotal := hTop.2 competitor hCompetitorCard
  have hTopAB :
      B.sum (fun j ↦ osc (productResponse q F j)) ≤
        A.sum (fun j ↦ osc (productResponse q F j)) := by
    have hcancel :
        selected.sum (fun j ↦ osc (productResponse q F j)) -
            competitor.sum (fun j ↦ osc (productResponse q F j)) =
          A.sum (fun j ↦ osc (productResponse q F j)) -
            B.sum (fun j ↦ osc (productResponse q F j)) := by
      dsimp [A, B]
      rw [← Finset.sum_sdiff_sub_sum_sdiff]
    linarith
  have hoscS : osc RS = RS xplus - RS xminus := by
    simp only [osc, ← hxplus, ← hxminus]
  have hRaw : osc RS - osc RT ≤
      2 * (A.card : ℝ) * delta -
        (A.sum (fun j ↦ osc (productResponse q F j)) -
         B.sum (fun j ↦ osc (productResponse q F j))) := by
    rw [hoscS]
    linarith
  change osc RS / 2 - osc RT / 2 ≤ (A.card : ℝ) * delta -
    (A.sum (fun j ↦ osc (productResponse q F j)) -
     B.sum (fun j ↦ osc (productResponse q F j))) / 2
  linarith



/-- Sum a common separation margin across equal-size exchanged sets. -/
theorem score_surplus_ge_card_mul_margin {I : Type*} [DecidableEq I]
    (A B : Finset I) (score : I → ℝ) (mu : ℝ) (hCard : A.card = B.card)
    (hMargin : ∀ i ∈ A, ∀ j ∈ B, mu + score j ≤ score i) :
    (A.card : ℝ) * mu ≤ A.sum score - B.sum score := by
  classical
  by_cases hB : B.Nonempty
  · obtain ⟨b, hb, hmax⟩ := B.exists_max_image score hB
    have ha : (A.card : ℝ) * (mu + score b) ≤ A.sum score := by
      calc _ = A.sum (fun _ => mu + score b) := by simp [mul_add]
           _ ≤ _ := Finset.sum_le_sum (fun i hi => hMargin i hi b hb)
    have hbSum : B.sum score ≤ (A.card : ℝ) * score b := by
      calc _ ≤ B.sum (fun _ => score b) := Finset.sum_le_sum (fun j hj => hmax j hj)
           _ = _ := by simp [hCard]
    nlinarith
  · have hBe : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    have hAe : A = ∅ := Finset.card_eq_zero.mp (by simpa [hBe] using hCard)
    simp [hAe, hBe]

/-- Universal margin-sensitive exchange bound; no symmetry or fixed cell assumed. -/
theorem pair_doubled_loss_le_card_mul_two_delta_sub_margin {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta mu : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected competitor : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore
      (fun j ↦ osc (productResponse q F j)) selected k)
    (hCompetitorCard : competitor.card = k)
    (hMargin : ∀ i ∈ selected, ∀ j ∉ selected,
      mu + osc (productResponse q F j) ≤ osc (productResponse q F i)) :
    2 * (productCompressionLoss F (productResponse q F) selected -
      productCompressionLoss F (productResponse q F) competitor) ≤
      ((selected \ competitor).card : ℝ) * (2 * delta - mu) := by
  have h := pair_loss_le_sdiff_card_sub_score_surplus q F delta hWeight hNorm
    hDeltaNonneg hdelta selected competitor k hTop hCompetitorCard
  have hc : (selected \ competitor).card = (competitor \ selected).card :=
    Finset.card_sdiff_comm (hTop.1.trans hCompetitorCard.symm)
  have hs := score_surplus_ge_card_mul_margin (selected \ competitor)
    (competitor \ selected) (fun j => osc (productResponse q F j)) mu hc
    (fun i hi j hj => hMargin i (Finset.mem_sdiff.mp hi).1 j (Finset.mem_sdiff.mp hj).2)
  nlinarith

end CIGAMF.P13.D6MarginSensitiveExchange
#print axioms CIGAMF.P13.D6MarginSensitiveExchange.pair_loss_le_sdiff_card_sub_score_surplus
#print axioms CIGAMF.P13.D6MarginSensitiveExchange.score_surplus_ge_card_mul_margin
#print axioms CIGAMF.P13.D6MarginSensitiveExchange.pair_doubled_loss_le_card_mul_two_delta_sub_margin
