import Mathlib
import «LeanD6SmallSymmetricDifference»

/-!
# Exact symmetric-difference reduction for D6

`pair_loss_le_sdiff_card` is the already-written direct NEW-1 theorem.  This
module packages the pure finite combinatorics showing that it proves the
headline coefficient everywhere except the unique maximal-distance geometry:
an even universe split into two complementary equal halves.

The direct NEW-1 inequality does not by itself construct a PAEC filling of
mass `2r`; no LP-duality/completeness claim is made here.
-/

namespace CIGAMF.P13.D6SymmetricDifferenceReduction

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6SmallSymmetricDifference

variable {U : Type*} [Fintype U] [Nonempty U]

theorem equal_card_small_symmdiff_or_balanced_complement {n : ℕ}
    (S T : Finset (Fin (n + 1))) (hcard : S.card = T.card) :
    2 * (S \ T).card ≤ n ∨
      (n + 1 = 2 * S.card ∧ Disjoint S T ∧ S ∪ T = Finset.univ) := by
  classical
  by_cases hSmall : 2 * (S \ T).card ≤ n
  · exact Or.inl hSmall
  · right
    have hdiff : (S \ T).card = (T \ S).card :=
      Finset.card_sdiff_comm hcard
    have hdisj : Disjoint (S \ T) (T \ S) := by
      exact Finset.disjoint_left.mpr (by aesop)
    have hsub : (S \ T) ∪ (T \ S) ⊆ Finset.univ := Finset.subset_univ _
    have hcardUnion : ((S \ T) ∪ (T \ S)).card =
        (S \ T).card + (T \ S).card :=
      Finset.card_union_of_disjoint hdisj
    have hle : 2 * (S \ T).card ≤ n + 1 := by
      have hu := Finset.card_le_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at hu
      omega
    have heq : 2 * (S \ T).card = n + 1 := by omega
    have hfull : (S \ T) ∪ (T \ S) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le hsub
      simp only [Finset.card_univ, Fintype.card_fin, hcardUnion, hdiff]
      omega
    have hSTdisj : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro a haS haT
      have haFull : a ∈ (S \ T) ∪ (T \ S) := by
        rw [hfull]
        simp
      rcases Finset.mem_union.mp haFull with ha | ha
      · exact (Finset.mem_sdiff.mp ha).2 haT
      · exact (Finset.mem_sdiff.mp ha).2 haS
    have hUnion : S ∪ T = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      rw [Finset.card_univ, Fintype.card_fin,
        Finset.card_union_of_disjoint hSTdisj, ← hcard]
      have hInter : S ∩ T = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hSTdisj
      have hInter' : T ∩ S = ∅ := by simpa [Finset.inter_comm] using hInter
      have hSdiff : (S \ T).card = S.card := by
        rw [Finset.card_sdiff, hInter']
        simp
      omega
    have hInter : S ∩ T = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hSTdisj
    have hInter' : T ∩ S = ∅ := by simpa [Finset.inter_comm] using hInter
    have hSdiff : (S \ T).card = S.card := by
      rw [Finset.card_sdiff, hInter']
      simp
    exact ⟨by omega, hSTdisj, hUnion⟩

theorem pair_half_factor_except_balanced_complement {n : ℕ}
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
    (hCompetitorCard : competitor.card = k)
    (hNotExceptional : ¬(n + 1 = 2 * selected.card ∧
      Disjoint selected competitor ∧ selected ∪ competitor = Finset.univ)) :
    productCompressionLoss F (productResponse q F) selected -
        productCompressionLoss F (productResponse q F) competitor ≤
      (n : ℝ) * delta / 2 := by
  have hcard : selected.card = competitor.card := by
    rw [hTop.1, hCompetitorCard]
  rcases equal_card_small_symmdiff_or_balanced_complement
      selected competitor hcard with hSmall | hExceptional
  · exact pair_half_factor_of_small_symmetric_difference q F delta hWeight
      hNorm hDeltaNonneg hdelta selected competitor k hTop hCompetitorCard hSmall
  · exact False.elim (hNotExceptional hExceptional)

end CIGAMF.P13.D6SymmetricDifferenceReduction
