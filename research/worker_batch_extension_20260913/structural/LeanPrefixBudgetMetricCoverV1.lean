import «LeanStructuralPrefixCoverDimensionV1»

/-! Finite metric-cover lemma for budget-indexed anchored rankings. The actual
support-radius application discharges the anchored-ranking premise separately. -/
namespace CIGAMF.P13.PrefixBudgetMetricCover
open Finset
open CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem metric_cover (objective : Finset I → ℝ) (phi : ℕ → ℝ)
    (hphi : Monotone phi) (hpos : ∀ k, 0 ≤ phi k)
    (hanchor : ∀ a, a ≤ Fintype.card I → ∃ r : List I, IsFullRanking r ∧
      ∀ k, a ≤ k → k ≤ Fintype.card I →
        EpsilonOptimalAt objective (phi k-phi a) k (prefixSet r k))
    (eps : ℝ) (heps : 0 < eps) :
    PrefixCoverDimensionAtMost objective eps (⌊phi (Fintype.card I)/eps⌋₊+1) := by
  let B := Fin (Fintype.card I+1)
  let N := ⌊phi (Fintype.card I)/eps⌋₊+1
  let bucket (k : B) : ℕ := ⌊phi k.val/eps⌋₊
  let fibre (b : Fin N) : Finset B := univ.filter (fun k => bucket k=b.val)
  let anchor (b : Fin N) : B := if hn : (fibre b).Nonempty then (fibre b).min' hn else 0
  have hrank (b : Fin N) : ∃ r : List I, IsFullRanking r ∧
      ∀ k, (anchor b).val ≤ k → k ≤ Fintype.card I →
        EpsilonOptimalAt objective (phi k-phi (anchor b).val) k (prefixSet r k) :=
    hanchor _ (by have := (anchor b).isLt;omega)
  choose r hr using hrank
  let menu : Finset (List I) := univ.image r
  refine ⟨menu,?_,?_,?_,?_⟩
  · exact card_image_le.trans (by simp [N])
  · have hN : 0 < N := by dsimp [N];omega
    haveI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
    exact image_nonempty.mpr univ_nonempty
  · intro s hs
    obtain ⟨b,_,rfl⟩ := mem_image.mp hs
    exact (hr b).1
  · intro k hk
    let kb : B := ⟨k,by omega⟩
    have hb : bucket kb < N := by
      have hh := Nat.floor_mono (div_le_div_of_nonneg_right (hphi hk) heps.le)
      dsimp [bucket,kb,N];omega
    let b : Fin N := ⟨bucket kb,hb⟩
    have hmem : kb ∈ fibre b := by simp [fibre,b]
    have hn : (fibre b).Nonempty := ⟨kb,hmem⟩
    have hale : (anchor b).val ≤ k := by
      have h := min'_le (fibre b) kb hmem
      change (anchor b).val ≤ kb.val
      change ((fibre b).min' hn).val ≤ kb.val at h
      simpa only [anchor,dif_pos hn] using h
    have hsame : bucket (anchor b)=bucket kb := by
      have h := min'_mem (fibre b) hn
      simpa only [fibre,mem_filter,mem_univ,true_and,anchor,dif_pos hn,b] using h
    have hlo := Nat.floor_le (div_nonneg (hpos (anchor b).val) heps.le)
    have hhi := Nat.lt_floor_add_one (phi k/eps)
    change (bucket (anchor b):ℝ) ≤ phi (anchor b).val/eps at hlo
    change phi k/eps < (bucket kb:ℝ)+1 at hhi
    rw [hsame] at hlo
    have hgap : phi k-phi (anchor b).val ≤ eps := by
      have hu : phi k/eps < phi (anchor b).val/eps+1 := by linarith
      have hh := (div_lt_iff₀ heps).mp (show (phi k-phi (anchor b).val)/eps < 1 by rw [sub_div];linarith)
      linarith
    have ho := (hr b).2 k hale hk
    refine ⟨r b,mem_image.mpr ⟨b,mem_univ _,rfl⟩,ho.1,?_⟩
    intro T hT
    have hh := ho.2 T hT
    linarith

#print axioms metric_cover
end
end CIGAMF.P13.PrefixBudgetMetricCover
