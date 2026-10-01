import «LeanStructuralRandomMenuV1»

namespace CIGAMF.P13.StructuralRandomMenuExact
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension CIGAMF.P13.StructuralStaircaseFamily
open CIGAMF.P13.StructuralStaircaseExactPrefixCover CIGAMF.P13.StructuralRandomMenu
noncomputable section
attribute [local instance] Classical.propDecidable
variable {r : ℕ}

def targetSize (r : ℕ) (delta : ℝ) : ℕ := ⌈(1-delta)*(r : ℝ)⌉₊

lemma targetSize_bounds (hr : 0<r) (delta : ℝ) (h0 : 0 ≤ delta) (h1 : delta<1) :
    0 < targetSize r delta ∧ targetSize r delta ≤ r ∧
      1-delta ≤ (targetSize r delta : ℝ)/r := by
  have hrR : (0 : ℝ)<r := by exact_mod_cast hr
  have hp : 0<(1-delta)*(r : ℝ) := mul_pos (by linarith) hrR
  have hc : (1-delta)*(r : ℝ) ≤ (targetSize r delta : ℝ) := Nat.le_ceil _
  have hlo : 0<targetSize r delta := by
    have hh : (0 : ℝ)<targetSize r delta := hp.trans_le hc
    exact_mod_cast hh
  refine ⟨hlo,?_,?_⟩
  · apply Nat.ceil_le.mpr
    nlinarith
  · exact (le_div_iff₀ hrR).mpr hc

theorem exact_random_lower {Ω : Type*} [Fintype Ω] (hr : 0<r) (eps delta : ℝ)
    (heps : 2*(r : ℝ)*eps<1) (p : Ω → ℝ) (hp : ∀ o,0 ≤ p o)
    (hpsum : ∑ o,p o=1) (menu : Ω → Finset (List (StairRel r))) (K : ℕ)
    (hK : ∀ o,(menu o).card ≤ K)
    (hs : ∀ t : Fin r,1-delta ≤ ∑ o,p o*(if t ∈ hitSet eps (menu o) then 1 else 0)) :
    targetSize r delta ≤ K := by
  have h := random_menu_lower hr eps delta heps p hp hpsum menu K hK hs
  apply Nat.ceil_le.mpr
  nlinarith

/-- Explicit uniform sample space: every outcome is a menu of exactly ceil((1-delta)r)
rankings, and each budget has success probability at least 1-delta. -/
theorem exact_random_upper (hr : 0<r) (eps delta : ℝ) (he : 0 ≤ eps)
    (h0 : 0 ≤ delta) (h1 : delta<1) :
    let C := (stairMenu r).powersetCard (targetSize r delta)
    C.Nonempty ∧ (∀ M ∈ C,M.card=targetSize r delta) ∧
      ∀ k ≤ Fintype.card (StairRel r),1-delta ≤
        ((C.filter (fun M => ∃ ranking ∈ M,
          EpsilonOptimalAt (fun S => selectedRadius staircaseF S/(r : ℝ)) eps k
            (prefixSet ranking k))).card : ℝ)/C.card := by
  obtain ⟨hK,hKr,hprob⟩ := targetSize_bounds hr delta h0 h1
  dsimp
  refine ⟨powersetCard_nonempty.mpr (by rw [canonical_menu_card hr]; exact hKr),?_,?_⟩
  · intro M hM; exact (mem_powersetCard.mp hM).2
  · intro k hk
    exact hprob.trans (actual_uniform_submenu_coverage hr eps he _ k hK hKr hk)

/-- Matching lower and attaining finite-uniform construction, with budget selected
independently of the random menu. The post-randomization adversary remains separate. -/
theorem random_menu_exact (hr : 0<r) (eps delta : ℝ) (he : 0 ≤ eps)
    (heps : 2*(r : ℝ)*eps<1) (h0 : 0 ≤ delta) (h1 : delta<1) :
    (∀ (Ω : Type) [Fintype Ω] (p : Ω → ℝ) (menu : Ω → Finset (List (StairRel r))) (K : ℕ),
      (∀ o,0 ≤ p o) → (∑ o,p o)=1 → (∀ o,(menu o).card ≤ K) →
      (∀ t : Fin r,1-delta ≤ ∑ o,p o*(if t ∈ hitSet eps (menu o) then 1 else 0)) →
      targetSize r delta ≤ K) ∧
    (let C := (stairMenu r).powersetCard (targetSize r delta);
      C.Nonempty ∧ (∀ M ∈ C,M.card=targetSize r delta) ∧
        ∀ k ≤ Fintype.card (StairRel r),1-delta ≤
          ((C.filter (fun M => ∃ ranking ∈ M,
            EpsilonOptimalAt (fun S => selectedRadius staircaseF S/(r : ℝ)) eps k
              (prefixSet ranking k))).card : ℝ)/C.card) := by
  refine ⟨?_,exact_random_upper hr eps delta he h0 h1⟩
  intro Ω inst p menu K hp hsum hK hs
  exact exact_random_lower hr eps delta heps p hp hsum menu K hK hs

#print axioms targetSize_bounds
#print axioms exact_random_lower
#print axioms exact_random_upper
#print axioms random_menu_exact
end
end CIGAMF.P13.StructuralRandomMenuExact
