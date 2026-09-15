import Mathlib
import «LeanAuxiliaryBH6StructuralV4»

/-! Strictness witnesses inside the actual CIG-AMF support-radius class. -/
namespace CIGAMF.V4.StructuralGeometryWitnesses

open SupportGeometry StructuralRankability AuxiliaryBH6Structural

@[simp] theorem fin3_compl_0 : ({0} : Finset (Fin 3))ᶜ = {1,2} := by decide
@[simp] theorem fin3_compl_1 : ({1} : Finset (Fin 3))ᶜ = {0,2} := by decide
@[simp] theorem fin3_compl_2 : ({2} : Finset (Fin 3))ᶜ = {0,1} := by decide
@[simp] theorem fin3_compl_01 : ({0,1} : Finset (Fin 3))ᶜ = {2} := by decide
@[simp] theorem fin3_compl_02 : ({0,2} : Finset (Fin 3))ᶜ = {1} := by decide
@[simp] theorem fin3_compl_12 : ({1,2} : Finset (Fin 3))ᶜ = {0} := by decide

theorem selectedRadius_from_extrema
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι]
    (f : ι → Ω → ℝ) (S : Finset ι) (M m : ℝ)
    (hmax : ∀ a, sumComponent Sᶜ f a ≤ M)
    (hmin : ∀ a, m ≤ sumComponent Sᶜ f a)
    (amax amin : Ω)
    (hmaxeq : sumComponent Sᶜ f amax = M)
    (hmineq : sumComponent Sᶜ f amin = m) :
    selectedRadius f S = (M - m) / 2 := by
  have hM : maxVal (sumComponent Sᶜ f) = M := by
    apply le_antisymm (maxVal_le _ hmax)
    rw [← hmaxeq]
    exact le_maxVal _ amax
  have hm : minVal (sumComponent Sᶜ f) = m := by
    apply le_antisymm
    · rw [← hmineq]
      exact minVal_le _ amin
    · exact le_minVal _ hmin
  simp [selectedRadius, supportOsc, osc, hM, hm]

theorem componentSpan_from_extrema
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι]
    (f : ι → Ω → ℝ) (j : ι) (M m : ℝ)
    (hmax : ∀ a, f j a ≤ M) (hmin : ∀ a, m ≤ f j a)
    (amax amin : Ω) (hmaxeq : f j amax = M) (hmineq : f j amin = m) :
    componentSpan f j = M - m := by
  have hM : componentMax f j = M := by
    unfold componentMax
    apply le_antisymm (maxVal_le _ hmax)
    rw [← hmaxeq]
    exact le_maxVal _ amax
  have hm : componentMin f j = m := by
    unfold componentMin
    apply le_antisymm
    · rw [← hmineq]
      exact minVal_le _ amin
    · exact le_minVal _ hmin
  simp [componentSpan, hM, hm]

/- Search witness:
Ω={(0,0,0),(0,1,1),(1,0,0)}, slopes=(-2,1,-3).
The optimal nested ranking is (0,2,1), whereas the unique-span Top-C ranking
is (2,0,1). -/
def w1F (j a : Fin 3) : ℝ :=
  if j = 0 then (if a = 2 then -2 else 0)
  else if j = 1 then (if a = 1 then 1 else 0)
  else (if a = 1 then -3 else 0)

theorem w1_radius_keep0 : selectedRadius w1F ({0} : Finset (Fin 3)) = 1 := by
  calc
    _ = (0 - (-2 : ℝ)) / 2 := selectedRadius_from_extrema w1F {0} 0 (-2)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num) 0 1
      (by simp [sumComponent, w1F]) (by simp [sumComponent, w1F] <;> norm_num)
    _ = 1 := by norm_num

theorem w1_radius_keep1 : selectedRadius w1F ({1} : Finset (Fin 3)) = 3 / 2 := by
  calc
    _ = (0 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema w1F {1} 0 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num) 0 1
      (by simp [sumComponent, w1F]) (by simp [sumComponent, w1F])
    _ = 3 / 2 := by norm_num

theorem w1_radius_keep2 : selectedRadius w1F ({2} : Finset (Fin 3)) = 3 / 2 := by
  calc
    _ = (1 - (-2 : ℝ)) / 2 := selectedRadius_from_extrema w1F {2} 1 (-2)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num) 1 2
      (by simp [sumComponent, w1F]) (by simp [sumComponent, w1F])
    _ = 3 / 2 := by norm_num

theorem w1_radius_keep02 :
    selectedRadius w1F ({0, 2} : Finset (Fin 3)) = 1 / 2 := by
  calc
    _ = (1 - 0 : ℝ) / 2 := selectedRadius_from_extrema w1F {0, 2} 1 0
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num) 1 0
      (by simp [sumComponent, w1F]) (by simp [sumComponent, w1F])
    _ = 1 / 2 := by norm_num

theorem w1_radius_keep01 : selectedRadius w1F ({0,1} : Finset (Fin 3)) = 3 / 2 := by
  calc
    _ = (0 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema w1F {0,1} 0 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num) 0 1
      (by simp [sumComponent, w1F]) (by simp [sumComponent, w1F])
    _ = 3 / 2 := by norm_num

theorem w1_radius_keep12 : selectedRadius w1F ({1,2} : Finset (Fin 3)) = 1 := by
  calc
    _ = (0 - (-2 : ℝ)) / 2 := selectedRadius_from_extrema w1F {1,2} 0 (-2)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w1F] <;> norm_num) 0 2
      (by simp [sumComponent, w1F]) (by simp [sumComponent, w1F])
    _ = 1 := by norm_num

def w1OptimalRanking : List (Fin 3) := [0, 2, 1]
def w1TopCRanking : List (Fin 3) := [2, 0, 1]
def w1TopC (k : ℕ) : Finset (Fin 3) := prefixSet w1TopCRanking k

@[simp] theorem w1_span0 : componentSpan w1F 0 = 2 := by
  convert componentSpan_from_extrema w1F 0 0 (-2)
    (by intro a; fin_cases a <;> simp [w1F])
    (by intro a; fin_cases a <;> simp [w1F]) 0 2
    (by simp [w1F]) (by simp [w1F]) using 1 <;> norm_num

@[simp] theorem w1_span1 : componentSpan w1F 1 = 1 := by
  convert componentSpan_from_extrema w1F 1 1 0
    (by intro a; fin_cases a <;> simp [w1F])
    (by intro a; fin_cases a <;> simp [w1F]) 1 0
    (by simp [w1F]) (by simp [w1F]) using 1 <;> norm_num

@[simp] theorem w1_span2 : componentSpan w1F 2 = 3 := by
  convert componentSpan_from_extrema w1F 2 0 (-3)
    (by intro a; fin_cases a <;> simp [w1F])
    (by intro a; fin_cases a <;> simp [w1F]) 0 1
    (by simp [w1F]) (by simp [w1F]) using 1 <;> norm_num

theorem W1_geometry_topC_is_score_topK :
    ∀ k, k ≤ Fintype.card (Fin 3) →
      IsTopKByScore (componentSpan w1F) (w1TopC k) k := by
  intro k hk
  have hk3 : k ≤ 3 := by simpa using hk
  have hC : componentSpan w1F = fun j : Fin 3 =>
      if j = 0 then 2 else if j = 1 then 1 else 3 := by
    funext j
    fin_cases j <;> simp
  rw [hC]
  constructor
  · interval_cases k <;> decide
  · intro S hcard
    interval_cases k
    · have hS : S = ∅ := Finset.card_eq_zero.mp hcard
      subst S
      norm_num [w1TopC, prefixSet, w1TopCRanking]
    · rcases Finset.card_eq_one.mp hcard with ⟨a, rfl⟩
      fin_cases a
      · simp [w1TopC, prefixSet, w1TopCRanking] <;> norm_num
      · simp [w1TopC, prefixSet, w1TopCRanking] <;> norm_num
      · simp [w1TopC, prefixSet, w1TopCRanking] <;> norm_num
    · have hcomp : Sᶜ.card = 1 := by simp [Finset.card_compl, hcard]
      rcases Finset.card_eq_one.mp hcomp with ⟨a, ha⟩
      have hs : S = ({a} : Finset (Fin 3))ᶜ := by rw [← ha, compl_compl]
      fin_cases a
      · have hs0 : S = ({0} : Finset (Fin 3))ᶜ := by simpa using hs
        rw [hs0, fin3_compl_0]
        simp [w1TopC, prefixSet, w1TopCRanking] <;> norm_num
      · have hs1 : S = ({1} : Finset (Fin 3))ᶜ := by simpa using hs
        rw [hs1, fin3_compl_1]
        simp [w1TopC, prefixSet, w1TopCRanking] <;> norm_num
      · have hs2 : S = ({2} : Finset (Fin 3))ᶜ := by simpa using hs
        rw [hs2, fin3_compl_2]
        simp [w1TopC, prefixSet, w1TopCRanking] <;> norm_num
    · have hS : S = Finset.univ := S.card_eq_iff_eq_univ.mp (by simpa using hcard)
      subst S
      rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
      simp [w1TopC, prefixSet, w1TopCRanking] <;> norm_num

theorem selectedRadius_nonneg
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι]
    (f : ι → Ω → ℝ) (S : Finset ι) : 0 ≤ selectedRadius f S := by
  unfold selectedRadius
  exact div_nonneg (osc_nonneg _) (by norm_num)

theorem W1_geometry_scalar_prefix_rankable :
    ScalarPrefixRankable (selectedRadius w1F) := by
  refine ⟨w1OptimalRanking, ?_, ?_⟩
  · constructor
    · decide
    · ext x
      fin_cases x <;> simp [w1OptimalRanking]
  · intro k hk S hcard
    have hk3 : k ≤ 3 := by simpa using hk
    interval_cases k
    · have hS : S = ∅ := Finset.card_eq_zero.mp hcard
      subst S
      simp [prefixSet, w1OptimalRanking]
    · rcases Finset.card_eq_one.mp hcard with ⟨a, rfl⟩
      fin_cases a
      · simp [prefixSet, w1OptimalRanking, w1_radius_keep0]
      · norm_num [prefixSet, w1OptimalRanking, w1_radius_keep0, w1_radius_keep1]
      · change selectedRadius w1F ({0} : Finset (Fin 3)) ≤ selectedRadius w1F {2}
        rw [w1_radius_keep0, w1_radius_keep2]
        norm_num
    · have hcomp : Sᶜ.card = 1 := by simp [Finset.card_compl, hcard]
      rcases Finset.card_eq_one.mp hcomp with ⟨a, ha⟩
      have hs : S = ({a} : Finset (Fin 3))ᶜ := by rw [← ha, compl_compl]
      fin_cases a
      · have heq : ({(0 : Fin 3)} : Finset (Fin 3))ᶜ = {1,2} := by ext x <;> fin_cases x <;> simp
        have hs0 : S = ({0} : Finset (Fin 3))ᶜ := by simpa using hs
        rw [hs0, heq, w1_radius_keep12]
        norm_num [prefixSet, w1OptimalRanking, w1_radius_keep02]
      · have heq : ({(1 : Fin 3)} : Finset (Fin 3))ᶜ = {0,2} := by ext x <;> fin_cases x <;> simp
        have hs1 : S = ({1} : Finset (Fin 3))ᶜ := by simpa using hs
        rw [hs1, heq]
        norm_num [prefixSet, w1OptimalRanking, w1_radius_keep02]
      · have heq : ({(2 : Fin 3)} : Finset (Fin 3))ᶜ = {0,1} := by ext x <;> fin_cases x <;> simp
        have hs2 : S = ({2} : Finset (Fin 3))ᶜ := by simpa using hs
        rw [hs2, heq, w1_radius_keep01]
        norm_num [prefixSet, w1OptimalRanking, w1_radius_keep02]
    · have hS : S = Finset.univ := S.card_eq_iff_eq_univ.mp (by simpa using hcard)
      subst S
      have hp : prefixSet w1OptimalRanking 3 = (Finset.univ : Finset (Fin 3)) := by
        ext x <;> fin_cases x <;> simp [prefixSet, w1OptimalRanking]
      rw [hp]

theorem W1_geometry_topC_not_exact :
    ¬ TopCExactAllBudgets (selectedRadius w1F) w1TopC := by
  intro h
  have bad := h 1 (by decide) ({0} : Finset (Fin 3)) (by simp)
  rw [show w1TopC 1 = ({2} : Finset (Fin 3)) by
      simp [w1TopC, prefixSet, w1TopCRanking], w1_radius_keep2,
    w1_radius_keep0] at bad
  norm_num at bad

theorem W1_geometry_strictness :
    ScalarPrefixRankable (selectedRadius w1F) ∧
      ¬ TopCExactAllBudgets (selectedRadius w1F) w1TopC :=
  ⟨W1_geometry_scalar_prefix_rankable, W1_geometry_topC_not_exact⟩

theorem W1_geometry_strictness_typed :
    ScalarPrefixRankable (selectedRadius w1F) ∧
      (∀ k, k ≤ Fintype.card (Fin 3) →
        IsTopKByScore (componentSpan w1F) (w1TopC k) k) ∧
      ¬ TopCExactAllBudgets (selectedRadius w1F) w1TopC :=
  ⟨W1_geometry_scalar_prefix_rankable,
    W1_geometry_topC_is_score_topK, W1_geometry_topC_not_exact⟩

/- Search witness:
Ω={(0,0,1),(0,1,0),(1,0,0)}, slopes=(-3,-3,1).
The unique k=1 optimum is {2}; the unique k=2 optimum is {0,1}. -/
def w3F (j a : Fin 3) : ℝ :=
  if j = 0 then (if a = 2 then -3 else 0)
  else if j = 1 then (if a = 1 then -3 else 0)
  else (if a = 0 then 1 else 0)

theorem w3_r0 : selectedRadius w3F ({0} : Finset (Fin 3)) = 2 := by
  calc
    _ = (1 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema w3F {0} 1 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num) 0 1
      (by simp [sumComponent, w3F]) (by simp [sumComponent, w3F])
    _ = 2 := by norm_num

theorem w3_r1 : selectedRadius w3F ({1} : Finset (Fin 3)) = 2 := by
  calc
    _ = (1 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema w3F {1} 1 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num) 0 2
      (by simp [sumComponent, w3F]) (by simp [sumComponent, w3F])
    _ = 2 := by norm_num

theorem w3_r2 : selectedRadius w3F ({2} : Finset (Fin 3)) = 3 / 2 := by
  calc
    _ = (0 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema w3F {2} 0 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num) 0 1
      (by simp [sumComponent, w3F]) (by simp [sumComponent, w3F])
    _ = 3 / 2 := by norm_num

theorem w3_r01 : selectedRadius w3F ({0,1} : Finset (Fin 3)) = 1 / 2 := by
  calc
    _ = (1 - 0 : ℝ) / 2 := selectedRadius_from_extrema w3F {0,1} 1 0
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num) 0 1
      (by simp [sumComponent, w3F]) (by simp [sumComponent, w3F])
    _ = 1 / 2 := by norm_num

theorem w3_r02 : selectedRadius w3F ({0,2} : Finset (Fin 3)) = 3 / 2 := by
  calc
    _ = (0 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema w3F {0,2} 0 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num) 0 1
      (by simp [sumComponent, w3F]) (by simp [sumComponent, w3F])
    _ = 3 / 2 := by norm_num

theorem w3_r12 : selectedRadius w3F ({1,2} : Finset (Fin 3)) = 3 / 2 := by
  calc
    _ = (0 - (-3 : ℝ)) / 2 := selectedRadius_from_extrema w3F {1,2} 0 (-3)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num)
      (by intro a; fin_cases a <;> simp [sumComponent, w3F] <;> norm_num) 0 2
      (by simp [sumComponent, w3F]) (by simp [sumComponent, w3F])
    _ = 3 / 2 := by norm_num

theorem W3_geometry_not_scalar_prefix_rankable :
    ¬ ScalarPrefixRankable (selectedRadius w3F) := by
  rintro ⟨ranking, hfull, hopt⟩
  have hc1 := prefixSet_card_of_full ranking hfull 1 (by decide)
  have hc2 := prefixSet_card_of_full ranking hfull 2 (by decide)
  have h1 := hopt 1 (by decide) ({2} : Finset (Fin 3)) (by simp)
  have h2 := hopt 2 (by decide) ({0,1} : Finset (Fin 3)) (by simp)
  have hp1 : prefixSet ranking 1 = ({2} : Finset (Fin 3)) := by
    rcases Finset.card_eq_one.mp hc1 with ⟨a, ha⟩
    rw [ha] at h1 ⊢
    fin_cases a
    · change selectedRadius w3F ({0} : Finset (Fin 3)) ≤ selectedRadius w3F {2} at h1
      rw [w3_r0, w3_r2] at h1
      norm_num at h1
    · change selectedRadius w3F ({1} : Finset (Fin 3)) ≤ selectedRadius w3F {2} at h1
      rw [w3_r1, w3_r2] at h1
      norm_num at h1
    · simp
  have hp2 : prefixSet ranking 2 = ({0,1} : Finset (Fin 3)) := by
    have hcomp : (prefixSet ranking 2)ᶜ.card = 1 := by
      simp [Finset.card_compl, hc2]
    rcases Finset.card_eq_one.mp hcomp with ⟨a, ha⟩
    have hs : prefixSet ranking 2 = ({a} : Finset (Fin 3))ᶜ := by
      rw [← ha, compl_compl]
    fin_cases a
    · have heq : ({(0 : Fin 3)} : Finset (Fin 3))ᶜ = {1,2} := by ext x <;> fin_cases x <;> simp
      have hs0 : prefixSet ranking 2 = ({0} : Finset (Fin 3))ᶜ := by simpa using hs
      rw [hs0, heq, w3_r12, w3_r01] at h2
      norm_num at h2
    · have heq : ({(1 : Fin 3)} : Finset (Fin 3))ᶜ = {0,2} := by ext x <;> fin_cases x <;> simp
      have hs1 : prefixSet ranking 2 = ({1} : Finset (Fin 3))ᶜ := by simpa using hs
      rw [hs1, heq, w3_r02, w3_r01] at h2
      norm_num at h2
    · have heq : ({(2 : Fin 3)} : Finset (Fin 3))ᶜ = {0,1} := by ext x <;> fin_cases x <;> simp
      have hs2 : prefixSet ranking 2 = ({2} : Finset (Fin 3))ᶜ := by simpa using hs
      rw [hs2, heq]
  have hnested := prefixSet_nested ranking 1
  rw [hp1, hp2] at hnested
  have : (2 : Fin 3) ∈ ({0,1} : Finset (Fin 3)) := hnested (by simp)
  simp at this

end CIGAMF.V4.StructuralGeometryWitnesses
