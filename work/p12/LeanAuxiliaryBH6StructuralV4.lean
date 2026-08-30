import Mathlib
import «LeanSupportGeometryV4»
import «LeanStructuralRankabilityV4»

/-! Auxiliary support-geometry and structural results.  The operational
MASTER is imported unchanged. -/

namespace CIGAMF.V4.AuxiliaryBH6Structural

open scoped BigOperators
open SupportGeometry
open StructuralRankability

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
variable [Fintype ι] [DecidableEq ι]

noncomputable def globalE (f : ι → Ω → ℝ) : ℝ :=
  ePlus Finset.univ f + eMinus Finset.univ f

private theorem maxGap_nonneg (f : ι → Ω → ℝ) (j : ι) (a : Ω) :
    0 ≤ componentMax f j - f j a := by
  exact sub_nonneg.mpr (le_maxVal (f j) a)

private theorem minGap_nonneg (f : ι → Ω → ℝ) (j : ι) (a : Ω) :
    0 ≤ f j a - componentMin f j := by
  exact sub_nonneg.mpr (minVal_le (f j) a)

private theorem minVal_mono
    (u v : Ω → ℝ) (h : ∀ a, u a ≤ v a) : minVal u ≤ minVal v := by
  rcases exists_eq_minVal v with ⟨a, ha⟩
  calc
    minVal u ≤ u a := minVal_le u a
    _ ≤ v a := h a
    _ = minVal v := ha

theorem ePlus_subset_le_global (T : Finset ι) (f : ι → Ω → ℝ) :
    ePlus T f ≤ ePlus Finset.univ f := by
  unfold ePlus
  apply minVal_mono
  intro a
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun j _ _ => maxGap_nonneg f j a)

theorem eMinus_subset_le_global (T : Finset ι) (f : ι → Ω → ℝ) :
    eMinus T f ≤ eMinus Finset.univ f := by
  unfold eMinus
  apply minVal_mono
  intro a
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
    (fun j _ _ => minGap_nonneg f j a)

theorem BH6_deficit_le_globalE (T : Finset ι) (f : ι → Ω → ℝ) :
    deficit T f ≤ globalE f := by
  rw [(BH3_exact_support_deficit_identity T f).1]
  unfold globalE
  exact add_le_add (ePlus_subset_le_global T f) (eMinus_subset_le_global T f)

theorem BH6_cardinality_topC_global_E_half
    (f : ι → Ω → ℝ) (trueTop optimum : Finset ι) (k : ℕ)
    (hTop : IsTopKByScore (componentSpan f) trueTop k)
    (hOptCard : optimum.card = k) :
    selectedRadius f trueTop - selectedRadius f optimum ≤ globalE f / 2 := by
  exact BH5_cardinality_topC_support_deficit f trueTop optimum k (globalE f)
    hTop hOptCard (BH6_deficit_le_globalE optimumᶜ f)

theorem modularity_radius_formula
    (f : ι → Ω → ℝ) (hmod : AllSubsetsModular f) (S : Finset ι) :
    selectedRadius f S = Sᶜ.sum (componentSpan f) / 2 := by
  unfold selectedRadius
  rw [hmod Sᶜ]
  rfl

theorem S2_all_subsets_modular_implies_topC_exact_at_k
    (f : ι → Ω → ℝ) (hmod : AllSubsetsModular f)
    (top : Finset ι) (k : ℕ)
    (hTop : IsTopKByScore (componentSpan f) top k) :
    ∀ S : Finset ι, S.card = k → selectedRadius f top ≤ selectedRadius f S := by
  intro S hcard
  rw [modularity_radius_formula f hmod top, modularity_radius_formula f hmod S]
  exact div_le_div_of_nonneg_right
    (topK_implies_omitted_modular_min (componentSpan f) top S k hTop hcard)
    (by norm_num)

theorem S2_all_subsets_modular_implies_topC_exact_all_budgets
    (f : ι → Ω → ℝ) (hmod : AllSubsetsModular f)
    (topC : ℕ → Finset ι)
    (hTop : ∀ k, k ≤ Fintype.card ι →
      IsTopKByScore (componentSpan f) (topC k) k) :
    TopCExactAllBudgets (selectedRadius f) topC := by
  intro k hk S hcard
  exact S2_all_subsets_modular_implies_topC_exact_at_k f hmod (topC k) k
    (hTop k hk) S hcard

private theorem ePlus_nonneg (T : Finset ι) (f : ι → Ω → ℝ) :
    0 ≤ ePlus T f := by
  unfold ePlus
  apply le_minVal
  intro a
  exact Finset.sum_nonneg (fun j hj => maxGap_nonneg f j a)

private theorem eMinus_nonneg (T : Finset ι) (f : ι → Ω → ℝ) :
    0 ≤ eMinus T f := by
  unfold eMinus
  apply le_minVal
  intro a
  exact Finset.sum_nonneg (fun j hj => minGap_nonneg f j a)

theorem S3_all_subsets_modular_implies_global_coextremizable
    (f : ι → Ω → ℝ) :
    AllSubsetsModular f → GloballyCoextremizable f := by
  intro hmod
  have hdef : deficit Finset.univ f = 0 := by
    unfold deficit
    rw [hmod Finset.univ]
    ring
  have hid := (BH3_exact_support_deficit_identity Finset.univ f).1
  have hp0 : ePlus Finset.univ f = 0 := by
    have hp := ePlus_nonneg Finset.univ f
    have hm := eMinus_nonneg Finset.univ f
    linarith
  have hm0 : eMinus Finset.univ f = 0 := by
    have hp := ePlus_nonneg Finset.univ f
    have hm := eMinus_nonneg Finset.univ f
    linarith
  let plusGap : Ω → ℝ := fun a =>
    Finset.univ.sum (fun j => componentMax f j - f j a)
  let minusGap : Ω → ℝ := fun a =>
    Finset.univ.sum (fun j => f j a - componentMin f j)
  rcases exists_eq_minVal plusGap with ⟨amax, hamax⟩
  rcases exists_eq_minVal minusGap with ⟨amin, hamin⟩
  have hsumMax : Finset.univ.sum (fun j => componentMax f j - f j amax) = 0 := by
    change plusGap amax = 0
    rw [hamax]
    exact hp0
  have hsumMin : Finset.univ.sum (fun j => f j amin - componentMin f j) = 0 := by
    change minusGap amin = 0
    rw [hamin]
    exact hm0
  refine ⟨amax, amin, ?_, ?_⟩
  · intro j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun l _ => maxGap_nonneg f l amax)).mp hsumMax j (Finset.mem_univ j)
    linarith
  · intro j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun l _ => minGap_nonneg f l amin)).mp hsumMin j (Finset.mem_univ j)
    linarith

theorem S3_global_coextremizable_iff_all_subsets_modular
    (f : ι → Ω → ℝ) :
    GloballyCoextremizable f ↔ AllSubsetsModular f := by
  constructor
  · exact S1_global_coextremizable_implies_all_subsets_modular f
  · exact S3_all_subsets_modular_implies_global_coextremizable f

section StrictnessWitnesses

theorem prefixSet_card_of_full
    (ranking : List ι) (hfull : IsFullRanking ranking)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    (prefixSet ranking k).card = k := by
  have hlen : ranking.length = Fintype.card ι := by
    calc
      ranking.length = ranking.toFinset.card :=
        (List.toFinset_card_of_nodup hfull.1).symm
      _ = Finset.univ.card := congrArg Finset.card hfull.2
      _ = Fintype.card ι := Finset.card_univ
  unfold prefixSet
  rw [List.toFinset_card_of_nodup hfull.1.take]
  simp [List.length_take, hlen, Nat.min_eq_left hk]

def scalarNotTopObjective (S : Finset (Fin 2)) : ℝ :=
  if S.card = 1 then if (1 : Fin 2) ∈ S then 0 else 1 else 0

def badTopC : ℕ → Finset (Fin 2) := fun k =>
  if k = 1 then {(0 : Fin 2)} else ([(1 : Fin 2), 0].take k).toFinset

theorem W1_scalar_prefix_rankable_not_topC_exact :
    ScalarPrefixRankable scalarNotTopObjective ∧
      ¬ TopCExactAllBudgets scalarNotTopObjective badTopC := by
  constructor
  · refine ⟨[(1 : Fin 2), 0], ?_, ?_⟩
    · constructor
      · decide
      · ext x
        fin_cases x <;> simp
    intro k hk S hcard
    have hk2 : k ≤ 2 := by simpa using hk
    interval_cases k <;>
      simp_all [prefixSet, scalarNotTopObjective] <;> split_ifs <;> norm_num
  · intro h
    have hbad := h 1 (by decide) ({(1 : Fin 2)} : Finset (Fin 2)) (by simp)
    norm_num [badTopC, scalarNotTopObjective] at hbad

def antiF (j a : Bool) : ℝ := if j = a then 1 else 0

theorem antiF_componentMax (j : Bool) :
    componentMax antiF j = 1 := by
  apply le_antisymm
  · apply maxVal_le
    intro a
    simp only [antiF]
    split_ifs <;> norm_num
  · unfold componentMax
    simpa [antiF] using le_maxVal (antiF j) j

theorem antiF_componentMin (j : Bool) :
    componentMin antiF j = 0 := by
  apply le_antisymm
  · unfold componentMin
    simpa [antiF] using minVal_le (antiF j) (!j)
  · apply le_minVal
    intro a
    simp only [antiF]
    split_ifs <;> norm_num

theorem antiF_singleton_radius (j : Bool) :
    selectedRadius antiF ({j} : Finset Bool) = 1 / 2 := by
  have hcomp : ({j} : Finset Bool)ᶜ = {!j} := by
    ext x
    cases j <;> cases x <;> simp
  rw [selectedRadius, hcomp]
  have hexact := BH4_coextremizable_exactness ({!j} : Finset Bool) antiF (!j) j
    (fun l hl => by
      have : l = !j := by simpa using hl
      subst l
      simp [antiF, antiF_componentMax])
    (fun l hl => by
      have : l = !j := by simpa using hl
      subst l
      simp [antiF, antiF_componentMin])
  rw [hexact]
  simp [modularSpan, componentSpan, antiF_componentMax, antiF_componentMin]

def antiTopC : ℕ → Finset Bool := fun k =>
  if k = 0 then ∅ else if k = 1 then {false} else Finset.univ

theorem antiF_topC_exact_all_budgets :
    TopCExactAllBudgets (selectedRadius antiF) antiTopC := by
  intro k hk S hcard
  have hk2 : k ≤ 2 := by simpa using hk
  interval_cases k
  · have hS : S = ∅ := Finset.card_eq_zero.mp hcard
    subst S
    simp [antiTopC]
  · rcases Finset.card_eq_one.mp hcard with ⟨a, rfl⟩
    cases a <;> simp [antiTopC, antiF_singleton_radius]
  · have hS : S = Finset.univ := S.card_eq_iff_eq_univ.mp (by simpa using hcard)
    subst S
    simp [antiTopC]

theorem antiF_not_globally_coextremizable :
    ¬ GloballyCoextremizable antiF := by
  rintro ⟨amax, amin, hmax, hmin⟩
  have hfalse := hmax false
  have htrue := hmax true
  have hfmax := antiF_componentMax false
  have htmax := antiF_componentMax true
  cases amax <;> simp [antiF] at hfalse htrue <;> linarith

theorem W2_topC_exact_not_global_coextremizable :
    TopCExactAllBudgets (selectedRadius antiF) antiTopC ∧
      ¬ GloballyCoextremizable antiF :=
  ⟨antiF_topC_exact_all_budgets, antiF_not_globally_coextremizable⟩

def nonnestedObjective (S : Finset (Fin 3)) : ℝ :=
  if S.card = 1 then
    if S = {(0 : Fin 3)} then 0 else 1
  else if S.card = 2 then
    if S = {(1 : Fin 3), 2} then 0 else 1
  else 0

theorem W3_nonnested_unique_optima_not_scalar_prefix :
    ¬ ScalarPrefixRankable nonnestedObjective := by
  rintro ⟨ranking, hfull, hopt⟩
  have hc1 := prefixSet_card_of_full ranking hfull 1 (by decide)
  have hc2 := prefixSet_card_of_full ranking hfull 2 (by decide)
  have h1 := hopt 1 (by decide) ({(0 : Fin 3)} : Finset (Fin 3)) (by simp)
  have h2 := hopt 2 (by decide) ({(1 : Fin 3), 2} : Finset (Fin 3)) (by simp)
  have hp1 : prefixSet ranking 1 = {(0 : Fin 3)} := by
    by_contra hne
    simp [nonnestedObjective, hc1, hne] at h1
    norm_num at h1
  have hp2 : prefixSet ranking 2 = {(1 : Fin 3), 2} := by
    by_contra hne
    simp [nonnestedObjective, hc2, hne] at h2
    norm_num at h2
  have hnested := prefixSet_nested ranking 1
  rw [hp1, hp2] at hnested
  have := hnested (by simp : (0 : Fin 3) ∈ ({0} : Finset (Fin 3)))
  have hne : (0 : Fin 3) ≠ 2 := by decide
  exact hne (by simpa using this)

end StrictnessWitnesses

end CIGAMF.V4.AuxiliaryBH6Structural
