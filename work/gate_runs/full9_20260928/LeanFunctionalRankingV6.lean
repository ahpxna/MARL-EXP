import Mathlib
import «LeanFunctionalBoundaryV4»
import «LeanPairwiseMasterV4»

/-! Chain-A V6: response-surface error, within-relation extrema stability,
between-relation ranking, and directional sign stability.  This module is
independent of the frozen operational MASTER. -/

namespace CIGAMF.V6.FunctionalRanking

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.FunctionalBoundary

variable {A ι : Type*}
variable [Fintype A] [Nonempty A] [DecidableEq A]
variable [Fintype ι] [DecidableEq ι]

/-! ## A8: gauge-invariant Q error controls capacity error -/

theorem A8_gauge_capacity_bound (Qhat Q : A → ℝ) :
    |capacity Qhat - capacity Q| ≤ 2 * gaugeError Qhat Q := by
  have h := osc_add_deviation Q (fun a ↦ Qhat a - Q a)
  have heq : (fun a ↦ Q a + (Qhat a - Q a)) = Qhat := by
    funext a
    ring
  rw [heq] at h
  unfold capacity gaugeError
  convert h using 1 <;> ring

/-! ## A9: between-relation margins -/

theorem A9_pair_order_preserved
    (C Chat : ι → ℝ) (e : ι → ℝ) (j l : ι)
    (hj : |Chat j - C j| ≤ e j) (hl : |Chat l - C l| ≤ e l)
    (hmargin : e j + e l < C j - C l) :
    Chat l < Chat j := by
  have hj' := (abs_le.mp hj).1
  have hl' := (abs_le.mp hl).2
  linarith

def StrictTopK (C : ι → ℝ) (S : Finset ι) (k : ℕ) : Prop :=
  S.card = k ∧ ∀ j ∈ S, ∀ l ∉ S, C l < C j

def betweenCapacityGap (C : ι → ℝ) (j l : ι) : ℝ := C j - C l

theorem A9_per_relation_topK_margin
    (C Chat e : ι → ℝ) (S : Finset ι) (k : ℕ)
    (hcard : S.card = k)
    (hcover : ∀ j, |Chat j - C j| ≤ e j)
    (hmargin : ∀ j ∈ S, ∀ l ∉ S, e j + e l < C j - C l) :
    StrictTopK Chat S k := by
  refine ⟨hcard, ?_⟩
  intro j hj l hl
  exact A9_pair_order_preserved C Chat e j l (hcover j) (hcover l)
    (hmargin j hj l hl)

theorem A9_uniform_topK_margin
    (C Chat : ι → ℝ) (S : Finset ι) (k : ℕ) (e : ℝ)
    (hcard : S.card = k)
    (hcover : ∀ j, |Chat j - C j| ≤ e)
    (hmargin : ∀ j ∈ S, ∀ l ∉ S, 2 * e < C j - C l) :
    StrictTopK Chat S k := by
  apply A9_per_relation_topK_margin C Chat (fun _ ↦ e) S k hcard hcover
  intro j hj l hl
  simpa [two_mul] using hmargin j hj l hl

theorem strictTopK_unique
    (C : ι → ℝ) (S T : Finset ι) (k : ℕ)
    (hS : StrictTopK C S k) (hT : StrictTopK C T k) : S = T := by
  apply Finset.Subset.antisymm
  · intro j hj
    by_contra hjT
    have hnsub : ¬ T ⊆ S := by
      intro hTS
      have hEq : T = S := Finset.eq_of_subset_of_card_le hTS (by rw [hT.1, hS.1])
      exact hjT (hEq.symm ▸ hj)
    obtain ⟨l, hlT, hlS⟩ := Finset.not_subset.mp hnsub
    have h1 := hS.2 j hj l hlS
    have h2 := hT.2 l hlT j hjT
    linarith
  · intro j hj
    by_contra hjS
    have hnsub : ¬ S ⊆ T := by
      intro hST
      have hEq : S = T := Finset.eq_of_subset_of_card_le hST (by rw [hS.1, hT.1])
      exact hjS (hEq ▸ hj)
    obtain ⟨l, hlS, hlT⟩ := Finset.not_subset.mp hnsub
    have h1 := hT.2 j hj l hlT
    have h2 := hS.2 l hlS j hjS
    linarith

theorem A9_per_relation_topK_membership
    (C Chat e : ι → ℝ) (S Shat : Finset ι) (k : ℕ)
    (hcard : S.card = k)
    (hcover : ∀ j, |Chat j - C j| ≤ e j)
    (hmargin : ∀ j ∈ S, ∀ l ∉ S, e j + e l < C j - C l)
    (hShat : StrictTopK Chat Shat k) :
    Shat = S := by
  exact strictTopK_unique Chat Shat S k hShat
    (A9_per_relation_topK_margin C Chat e S k hcard hcover hmargin)

/-! ## A10: direct Q-surface error to global Top-C -/

theorem A10_Q_error_pair_order
    (Qhat Q : ι → A → ℝ) (j l : ι)
    (hmargin :
      2 * gaugeError (Qhat j) (Q j) + 2 * gaugeError (Qhat l) (Q l) <
        capacity (Q j) - capacity (Q l)) :
    capacity (Qhat l) < capacity (Qhat j) := by
  exact A9_pair_order_preserved
    (fun r ↦ capacity (Q r)) (fun r ↦ capacity (Qhat r))
    (fun r ↦ 2 * gaugeError (Qhat r) (Q r)) j l
    (A8_gauge_capacity_bound (Qhat j) (Q j))
    (A8_gauge_capacity_bound (Qhat l) (Q l)) hmargin

theorem A10_Q_error_topK
    (Qhat Q : ι → A → ℝ) (S : Finset ι) (k : ℕ)
    (hcard : S.card = k)
    (hmargin : ∀ j ∈ S, ∀ l ∉ S,
      2 * gaugeError (Qhat j) (Q j) + 2 * gaugeError (Qhat l) (Q l) <
        capacity (Q j) - capacity (Q l)) :
    StrictTopK (fun r ↦ capacity (Qhat r)) S k := by
  refine ⟨hcard, ?_⟩
  intro j hj l hl
  exact A10_Q_error_pair_order Qhat Q j l (hmargin j hj l hl)

theorem A10_Q_error_topK_membership
    (Qhat Q : ι → A → ℝ) (S Shat : Finset ι) (k : ℕ)
    (hcard : S.card = k)
    (hmargin : ∀ j ∈ S, ∀ l ∉ S,
      2 * gaugeError (Qhat j) (Q j) + 2 * gaugeError (Qhat l) (Q l) <
        capacity (Q j) - capacity (Q l))
    (hShat : StrictTopK (fun r ↦ capacity (Qhat r)) Shat k) :
    Shat = S := by
  exact strictTopK_unique (fun r ↦ capacity (Qhat r)) Shat S k hShat
    (A10_Q_error_topK Qhat Q S k hcard hmargin)

/-! ## A11: local extrema stability does not imply relation-rank stability -/

theorem maxVal_fin2 (f : Fin 2 → ℝ) : maxVal f = max (f 0) (f 1) := by
  apply le_antisymm
  · apply maxVal_le
    intro a
    fin_cases a
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (le_maxVal f 0) (le_maxVal f 1)

theorem minVal_fin2 (f : Fin 2 → ℝ) : minVal f = min (f 0) (f 1) := by
  apply le_antisymm
  · exact le_min (minVal_le f 0) (minVal_le f 1)
  · apply le_minVal
    intro a
    fin_cases a
    · exact min_le_left _ _
    · exact min_le_right _ _

def rankWitnessQ (r a : Fin 2) : ℝ :=
  if r = 0 then (if a = 0 then 0 else 10)
  else (if a = 0 then 0 else 9)

noncomputable def rankWitnessQhat (r a : Fin 2) : ℝ :=
  if r = 0 then (if a = 0 then 0 else 8)
  else (if a = 0 then 0 else 19 / 2)

theorem A11_all_local_extrema_stable :
    ∀ r : Fin 2, PreservesExtrema (rankWitnessQhat r) (rankWitnessQ r) 1 0 := by
  intro r
  fin_cases r <;> constructor <;> intro a ha <;> fin_cases a <;>
    simp_all [rankWitnessQ, rankWitnessQhat] <;> norm_num

theorem A11_all_local_phase_conditions :
    (∀ r : Fin 2,
      gaugeError (rankWitnessQhat r) (rankWitnessQ r) <
        (if r = 0 then 10 else 9) / 2) := by
  intro r
  fin_cases r <;>
    simp [gaugeError, osc, maxVal_fin2, minVal_fin2, rankWitnessQ, rankWitnessQhat] <;>
    norm_num

theorem A11_local_stability_not_global_rank_stability :
    capacity (rankWitnessQ 1) < capacity (rankWitnessQ 0) ∧
    capacity (rankWitnessQhat 0) < capacity (rankWitnessQhat 1) := by
  simp [capacity, osc, maxVal_fin2, minVal_fin2, rankWitnessQ, rankWitnessQhat]
  norm_num

/-! ## A12: directional sign margins -/

theorem A12_direction_positive
    (w Qhat Q : A → ℝ) (eps : ℝ)
    (hSup : ∀ a, |Qhat a - Q a| ≤ eps) (heps : 0 ≤ eps)
    (hmargin : (Finset.univ.sum fun a ↦ |w a|) * eps < direction w Q) :
    0 < direction w Qhat := by
  have h := A1_direction_transfer w Qhat Q eps hSup heps
  have hl := (abs_le.mp h).1
  linarith

theorem A12_direction_negative
    (w Qhat Q : A → ℝ) (eps : ℝ)
    (hSup : ∀ a, |Qhat a - Q a| ≤ eps) (heps : 0 ≤ eps)
    (hmargin : direction w Q < -((Finset.univ.sum fun a ↦ |w a|) * eps)) :
    direction w Qhat < 0 := by
  have h := A1_direction_transfer w Qhat Q eps hSup heps
  have hu := (abs_le.mp h).2
  linarith

theorem A12_direction_sign_stable
    (w Qhat Q : A → ℝ) (eps : ℝ)
    (hSup : ∀ a, |Qhat a - Q a| ≤ eps) (heps : 0 ≤ eps)
    (hmargin : (Finset.univ.sum fun a ↦ |w a|) * eps < |direction w Q|) :
    (0 < direction w Q ∧ 0 < direction w Qhat) ∨
      (direction w Q < 0 ∧ direction w Qhat < 0) := by
  rcases abs_cases (direction w Q) with ⟨habs, hnonneg⟩ | ⟨habs, hneg⟩
  · left
    rw [habs] at hmargin
    have herrnonneg : 0 ≤ (Finset.univ.sum fun a ↦ |w a|) * eps :=
      mul_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) heps
    have hQpos : 0 < direction w Q := lt_of_le_of_lt herrnonneg hmargin
    exact ⟨hQpos, A12_direction_positive w Qhat Q eps hSup heps hmargin⟩
  · right
    rw [habs] at hmargin
    refine ⟨hneg, A12_direction_negative w Qhat Q eps hSup heps ?_⟩
    linarith

/-! The implementation uses zero-sum contrasts.  This makes direction
invariant to the optimal additive gauge shift and improves the raw sup-norm
bound by a factor of two. -/

theorem A12_zero_sum_gauge_direction_bound
    (w Qhat Q : A → ℝ)
    (hZero : Finset.univ.sum w = 0) :
    |direction w Qhat - direction w Q| ≤
      (Finset.univ.sum fun a ↦ |w a|) * gaugeError Qhat Q := by
  let err : A → ℝ := fun a ↦ Qhat a - Q a
  rcases (GQ_exact_gauge_identity Qhat Q).1 with ⟨c, hc⟩
  have hdiff : direction w Qhat - direction w Q =
      Finset.univ.sum (fun a ↦ w a * (err a - c)) := by
    have hbase : direction w Qhat - direction w Q =
        Finset.univ.sum (fun a ↦ w a * err a) := by
      simp only [direction, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      dsimp [err]
      ring
    rw [hbase]
    calc
      Finset.univ.sum (fun a ↦ w a * err a) =
          Finset.univ.sum (fun a ↦ w a * (err a - c)) +
            Finset.univ.sum (fun a ↦ w a * c) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = Finset.univ.sum (fun a ↦ w a * (err a - c)) +
            (Finset.univ.sum w) * c := by rw [Finset.sum_mul]
      _ = Finset.univ.sum (fun a ↦ w a * (err a - c)) := by simp [hZero]
  rw [hdiff]
  calc
    |Finset.univ.sum (fun a ↦ w a * (err a - c))| ≤
        Finset.univ.sum (fun a ↦ |w a * (err a - c)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun a ↦ |w a| * |err a - c|) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul]
    _ ≤ Finset.univ.sum (fun a ↦ |w a| * gaugeError Qhat Q) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hc a) (abs_nonneg _)
    _ = (Finset.univ.sum fun a ↦ |w a|) * gaugeError Qhat Q := by
      rw [Finset.sum_mul]

noncomputable def lambdaD (w Qhat Q : A → ℝ) : ℝ :=
  ((Finset.univ.sum fun a ↦ |w a|) * gaugeError Qhat Q) /
    |direction w Q|

theorem A12_zero_sum_gauge_sign_stable
    (w Qhat Q : A → ℝ)
    (hZero : Finset.univ.sum w = 0)
    (hmargin :
      (Finset.univ.sum fun a ↦ |w a|) * gaugeError Qhat Q <
        |direction w Q|) :
    (0 < direction w Q ∧ 0 < direction w Qhat) ∨
      (direction w Q < 0 ∧ direction w Qhat < 0) := by
  have herr := A12_zero_sum_gauge_direction_bound w Qhat Q hZero
  have hgauge : 0 ≤ gaugeError Qhat Q := by
    exact div_nonneg (osc_nonneg _) (by norm_num)
  have hbound : 0 ≤
      (Finset.univ.sum fun a ↦ |w a|) * gaugeError Qhat Q :=
    mul_nonneg (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hgauge
  rcases abs_cases (direction w Q) with ⟨habs, hnonneg⟩ | ⟨habs, hneg⟩
  · left
    rw [habs] at hmargin
    have hQpos : 0 < direction w Q := lt_of_le_of_lt hbound hmargin
    have hl := (abs_le.mp herr).1
    exact ⟨hQpos, by linarith⟩
  · right
    rw [habs] at hmargin
    have hu := (abs_le.mp herr).2
    exact ⟨hneg, by linarith⟩

theorem A12_lambdaD_lt_one_sign_stable
    (w Qhat Q : A → ℝ)
    (hZero : Finset.univ.sum w = 0)
    (hD : direction w Q ≠ 0)
    (hPhase : lambdaD w Qhat Q < 1) :
    (0 < direction w Q ∧ 0 < direction w Qhat) ∨
      (direction w Q < 0 ∧ direction w Qhat < 0) := by
  have hDabs : 0 < |direction w Q| := abs_pos.mpr hD
  have hmargin :
      (Finset.univ.sum fun a ↦ |w a|) * gaugeError Qhat Q <
        |direction w Q| := by
    apply (div_lt_one hDabs).mp
    exact hPhase
  exact A12_zero_sum_gauge_sign_stable w Qhat Q hZero hmargin

/-! ## Sharpness and tie boundaries -/

noncomputable def sharpQ (g : ℝ) (a : Fin 2) : ℝ :=
  if a = 0 then 0 else g

noncomputable def sharpQhat (g t : ℝ) (a : Fin 2) : ℝ :=
  if a = 0 then t else g - t

theorem sharpGauge_exact (g t : ℝ) (ht : 0 ≤ t) :
    gaugeError (sharpQhat g t) (sharpQ g) = t := by
  simp [gaugeError, osc, maxVal_fin2, minVal_fin2, sharpQhat, sharpQ,
    max_eq_left (by linarith : -t ≤ t), min_eq_right (by linarith : -t ≤ t)]

theorem A13_lambdaC_half_worst_case_sharp
    (g epsilon : ℝ) (hg : 0 < g) (hepsilon : g / 2 < epsilon) :
    ∃ Qhat : Fin 2 → ℝ,
      gaugeError Qhat (sharpQ g) < epsilon ∧
      sharpQ g 0 < sharpQ g 1 ∧
      Qhat 1 < Qhat 0 := by
  let t : ℝ := (g / 2 + epsilon) / 2
  have htLower : g / 2 < t := by dsimp [t]; linarith
  have htUpper : t < epsilon := by dsimp [t]; linarith
  have ht : 0 ≤ t := by linarith
  refine ⟨sharpQhat g t, ?_, ?_, ?_⟩
  · rw [sharpGauge_exact g t ht]
    exact htUpper
  · simp [sharpQ]
    exact hg
  · simp [sharpQhat]
    linarith

noncomputable def tiedQ (_a : Fin 2) : ℝ := 0

noncomputable def breakActionTie (t : ℝ) (a : Fin 2) : ℝ :=
  if a = 0 then 0 else t

theorem A14_within_relation_tie_no_positive_radius
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Qhat : Fin 2 → ℝ,
      gaugeError Qhat tiedQ < epsilon ∧
      tiedQ 0 = tiedQ 1 ∧
      Qhat 0 < Qhat 1 := by
  let t : ℝ := epsilon
  refine ⟨breakActionTie t, ?_, rfl, ?_⟩
  · simp [gaugeError, osc, maxVal_fin2, minVal_fin2, breakActionTie, tiedQ,
      max_eq_right (show (0 : ℝ) ≤ t by dsimp [t]; linarith),
      min_eq_left (show (0 : ℝ) ≤ t by dsimp [t]; linarith)]
    dsimp [t]
    linarith
  · simp [breakActionTie, t]
    exact hepsilon

noncomputable def tiedRelationScore (_r : Fin 2) : ℝ := 1

noncomputable def breakRelationTie (t : ℝ) (r : Fin 2) : ℝ :=
  if r = 0 then 1 else 1 + t

theorem A14_between_relation_tie_no_top1_radius
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ Chat : Fin 2 → ℝ,
      (∀ r, |Chat r - tiedRelationScore r| < epsilon) ∧
      tiedRelationScore 0 = tiedRelationScore 1 ∧
      StrictTopK Chat {1} 1 := by
  let t : ℝ := epsilon / 2
  refine ⟨breakRelationTie t, ?_, rfl, ?_⟩
  · intro r
    fin_cases r
    · simp [breakRelationTie, tiedRelationScore]
      exact hepsilon
    · simp [breakRelationTie, tiedRelationScore,
        abs_of_pos (show 0 < t by dsimp [t]; linarith)]
      dsimp [t]
      linarith
  · constructor
    · decide
    · intro j hj l hl
      fin_cases j <;> fin_cases l <;>
        simp_all [breakRelationTie, t] <;> linarith

end CIGAMF.V6.FunctionalRanking
