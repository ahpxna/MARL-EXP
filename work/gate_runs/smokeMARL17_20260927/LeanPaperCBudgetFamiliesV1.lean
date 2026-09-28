import «LeanPaperCBudgetAwareV1»
import «LeanPaperCRelaxedJoinV1»
import «LeanPaperCStabilityFamilyV1»
import «LeanPaperCOddFrontierV1»

/-!
# Paper C: the value of knowing the budget, and one exchange, on two families

**The four-item family** `g = (a, -a, b, -b)`, `0 < b < a`, `c = (a-b)/(2(a+b))`.
* `aware_twoMag`: `B(η) = c · max((1-η)/2, 0)`.
  - At budgets `1` and `3` the band forces mass `(1-η)/2` on the heavy items, each costing `c`
    (a linear certificate); the law `((1-η)/4, (1-η)/4, (1+η)/4, (1+η)/4)` meets it.
  - At budget `2` the two cancelling pairs, each with probability `1/2`, cost nothing at
    `η = 0`.
* `advantage_*`: with `U(η) = c · max((1-η)/2, 1/3)` (`twoMag_frontier`), the value of knowing
  the budget `A = U - B` is `0` on `[0, 1/3]`, `c(η - 1/3)/2` on `[1/3, 1]`, and `c/3` beyond.
* `recourse_one_twoMag`: **one exchange reaches it**, `V^{(1)}(η) = B(η)` for every `η ≥ 0`. The
  base law is uniform on the four cyclic orders (band `0`). At budgets `1, 3` any two sets differ
  by one item. At budget `2` a mixed prefix is sent to a uniformly chosen cancelling pair by one
  exchange; a cancelling prefix is kept.
* `recourse_zero_twoMag`, `exchange_needed`: `V^{(0)} = U`, so an exchange is needed exactly when
  `η > 1/3`.

**The family `g_m`** (`D = m + 4`).
* `aware_even`: for even `m ≥ 4` and `0 ≤ η ≤ (m-2)/(2(m-1))`,
  `B(η) = U(η) = 4(1-η)/(mD)`. The budget-one layer alone forces the universal value.
* `aware_odd`: for odd `m ≥ 3` and `0 ≤ η ≤ 1 - 2/(m(m-1))`,
  `B(η) = U(η) = (m+3-(m+1)η)/(mD)`. The budget-`(m-1)` layer alone forces it.
So on these ranges **knowing the budget in advance is worth nothing**.
-/

namespace CIGAMF.P13.PaperCBudgetFamilies

open Finset
open CIGAMF.P13.PaperCValueSet CIGAMF.P13.PaperCEndpoint CIGAMF.P13.PaperCFrontier
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.PaperCLawPush CIGAMF.P13.PaperCBudgetAware
open CIGAMF.P13.PaperCTwoMagFour

/-! ## 1. Point-mass subset laws and kernel plans -/

section Tools

variable {m : ℕ}

/-- A finite mixture of point masses on subsets. -/
noncomputable def ptLaw {n : ℕ} (T : Fin n → Finset (Fin m)) (w : Fin n → ℝ) :
    Finset (Fin m) → ℝ :=
  fun S => ∑ j, w j * (if T j = S then 1 else 0)

theorem ptLaw_sum {n : ℕ} (T : Fin n → Finset (Fin m)) (w : Fin n → ℝ)
    (f : Finset (Fin m) → ℝ) : ∑ S, ptLaw T w S * f S = ∑ j, w j * f (T j) := by
  unfold ptLaw
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [ite_mul]

theorem ptLaw_feasible {n : ℕ} (T : Fin n → Finset (Fin m)) (w : Fin n → ℝ) (k : ℕ) (η : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hT : ∀ j, (T j).card = k)
    (hband : ∀ i, |∑ j, w j * ind i (T j) - (k : ℝ) / m| ≤ η / m) :
    ptLaw T w ∈ SubFeasible k η := by
  refine ⟨fun S => Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (by split_ifs <;> norm_num),
    ?_, ?_, fun i => ?_⟩
  · have := ptLaw_sum T w (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hw1]
  · intro S hS
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
    have : T j = S := by
      by_contra h; apply hj; rw [if_neg h, mul_zero]
    rw [← this, hT j]
  · rw [ptLaw_sum]; exact hband i

/-- The plan that edits the prefix through a kernel `Kf(prefix, final)`. -/
noncomputable def kerPlan (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1))
    (Kf : Finset (Fin m) → Finset (Fin m) → ℝ) : Equiv.Perm (Fin m) → Finset (Fin m) → ℝ :=
  fun σ T => P σ * Kf (prefixSet σ k) T

theorem kerPlan_feasible (P : Equiv.Perm (Fin m) → ℝ) (η : ℝ)
    (hP : P ∈ FeasibleAt (id : Equiv.Perm (Fin m) → _) η) (k : Fin (m + 1)) (R : ℕ)
    (Kf : Finset (Fin m) → Finset (Fin m) → ℝ) (hK0 : ∀ S T, 0 ≤ Kf S T)
    (hK1 : ∀ S, ∑ T, Kf S T = 1)
    (hKs : ∀ S T, S.card = k.val → Kf S T ≠ 0 → T.card = k.val ∧ (S \ T).card ≤ R)
    (hband : ∀ i, |∑ σ, P σ * ∑ T, Kf (prefixSet σ k) T * ind i T - (k.val : ℝ) / m|
      ≤ η / m) :
    kerPlan P k Kf ∈ PlanFeasible P k R η := by
  refine ⟨fun σ T => mul_nonneg (hP.1 σ) (hK0 _ _), fun σ => ?_, fun σ T h => ?_, fun i => ?_⟩
  · unfold kerPlan; rw [← Finset.mul_sum, hK1, mul_one]
  · have hK : Kf (prefixSet σ k) T ≠ 0 := fun h0 => h (by unfold kerPlan; rw [h0, mul_zero])
    exact hKs _ T (prefixSet_card σ k) hK
  · have e : ∑ σ, ∑ T, kerPlan P k Kf σ T * ind i T
        = ∑ σ, P σ * ∑ T, Kf (prefixSet σ k) T * ind i T := by
      unfold kerPlan
      simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [e]; exact hband i

theorem kerPlan_cost (g : Fin m → ℝ) (P : Equiv.Perm (Fin m) → ℝ) (k : Fin (m + 1))
    (Kf : Finset (Fin m) → Finset (Fin m) → ℝ) :
    planCost g k (kerPlan P k Kf) = ∑ σ, P σ * ∑ T, Kf (prefixSet σ k) T * subCost g k T := by
  unfold planCost kerPlan
  simp_rw [mul_assoc, ← Finset.mul_sum]

end Tools

/-! ## 2. The four-item family: the budget-aware value -/

section Four

variable {a b : ℝ}

/-- The normalised cost unit `c = (a-b)/(2(a+b))`. -/
noncomputable def cU (a b : ℝ) : ℝ := (a - b) / (2 * (a + b))

theorem sc1 (hb : 0 < b) (hab : b < a) (j : Fin 4) :
    subCost (g4 a b) 1 {j} = (|g4 a b j| - b) / (2 * (a + b)) := by
  unfold subCost; rw [Finset.sum_singleton, base_one hb hab, normMass_g4 hb hab]

theorem sc3 (hb : 0 < b) (hab : b < a) (j : Fin 4) :
    subCost (g4 a b) 3 {j}ᶜ = (|g4 a b j| - b) / (2 * (a + b)) := by
  unfold subCost; rw [sum_compl_single, abs_neg, base_three hb hab, normMass_g4 hb hab]

theorem sc2_a : subCost (g4 a b) 2 {0, 1} = 0 := by
  unfold subCost; rw [base_two]; simp [g4]

theorem sc2_b : subCost (g4 a b) 2 {2, 3} = 0 := by
  unfold subCost; rw [base_two]; simp [g4]

/-- The heavy weight of the budget-one law. -/
noncomputable def hW (η : ℝ) : ℝ := max (1 - η) 0 / 4

theorem hW_facts (η : ℝ) (hη : 0 ≤ η) : 0 ≤ hW η ∧ hW η ≤ 1 / 4 ∧ 1 / 4 - hW η ≤ η / 4 := by
  unfold hW
  have h1 : 1 - η ≤ max (1 - η) 0 := le_max_left _ _
  have h2 : 0 ≤ max (1 - η) 0 := le_max_right _ _
  have h3 : max (1 - η) 0 ≤ 1 := max_le (by linarith) (by norm_num)
  refine ⟨by positivity, by linarith, by linarith⟩

/-- The singleton law at budget one. -/
noncomputable def T1 : Fin 4 → Finset (Fin 4) := ![{0}, {1}, {2}, {3}]
/-- The complement law at budget three. -/
noncomputable def T3 : Fin 4 → Finset (Fin 4) := ![{0}ᶜ, {1}ᶜ, {2}ᶜ, {3}ᶜ]
/-- The cancelling pairs at budget two. -/
noncomputable def T2 : Fin 2 → Finset (Fin 4) := ![{0, 1}, {2, 3}]

noncomputable def w1 (η : ℝ) : Fin 4 → ℝ := ![hW η, hW η, 1 / 2 - hW η, 1 / 2 - hW η]
noncomputable def w2 : Fin 2 → ℝ := ![1 / 2, 1 / 2]

theorem w1_nonneg (η : ℝ) (hη : 0 ≤ η) (j : Fin 4) : 0 ≤ w1 η j := by
  obtain ⟨h0, h1, -⟩ := hW_facts η hη
  fin_cases j <;> simp [w1] <;> linarith

theorem w1_sum (η : ℝ) : ∑ j, w1 η j = 1 := by
  simp [w1, Fin.sum_univ_four]; ring

theorem Q1_feasible (η : ℝ) (hη : 0 ≤ η) : ptLaw T1 (w1 η) ∈ SubFeasible 1 η := by
  obtain ⟨h0, h1, h2⟩ := hW_facts η hη
  refine ptLaw_feasible T1 (w1 η) 1 η (w1_nonneg η hη) (w1_sum η)
    (fun j => by fin_cases j <;> rfl) fun i => ?_
  fin_cases i <;> simp [ind, T1, w1, Fin.sum_univ_four] <;> rw [abs_le] <;>
    constructor <;> linarith

theorem Q3_feasible (η : ℝ) (hη : 0 ≤ η) : ptLaw T3 (w1 η) ∈ SubFeasible 3 η := by
  obtain ⟨h0, h1, h2⟩ := hW_facts η hη
  refine ptLaw_feasible T3 (w1 η) 3 η (w1_nonneg η hη) (w1_sum η)
    (fun j => by fin_cases j <;> rfl) fun i => ?_
  fin_cases i <;> simp [ind, T3, w1, Fin.sum_univ_four] <;> rw [abs_le] <;>
    constructor <;> linarith

theorem Q2_feasible (η : ℝ) (hη : 0 ≤ η) : ptLaw T2 w2 ∈ SubFeasible 2 η := by
  refine ptLaw_feasible T2 w2 2 η (fun j => by fin_cases j <;> simp [w2])
    (by simp [w2, Fin.sum_univ_two]; norm_num) (fun j => by fin_cases j <;> rfl) fun i => ?_
  fin_cases i <;> simp [ind, T2, w2, Fin.sum_univ_two] <;> norm_num <;> positivity

theorem max_half (η : ℝ) : max ((1 - η) / 2) 0 = max (1 - η) 0 / 2 := by
  rw [← max_div_div_right (by norm_num : (0 : ℝ) ≤ 2), zero_div]

theorem Q1_cost (hb : 0 < b) (hab : b < a) (η : ℝ) :
    ∑ S, ptLaw T1 (w1 η) S * subCost (g4 a b) 1 S = cU a b * max ((1 - η) / 2) 0 := by
  have ha : 0 < a := hb.trans hab
  rw [ptLaw_sum, max_half, Fin.sum_univ_four]
  have e0 : T1 0 = {0} := rfl
  have e1 : T1 1 = {1} := rfl
  have e2 : T1 2 = {2} := rfl
  have e3 : T1 3 = {3} := rfl
  have f0 : w1 η 0 = hW η := rfl
  have f1 : w1 η 1 = hW η := rfl
  have f2 : w1 η 2 = 1 / 2 - hW η := rfl
  have f3 : w1 η 3 = 1 / 2 - hW η := rfl
  rw [e0, e1, e2, e3, f0, f1, f2, f3, sc1 hb hab, sc1 hb hab, sc1 hb hab, sc1 hb hab]
  simp [g4, abs_of_pos ha, abs_of_pos hb, cU, hW]
  ring

theorem Q3_cost (hb : 0 < b) (hab : b < a) (η : ℝ) :
    ∑ S, ptLaw T3 (w1 η) S * subCost (g4 a b) 3 S = cU a b * max ((1 - η) / 2) 0 := by
  have ha : 0 < a := hb.trans hab
  rw [ptLaw_sum, max_half, Fin.sum_univ_four]
  have e0 : T3 0 = {0}ᶜ := rfl
  have e1 : T3 1 = {1}ᶜ := rfl
  have e2 : T3 2 = {2}ᶜ := rfl
  have e3 : T3 3 = {3}ᶜ := rfl
  have f0 : w1 η 0 = hW η := rfl
  have f1 : w1 η 1 = hW η := rfl
  have f2 : w1 η 2 = 1 / 2 - hW η := rfl
  have f3 : w1 η 3 = 1 / 2 - hW η := rfl
  rw [e0, e1, e2, e3, f0, f1, f2, f3, sc3 hb hab, sc3 hb hab, sc3 hb hab, sc3 hb hab]
  simp [g4, abs_of_pos ha, abs_of_pos hb, cU, hW]
  ring

theorem Q2_cost : ∑ S, ptLaw T2 w2 S * subCost (g4 a b) 2 S = 0 := by
  rw [ptLaw_sum]
  simp [Fin.sum_univ_two, T2, w2, sc2_a, sc2_b]

theorem cU_nonneg (hb : 0 < b) (hab : b < a) : 0 ≤ cU a b :=
  div_nonneg (by linarith) (by linarith)

/-- **The budget-one layer**: `c(1-η)/2` from the linear certificate on the heavy items. -/
theorem lay1_lower (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) :
    cU a b * max ((1 - η) / 2) 0 ≤ layerValue (g4 a b) η 1 := by
  have ha : 0 < a := hb.trans hab
  rw [mul_max_of_nonneg _ _ (cU_nonneg hb hab), mul_zero]
  refine max_le ?_ (layer_nonneg _ η 1 (sub_nonempty η hη 1))
  have hD : 0 < normMass (g4 a b) := by rw [normMass_g4 hb hab]; linarith
  have h := layer_ge_of_linear (g4 a b) η 1 (sub_nonempty η hη 1) hD 0 ![a - b, a - b, 0, 0]
    (by
      intro S hS
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hS
      rw [Finset.sum_singleton, Finset.sum_singleton, base_one hb hab]
      fin_cases j <;> simp [g4, abs_of_pos ha, abs_of_pos hb])
  refine le_trans (le_of_eq ?_) h
  rw [normMass_g4 hb hab]
  simp [Fin.sum_univ_four, abs_of_pos (sub_pos.mpr hab), cU]
  field_simp
  ring

/-- **The budget-aware value of the four-item family.** -/
theorem aware_twoMag (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) :
    awareValue (g4 a b) η K3 K3_ne = cU a b * max ((1 - η) / 2) 0 := by
  have hc := cU_nonneg hb hab
  have hM : 0 ≤ cU a b * max ((1 - η) / 2) 0 := mul_nonneg hc (le_max_right _ _)
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun k hk => ?_
    simp only [K3, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact (layer_le _ η 1 _ (Q1_feasible η hη)).trans (le_of_eq (Q1_cost hb hab η))
    · exact (layer_le _ η 2 _ (Q2_feasible η hη)).trans (by rw [Q2_cost]; exact hM)
    · exact (layer_le _ η 3 _ (Q3_feasible η hη)).trans (le_of_eq (Q3_cost hb hab η))
  · exact (lay1_lower hb hab η hη).trans
      (Finset.le_sup' (fun k => layerValue (g4 a b) η k) (by simp [K3]))

/-- **The value of knowing the budget**, `A = U - B`. -/
theorem advantage_twoMag (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) :
    trueValue (g4 a b) η K3 K3_ne - awareValue (g4 a b) η K3 K3_ne
      = cU a b * (max ((1 - η) / 2) (1 / 3) - max ((1 - η) / 2) 0) := by
  rw [twoMag_frontier hb hab η hη, aware_twoMag hb hab η hη, cU]; ring

theorem advantage_zero (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) (h3 : η ≤ 1 / 3) :
    trueValue (g4 a b) η K3 K3_ne = awareValue (g4 a b) η K3 K3_ne := by
  have := advantage_twoMag hb hab η hη
  rw [max_eq_left (by linarith : (1 : ℝ) / 3 ≤ (1 - η) / 2),
    max_eq_left (by linarith : (0 : ℝ) ≤ (1 - η) / 2), sub_self, mul_zero] at this
  linarith

theorem advantage_mid (hb : 0 < b) (hab : b < a) (η : ℝ) (h3 : 1 / 3 ≤ η) (h1 : η ≤ 1) :
    trueValue (g4 a b) η K3 K3_ne - awareValue (g4 a b) η K3 K3_ne
      = cU a b * (η - 1 / 3) / 2 := by
  rw [advantage_twoMag hb hab η (by linarith),
    max_eq_right (by linarith : (1 - η) / 2 ≤ 1 / 3),
    max_eq_left (by linarith : (0 : ℝ) ≤ (1 - η) / 2)]
  ring

theorem advantage_top (hb : 0 < b) (hab : b < a) (η : ℝ) (h1 : 1 ≤ η) :
    trueValue (g4 a b) η K3 K3_ne - awareValue (g4 a b) η K3 K3_ne = cU a b / 3 := by
  rw [advantage_twoMag hb hab η (by linarith),
    max_eq_right (by linarith : (1 - η) / 2 ≤ 1 / 3),
    max_eq_right (by linarith : (1 - η) / 2 ≤ 0)]
  ring

/-! ## 3. The four-item family: one exchange -/

/-- The base law: uniform on the four cyclic orders. -/
noncomputable def P0 : Equiv.Perm (Fin 4) → ℝ := pushLaw (cyclicPerm 4) (cyclicLaw 4)

theorem P0_feasible (η : ℝ) (hη : 0 ≤ η) : P0 ∈ FeasibleAt (id : Equiv.Perm (Fin 4) → _) η :=
  feasible_mono id 0 η (by norm_num) hη (feasible_push _ _ 0 (feasible_zero_nonempty 4))

theorem P0_expect (v : Equiv.Perm (Fin 4) → ℝ) :
    ∑ σ, P0 σ * v σ = (v (cyclicPerm 4 0) + v (cyclicPerm 4 1) + v (cyclicPerm 4 2)
      + v (cyclicPerm 4 3)) / 4 := by
  unfold P0
  rw [pushLaw_expect]
  simp [Fin.sum_univ_four, cyclicLaw]
  ring

theorem pre0 : prefixSet (cyclicPerm 4 0) 2 = {0, 1} := by decide
theorem pre1 : prefixSet (cyclicPerm 4 1) 2 = {1, 2} := by decide
theorem pre2 : prefixSet (cyclicPerm 4 2) 2 = {2, 3} := by decide
theorem pre3 : prefixSet (cyclicPerm 4 3) 2 = {3, 0} := by decide

/-- The budget-two edit: keep a cancelling prefix, send a mixed one to a uniformly chosen
cancelling pair. -/
noncomputable def K2 (S T : Finset (Fin 4)) : ℝ :=
  if S = {0, 1} ∨ S = {2, 3} then (if T = S then 1 else 0)
  else (if T = {0, 1} then 1 / 2 else 0) + (if T = {2, 3} then 1 / 2 else 0)

theorem K2_sum (S : Finset (Fin 4)) (f : Finset (Fin 4) → ℝ) :
    ∑ T, K2 S T * f T
      = if S = {0, 1} ∨ S = {2, 3} then f S else f {0, 1} / 2 + f {2, 3} / 2 := by
  unfold K2
  split_ifs with h
  · simp [ite_mul]
  · simp only [add_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
    simp
    ring

theorem K2_nonneg (S T : Finset (Fin 4)) : 0 ≤ K2 S T := by
  unfold K2; split_ifs <;> norm_num

theorem K2_one (S : Finset (Fin 4)) : ∑ T, K2 S T = 1 := by
  have := K2_sum S (fun _ => 1)
  simp only [mul_one] at this
  rw [this]; split_ifs <;> norm_num

theorem mixed_close : ∀ S : Finset (Fin 4), S.card = 2 → ¬ (S = {0, 1} ∨ S = {2, 3}) →
    (S \ {0, 1}).card ≤ 1 ∧ (S \ {2, 3}).card ≤ 1 := by decide

theorem K2_supp (S T : Finset (Fin 4)) (hS : S.card = 2) (h : K2 S T ≠ 0) :
    T.card = 2 ∧ (S \ T).card ≤ 1 := by
  unfold K2 at h
  by_cases hp : S = {0, 1} ∨ S = {2, 3}
  · rw [if_pos hp] at h
    by_cases hT : T = S
    · subst hT; exact ⟨hS, by simp⟩
    · rw [if_neg hT] at h; exact absurd rfl h
  · rw [if_neg hp] at h
    by_cases hT1 : T = {0, 1}
    · subst hT1; exact ⟨by decide, (mixed_close S hS hp).1⟩
    · by_cases hT2 : T = {2, 3}
      · subst hT2; exact ⟨by decide, (mixed_close S hS hp).2⟩
      · rw [if_neg hT1, if_neg hT2] at h; norm_num at h

theorem K2_band (η : ℝ) (hη : 0 ≤ η) (i : Fin 4) :
    |∑ σ, P0 σ * ∑ T, K2 (prefixSet σ 2) T * ind i T - ((2 : Fin 5).val : ℝ) / (4 : ℕ)|
      ≤ η / (4 : ℕ) := by
  rw [P0_expect]
  simp only [K2_sum, pre0, pre1, pre2, pre3]
  rw [if_pos (by decide), if_neg (by decide), if_pos (by decide), if_neg (by decide)]
  fin_cases i <;> simp [ind] <;> norm_num <;> positivity

theorem K2_cost (hb : 0 < b) (hab : b < a) :
    ∑ σ, P0 σ * ∑ T, K2 (prefixSet σ 2) T * subCost (g4 a b) 2 T = 0 := by
  rw [P0_expect]
  simp only [K2_sum, pre0, pre1, pre2, pre3]
  rw [if_pos (by decide), if_neg (by decide), if_pos (by decide), if_neg (by decide)]
  rw [sc2_a, sc2_b]; norm_num

/-- **One exchange reaches the budget-aware value**, at every band width. -/
theorem recourse_one_twoMag (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) :
    recourseValue (g4 a b) η 1 K3 K3_ne = cU a b * max ((1 - η) / 2) 0 := by
  rw [← aware_twoMag hb hab η hη]
  refine le_antisymm ?_ (aware_le_recourse _ η hη 1 K3 K3_ne)
  rw [aware_twoMag hb hab η hη]
  have hP := P0_feasible η hη
  set J : Fin 5 → Equiv.Perm (Fin 4) → Finset (Fin 4) → ℝ := fun k =>
    if k = 1 then indepPlan P0 (ptLaw T1 (w1 η))
    else if k = 2 then kerPlan P0 2 K2 else indepPlan P0 (ptLaw T3 (w1 η)) with hJdef
  have hJ1 : J 1 = indepPlan P0 (ptLaw T1 (w1 η)) := by simp [hJdef]
  have hJ2 : J 2 = kerPlan P0 2 K2 := by simp [hJdef]
  have hJ3 : J 3 = indepPlan P0 (ptLaw T3 (w1 η)) := by simp [hJdef]
  have hfeas : ∀ k ∈ K3, J k ∈ PlanFeasible P0 k 1 η := by
    intro k hk
    simp only [K3, Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · rw [hJ1]; exact indep_feasible P0 η hP 1 1 (Or.inl le_rfl) _ (Q1_feasible η hη)
    · rw [hJ2]
      exact kerPlan_feasible P0 η hP 2 1 K2 K2_nonneg K2_one
        (fun S T hS h => K2_supp S T hS h) (fun i => K2_band η hη i)
    · rw [hJ3]; exact indep_feasible P0 η hP 3 1 (Or.inr (by decide)) _ (Q3_feasible η hη)
  refine (csInf_le (recourse_bdd _ η 1 K3 K3_ne) ⟨P0, hP, J, hfeas, rfl⟩).trans ?_
  refine Finset.sup'_le _ _ fun k hk => ?_
  simp only [K3, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl
  · rw [hJ1, indep_cost _ P0 hP.2.1, Q1_cost hb hab]
  · rw [hJ2, kerPlan_cost, K2_cost hb hab]
    exact mul_nonneg (cU_nonneg hb hab) (le_max_right _ _)
  · rw [hJ3, indep_cost _ P0 hP.2.1, Q3_cost hb hab]

/-- **Without an exchange the universal value is all one gets.** -/
theorem recourse_zero_twoMag (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) :
    recourseValue (g4 a b) η 0 K3 K3_ne = cU a b * max ((1 - η) / 2) (1 / 3) := by
  rw [recourse_zero _ η hη K3 K3_ne, twoMag_frontier hb hab η hη, cU]

/-- **An exchange is needed exactly when `η > 1/3`.** -/
theorem exchange_needed (hb : 0 < b) (hab : b < a) (η : ℝ) (hη : 0 ≤ η) :
    recourseValue (g4 a b) η 1 K3 K3_ne < recourseValue (g4 a b) η 0 K3 K3_ne ↔ 1 / 3 < η := by
  rw [recourse_one_twoMag hb hab η hη, recourse_zero_twoMag hb hab η hη]
  have hc : 0 < cU a b := div_pos (by linarith) (by linarith)
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    rw [max_eq_left (by linarith : (1 : ℝ) / 3 ≤ (1 - η) / 2),
      max_eq_left (by linarith : (0 : ℝ) ≤ (1 - η) / 2)] at h
    exact lt_irrefl _ h
  · intro h
    refine mul_lt_mul_of_pos_left ?_ hc
    rcases le_total η 1 with h1 | h1
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ (1 - η) / 2),
        max_eq_right (by linarith : (1 - η) / 2 ≤ 1 / 3)]
      linarith
    · rw [max_eq_right (by linarith : (1 - η) / 2 ≤ 0),
        max_eq_right (by linarith : (1 - η) / 2 ≤ 1 / 3)]
      norm_num

end Four

#print axioms aware_twoMag
#print axioms advantage_twoMag
#print axioms advantage_zero
#print axioms advantage_mid
#print axioms advantage_top
#print axioms recourse_one_twoMag
#print axioms recourse_zero_twoMag
#print axioms exchange_needed

end CIGAMF.P13.PaperCBudgetFamilies
