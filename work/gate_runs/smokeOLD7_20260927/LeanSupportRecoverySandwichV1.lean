import Mathlib

/-! # Support: the pointwise sandwich that separates SAFE DECISION from FULL RECOVERY.

`scripts/P2_support_exponent_law.py` shows that with `K` classes, class `i` holding
`a_i` safe and `b_i` unsafe tips each observed with probability `p_i`,

  deciding safely   `R_N^*      = Theta((1 - sum_i p_i)^N)`
  recovering all    `R_{N,rec}^*= Theta((1 - min_i p_i)^N)`,

with both prefactors pinned by finite-`N` two-sided brackets.  The recovery side runs
on the exact Bayes loss at an unseen-count vector `L`,

  `loss L = 1 - prod_i (choose (a_i + L_i) L_i)⁻¹`,

and the ONLY facts about that loss the brackets use are the two pointwise
inequalities proved here.  Proving them is what turns the two exponents from a
fitted slope into a consequence: the upper bound gives
`R_rec ≤ sum_i P(L_i ≥ 1) ≤ sum_i b_i (1-p_i)^N`, and the lower bound gives
`R_rec ≥ (a_{i₀}/(a_{i₀}+1)) P(L_{i₀} ≥ 1)`, whose exponents are both
`-log(1 - p_{i₀})`.

## WHAT IS PROVED

* `one_sub_prod_le_sum` — `1 - ∏ x ≤ ∑ (1 - x)` for `x i ∈ [0,1]` (union bound).
* `single_le_one_sub_prod` — `1 - x i₀ ≤ 1 - ∏ x`: one class failing already costs.
* `succ_le_choose` — `a + 1 ≤ choose (a + L) L` whenever `1 ≤ L`, by Pascal.
* `loss_lower` — hence `a_{i₀}/(a_{i₀}+1) ≤ loss L` as soon as `1 ≤ L i₀`: leaving a
  single unsafe tip unseen in ONE class already costs a constant.
* `loss_upper` — and `loss L ≤ ∑ i, (1 - (choose (a i + L i) (L i))⁻¹)`, each term
  vanishing when that class is fully seen.
* `recovery_sandwich` — the two together.

## WHAT THIS DOES NOT ESTABLISH

- Nothing here is about the DISTRIBUTION of `L`: the inclusion-exclusion joint law,
  the Bonferroni brackets for `P(L_i = 1)` and the resulting exponents live in the
  script.  This file proves the pointwise loss inequalities those brackets consume.
- That `loss` IS the Bayes recovery error is cross-checked against ordered-transcript
  enumeration in the script, not here.
- The decide-side law `E min_i L_i/(a_i + L_i)` and its minimax status are
  `LeanSupportBayesMinimaxV1`; they are not restated.
-/

namespace CIGAMF.P13.SupportRecoverySandwich

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Union bound: `1 - ∏ x ≤ ∑ (1 - x)` for factors in `[0,1]`. -/
theorem one_sub_prod_le_sum (s : Finset I) (x : I → ℝ)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    1 - ∏ i ∈ s, x i ≤ ∑ i ∈ s, (1 - x i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hp : (0:ℝ) ≤ ∏ i ∈ t, x i := Finset.prod_nonneg fun i _ => h0 i
    have hp1 : ∏ i ∈ t, x i ≤ 1 :=
      Finset.prod_le_one (fun i _ => h0 i) (fun i _ => h1 i)
    have key : (0:ℝ) ≤ (1 - x a) * (1 - ∏ i ∈ t, x i) :=
      mul_nonneg (by linarith [h1 a]) (by linarith)
    nlinarith [ih]

/-- One factor already bounds the loss from below. -/
theorem single_le_one_sub_prod (s : Finset I) (x : I → ℝ) (i₀ : I) (hi₀ : i₀ ∈ s)
    (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1) :
    1 - x i₀ ≤ 1 - ∏ i ∈ s, x i := by
  classical
  have hsplit : ∏ i ∈ s, x i = x i₀ * ∏ i ∈ s.erase i₀, x i :=
    (Finset.mul_prod_erase s x hi₀).symm
  have hp1 : ∏ i ∈ s.erase i₀, x i ≤ 1 :=
    Finset.prod_le_one (fun i _ => h0 i) (fun i _ => h1 i)
  have hp0 : (0:ℝ) ≤ ∏ i ∈ s.erase i₀, x i :=
    Finset.prod_nonneg fun i _ => h0 i
  have : ∏ i ∈ s, x i ≤ x i₀ := by
    rw [hsplit]
    nlinarith [h0 i₀]
  linarith

/-- `a + 1 ≤ choose (a + L) L` for `1 ≤ L`, by Pascal's rule. -/
theorem succ_le_choose (a : ℕ) : ∀ L : ℕ, 1 ≤ L → a + 1 ≤ Nat.choose (a + L) L := by
  intro L
  induction L with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
      intro _
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp [Nat.choose_one_right]
      · have h1 : a + 1 ≤ Nat.choose (a + n) n := ih hn
        have hre : a + (n + 1) = (a + n) + 1 := by omega
        rw [hre, Nat.choose_succ_succ]
        omega

/-- Leaving one unsafe tip unseen in class `i₀` already costs `a/(a+1)`. -/
theorem one_sub_inv_choose_ge (a L : ℕ) (hL : 1 ≤ L) :
    (a : ℝ) / (a + 1) ≤ 1 - ((Nat.choose (a + L) L : ℝ))⁻¹ := by
  have hc : (a : ℝ) + 1 ≤ (Nat.choose (a + L) L : ℝ) := by
    exact_mod_cast succ_le_choose a L hL
  have hpos : (0:ℝ) < (a : ℝ) + 1 := by positivity
  have hcpos : (0:ℝ) < (Nat.choose (a + L) L : ℝ) := lt_of_lt_of_le hpos hc
  have hinv : ((Nat.choose (a + L) L : ℝ))⁻¹ * ((a : ℝ) + 1) ≤ 1 := by
    have h2 : ((Nat.choose (a + L) L : ℝ))⁻¹ * ((a : ℝ) + 1)
        ≤ ((Nat.choose (a + L) L : ℝ))⁻¹ * (Nat.choose (a + L) L : ℝ) :=
      mul_le_mul_of_nonneg_left hc (le_of_lt (inv_pos.mpr hcpos))
    rwa [inv_mul_cancel₀ (ne_of_gt hcpos)] at h2
  rw [div_le_iff₀ hpos]
  nlinarith [hinv]

/-- The Bayes recovery loss at an unseen-count vector. -/
noncomputable def loss (a L : I → ℕ) : ℝ :=
  1 - ∏ i, ((Nat.choose (a i + L i) (L i) : ℝ))⁻¹

theorem inv_choose_le_one (a L : ℕ) :
    ((Nat.choose (a + L) L : ℝ))⁻¹ ≤ 1 := by
  have hp : 0 < Nat.choose (a + L) L := Nat.choose_pos (by omega)
  have h1 : (1:ℝ) ≤ (Nat.choose (a + L) L : ℝ) := by exact_mod_cast hp
  have hpos : (0:ℝ) < (Nat.choose (a + L) L : ℝ) := lt_of_lt_of_le zero_lt_one h1
  have h2 : ((Nat.choose (a + L) L : ℝ))⁻¹ * 1
      ≤ ((Nat.choose (a + L) L : ℝ))⁻¹ * (Nat.choose (a + L) L : ℝ) :=
    mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hpos))
  rw [inv_mul_cancel₀ (ne_of_gt hpos), mul_one] at h2
  exact h2

theorem loss_upper (a L : I → ℕ) :
    loss a L ≤ ∑ i, (1 - ((Nat.choose (a i + L i) (L i) : ℝ))⁻¹) := by
  unfold loss
  refine one_sub_prod_le_sum _ _ (fun i => ?_) (fun i => ?_)
  · positivity
  · exact inv_choose_le_one (a i) (L i)

theorem loss_lower (a L : I → ℕ) (i₀ : I) (hL : 1 ≤ L i₀) :
    (a i₀ : ℝ) / (a i₀ + 1) ≤ loss a L := by
  unfold loss
  have step : 1 - ((Nat.choose (a i₀ + L i₀) (L i₀) : ℝ))⁻¹
      ≤ 1 - ∏ i, ((Nat.choose (a i + L i) (L i) : ℝ))⁻¹ :=
    single_le_one_sub_prod (univ : Finset I)
      (fun i => ((Nat.choose (a i + L i) (L i) : ℝ))⁻¹) i₀ (mem_univ i₀)
      (fun i => by positivity) (fun i => inv_choose_le_one (a i) (L i))
  exact le_trans (one_sub_inv_choose_ge (a i₀) (L i₀) hL) step

/-- THE SANDWICH the two exponents are read off. -/
theorem recovery_sandwich (a L : I → ℕ) (i₀ : I) (hL : 1 ≤ L i₀) :
    (a i₀ : ℝ) / (a i₀ + 1) ≤ loss a L
      ∧ loss a L ≤ ∑ i, (1 - ((Nat.choose (a i + L i) (L i) : ℝ))⁻¹) :=
  ⟨loss_lower a L i₀ hL, loss_upper a L⟩

#print axioms one_sub_prod_le_sum
#print axioms single_le_one_sub_prod
#print axioms succ_le_choose
#print axioms one_sub_inv_choose_ge
#print axioms inv_choose_le_one
#print axioms loss_upper
#print axioms loss_lower
#print axioms recovery_sandwich

end CIGAMF.P13.SupportRecoverySandwich
