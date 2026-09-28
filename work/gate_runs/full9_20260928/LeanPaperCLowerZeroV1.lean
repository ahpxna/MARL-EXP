import «LeanPaperCValueSetV1»

/-!
# Paper C: the matching lower bound at uniform marginals

C-H1 says "the EXACT value at uniform marginals".  Checking the corpus for the even side,
only the upper bound was there: `evenMixture_value_at_D` gives a law of value `4/(m(m+4))`
and `LeanPaperCUniformV1` now shows it is feasible at `eta = 0`.  The only lower bound in
the corpus for even `m` is `O2_even_at_ranking_law`, which produces `2/(D(m-1))` -- strictly
SMALLER than `4/(m(m+4))` by `even_tradeoff`.  So "exact" was an over-claim: an upper bound
and a weaker lower bound do not pin a value.

The matching lower bound is available and short, and it is here.  At budget `1` the prefix
holds exactly one item, so `|S_1|` is that item's own `|g_i|`.  If every item's retained
marginal at budget `1` is exactly `1/m` -- which is what `eta = 0` says -- then

    E |S_1| = sum_i |g_i| / m = (m+4)/m,

because the signed-prefix family has `sum_i |g_i| = m + 4`.  The baseline at an odd budget
is `1`, so

    E r_1 = ((m+4)/m - 1)/D = 4/(m D),

an EQUALITY, not a bound.  The objective is a maximum over budgets, so it is at least that.
With the mixture's upper bound this pins `V_m(0) = 4/(m(m+4))` at even `m`, and the claim
becomes exact rather than one-sided.

The same computation gives `E r_1 = 4/(mD)` at odd `m` too; there the maximum sits at the
last budget instead, which is why the odd value is the larger `(m+3)/(m(m+4))`.
-/

namespace CIGAMF.P13.PaperCLowerZero

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCEndpoint
open CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCValueSet

variable {R : Type*} [Fintype R] {m : ℕ}

/-- **The budget-1 prefix sum is the first item's weight.** -/
theorem regret_at_one (hm : 0 < m) (g : Ranking m) (σ : Equiv.Perm (Fin m)) (D : ℝ) :
    regret g σ D 1 = (|g (σ ⟨0, hm⟩)| - 1) / D := by
  unfold regret excess
  rw [prefixSum_one hm (rankOf g σ)]
  unfold rankOf
  norm_num

/-- **The expected budget-1 regret, at uniform marginals.**  An identity: every item is in
the prefix with probability exactly `1/m`, so the expected absolute prefix sum is the mean
of `|g|`. -/
theorem expected_regret_at_one (hm : 0 < m) (g : Ranking m) (P : R → ℝ)
    (perm : R → Equiv.Perm (Fin m)) (D : ℝ) (hD : 0 < D)
    (hsum : ∑ x, P x = 1)
    (hmarg : ∀ i, (∑ x, P x * inPrefixInd (perm x) 1 i) = 1 / (m : ℝ))
    (habs : ∑ i, |g i| = (m : ℝ) + 4) :
    (∑ x, P x * regret g (perm x) D 1) = (((m : ℝ) + 4) / (m : ℝ) - 1) / D := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  -- expand each term
  have hterm : ∀ x : R, P x * regret g (perm x) D 1
      = P x * ((∑ i, |g i| * (if i = (perm x) ⟨0, hm⟩ then (1:ℝ) else 0)) - 1) / D := by
    intro x
    rw [regret_at_one hm g (perm x) D]
    have hpick : (∑ i, |g i| * (if i = (perm x) ⟨0, hm⟩ then (1:ℝ) else 0))
        = |g ((perm x) ⟨0, hm⟩)| := by
      have hrw : ∀ i : Fin m, |g i| * (if i = (perm x) ⟨0, hm⟩ then (1:ℝ) else 0)
          = if i = (perm x) ⟨0, hm⟩ then |g i| else 0 := by
        intro i
        by_cases hi : i = (perm x) ⟨0, hm⟩
        · rw [if_pos hi, if_pos hi, mul_one]
        · rw [if_neg hi, if_neg hi, mul_zero]
      rw [Finset.sum_congr rfl (fun i _ => hrw i),
        Finset.sum_ite_eq' Finset.univ ((perm x) ⟨0, hm⟩) (fun i => |g i|),
        if_pos (Finset.mem_univ _)]
    rw [hpick]
    ring
  -- pull out 1/D and swap the two sums
  have hswap : ∑ x, P x * ((∑ i, |g i| * (if i = (perm x) ⟨0, hm⟩ then (1:ℝ) else 0)) - 1)
      = (∑ i, |g i| * (∑ x, P x * inPrefixInd (perm x) 1 i)) - 1 := by
    have hexp : ∀ x : R,
        P x * ((∑ i, |g i| * (if i = (perm x) ⟨0, hm⟩ then (1:ℝ) else 0)) - 1)
          = (∑ i, |g i| * (P x * inPrefixInd (perm x) 1 i)) - P x := by
      intro x
      rw [mul_sub, mul_one, Finset.mul_sum]
      have hin : ∀ i : Fin m, P x * (|g i| * (if i = (perm x) ⟨0, hm⟩ then (1:ℝ) else 0))
          = |g i| * (P x * inPrefixInd (perm x) 1 i) := by
        intro i
        rw [first_eq_inPrefix hm (perm x) i]
        ring
      rw [Finset.sum_congr rfl (fun i _ => hin i)]
    rw [Finset.sum_congr rfl (fun x _ => hexp x), Finset.sum_sub_distrib, hsum,
      Finset.sum_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.sum_div, hswap,
    Finset.sum_congr rfl (fun i _ => by rw [hmarg i]), ← Finset.sum_mul, habs]
  field_simp

/-- **(C-H1, the lower side) The value at uniform marginals is at least `4/(m(m+4))`.**
The objective is a maximum over budgets, and budget `1` already costs that much. -/
theorem value_ge_at_uniform (hm : 0 < m) (g : Ranking m) (P : R → ℝ)
    (perm : R → Equiv.Perm (Fin m)) (D : ℝ) (hD : 0 < D)
    (hsum : ∑ x, P x = 1)
    (hmarg : ∀ i, (∑ x, P x * inPrefixInd (perm x) 1 i) = 1 / (m : ℝ))
    (habs : ∑ i, |g i| = (m : ℝ) + 4)
    (budgets : Finset ℕ) (hne : budgets.Nonempty) (h1 : 1 ∈ budgets) :
    4 / ((m : ℝ) * D) ≤ maxRegret P g perm D budgets hne := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hval := expected_regret_at_one hm g P perm D hD hsum hmarg habs
  have hrw : (((m : ℝ) + 4) / (m : ℝ) - 1) / D = 4 / ((m : ℝ) * D) := by
    field_simp
    ring
  rw [hrw] at hval
  rw [← hval]
  exact Finset.le_sup' (fun k => ∑ x, P x * regret g (perm x) D k) h1

/-- **At the family's own normaliser.**  `D = m + 4`, so the lower bound is exactly the
value C-H1 reports at even `m`. -/
theorem value_ge_at_uniform_at_D (hm : 0 < m) (g : Ranking m) (P : R → ℝ)
    (perm : R → Equiv.Perm (Fin m))
    (hsum : ∑ x, P x = 1)
    (hmarg : ∀ i, (∑ x, P x * inPrefixInd (perm x) 1 i) = 1 / (m : ℝ))
    (habs : ∑ i, |g i| = (m : ℝ) + 4)
    (budgets : Finset ℕ) (hne : budgets.Nonempty) (h1 : 1 ∈ budgets) :
    4 / ((m : ℝ) * ((m : ℝ) + 4))
      ≤ maxRegret P g perm ((m : ℝ) + 4) budgets hne := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact value_ge_at_uniform hm g P perm ((m : ℝ) + 4) (by linarith) hsum hmarg habs
    budgets hne h1

/-! ## Both sides at `eta = 0` -/

/-- **Every law feasible at `eta = 0` has exactly uniform budget-1 marginals.** -/
theorem marg_of_feasible_zero (hm : 0 < m) (perm : R → Equiv.Perm (Fin m)) (P : R → ℝ)
    (hP : P ∈ FeasibleAt perm 0) (i : Fin m) :
    (∑ x, P x * inPrefixInd (perm x) 1 i) = 1 / (m : ℝ) := by
  have hband := hP.2.2 1 hm i
  have hzero : (0 : ℝ) / (m : ℝ) = 0 := by simp
  rw [hzero] at hband
  have := abs_nonpos_iff.mp hband
  have hcast : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [hcast] at this
  linarith [this]

/-- **(C-H1, lower side at `eta = 0`) The value is at least `4/(m(m+4))`.**  Every feasible
law pays that much at budget `1` alone. -/
theorem Vm_ge_at_zero (hm : 0 < m) (g : Ranking m) (perm : R → Equiv.Perm (Fin m))
    (habs : ∑ i, |g i| = (m : ℝ) + 4)
    (budgets : Finset ℕ) (hne : budgets.Nonempty) (h1 : 1 ∈ budgets)
    (hfne : (FeasibleAt perm (0 : ℝ) : Set (R → ℝ)).Nonempty) :
    4 / ((m : ℝ) * ((m : ℝ) + 4)) ≤ Vm g perm ((m : ℝ) + 4) 0 budgets hne := by
  refine le_csInf (hfne.image _) ?_
  rintro y ⟨P, hP, rfl⟩
  exact value_ge_at_uniform_at_D hm g P perm hP.2.1
    (fun i => marg_of_feasible_zero hm perm P hP i) habs budgets hne h1

/-- **(C-H1 at even `m`, both sides) `V_m(0) = 4/(m(m+4))`.**  The lower side is the budget-1
identity above, holding for EVERY feasible law; the upper side is any single feasible law of
that value.  `LeanPaperCUniformV1` proves the flat-augmented flipped mixture's type counts
are exactly uniform and `evenMixtureFlipped_value_at_D` computes its value, so what the
hypothesis `hupper` still asks for is the index set and the law itself, not the arithmetic. -/
theorem Vm_eq_at_zero (hm : 0 < m) (g : Ranking m) (perm : R → Equiv.Perm (Fin m))
    (habs : ∑ i, |g i| = (m : ℝ) + 4)
    (budgets : Finset ℕ) (hne : budgets.Nonempty) (h1 : 1 ∈ budgets)
    (hD : (0 : ℝ) < (m : ℝ) + 4)
    (hbud : ∀ k ∈ budgets, k ≤ m)
    (hw : ∀ (σ : Equiv.Perm (Fin m)) (i : Fin m),
      rankOf g σ i = -3 ∨ rankOf g σ i = -1 ∨ rankOf g σ i = 1 ∨ rankOf g σ i = 3)
    (hupper : ∃ P ∈ FeasibleAt perm (0 : ℝ),
      maxRegret P g perm ((m : ℝ) + 4) budgets hne = 4 / ((m : ℝ) * ((m : ℝ) + 4))) :
    Vm g perm ((m : ℝ) + 4) 0 budgets hne = 4 / ((m : ℝ) * ((m : ℝ) + 4)) := by
  obtain ⟨P, hP, hval⟩ := hupper
  refine le_antisymm ?_ (Vm_ge_at_zero hm g perm habs budgets hne h1 ⟨P, hP⟩)
  have hmem : maxRegret P g perm ((m : ℝ) + 4) budgets hne
      ∈ (fun Q => maxRegret Q g perm ((m : ℝ) + 4) budgets hne) '' FeasibleAt perm (0 : ℝ) :=
    ⟨P, hP, rfl⟩
  have := csInf_le (Vm_bddBelow g perm ((m : ℝ) + 4) 0 hD budgets hne hbud hw) hmem
  rwa [hval] at this

/-! ## Audit -/

#print axioms marg_of_feasible_zero
#print axioms Vm_ge_at_zero
#print axioms Vm_eq_at_zero
#print axioms regret_at_one
#print axioms expected_regret_at_one
#print axioms value_ge_at_uniform
#print axioms value_ge_at_uniform_at_D

end CIGAMF.P13.PaperCLowerZero
