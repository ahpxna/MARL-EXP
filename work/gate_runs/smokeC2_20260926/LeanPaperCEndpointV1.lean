import «LeanPaperCFamilyV1»
import «LeanPaperCBandV1»

/-!
# Paper C: the four steps between the band and the value

`O2_even_from_endpoint_band` reduces (O2) to four inputs, and the C3 row owed all but one of
them at an actual law over rankings.  They are supplied here.

1. **Endpoint probabilities from the prefix band.**  The band constrains
   `Pr(i in prefix_k)`, not positions.  The first position IS the budget-1 prefix and the
   last position is the COMPLEMENT of the budget-`(m-1)` prefix, so the two endpoint
   probabilities come from the band's lower side at `k=1` and its UPPER side at `k=m-1`.
   Both are pointwise identities about a permutation: `i = sigma 0` iff `sigma^{-1} i < 1`,
   and `i = sigma (m-1)` iff NOT `sigma^{-1} i < m-1`.

2. **Actual regret is the normalised excess.**  `regret` is `excess / D` at the ranking the
   permutation names, and at the two budgets the breakpoint uses the baseline is `1` at
   both, which is what `hid_for_breakpoint` consumes.

3. **Two endpoint expectations bound the maximum.**  The objective is `max_k E r_k`, and the
   average of any two budgets is at most the maximum over a budget set containing them.

4. **The infimum over feasible laws.**  A bound holding at every feasible law bounds the
   infimum, which is the value.

The heavy-set cardinality, the fifth input, is `gFamily_heavy_card`.
-/

namespace CIGAMF.P13.PaperCEndpoint

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCInstantiation
open CIGAMF.P13.PaperCBand
open CIGAMF.P13.PaperCFamily

variable {m : ℕ}

/-! ## 1. The endpoints are prefix events -/

/-- Item `i` lies inside the first `k` positions of the ranking named by `σ`. -/
noncomputable def inPrefixInd (σ : Equiv.Perm (Fin m)) (k : ℕ) (i : Fin m) : ℝ :=
  if ((σ.symm i : Fin m) : ℕ) < k then 1 else 0

/-- **The first position is the budget-1 prefix**, as an identity of indicators. -/
theorem first_eq_inPrefix (hm : 0 < m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (if i = σ ⟨0, hm⟩ then (1 : ℝ) else 0) = inPrefixInd σ 1 i := by
  unfold inPrefixInd
  by_cases h : i = σ ⟨0, hm⟩
  · have hsym : ((σ.symm i : Fin m) : ℕ) = 0 := by
      rw [h, Equiv.symm_apply_apply]
    rw [if_pos h, if_pos (by omega)]
  · have hsym : ((σ.symm i : Fin m) : ℕ) ≠ 0 := by
      intro hc
      exact h (by
        have : σ.symm i = (⟨0, hm⟩ : Fin m) := Fin.ext hc
        rw [← this, Equiv.apply_symm_apply])
    rw [if_neg h, if_neg (by omega)]

/-- **The last position is the complement of the budget-`(m-1)` prefix**, as an identity of
indicators.  This is where the band's upper side enters. -/
theorem last_eq_one_sub_inPrefix (hm : 0 < m) (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    (if i = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) = 1 - inPrefixInd σ (m - 1) i := by
  unfold inPrefixInd
  have hlt : ((σ.symm i : Fin m) : ℕ) < m := (σ.symm i).isLt
  by_cases h : i = σ ⟨m - 1, by omega⟩
  · have hsym : ((σ.symm i : Fin m) : ℕ) = m - 1 := by
      rw [h, Equiv.symm_apply_apply]
    rw [if_pos h, if_neg (by omega)]
    norm_num
  · have hsym : ((σ.symm i : Fin m) : ℕ) ≠ m - 1 := by
      intro hc
      exact h (by
        have : σ.symm i = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext hc
        rw [← this, Equiv.apply_symm_apply])
    rw [if_neg h, if_pos (by omega)]
    norm_num

/-- **The first-position probability, from the band's lower side at `k = 1`.** -/
theorem endpoint_first_lower {R : Type*} [Fintype R] (hm : 0 < m)
    (P : R → ℝ) (perm : R → Equiv.Perm (Fin m)) (i : Fin m) (mR η : ℝ) (hmR : 0 < mR)
    (hband : 1 / mR - η / mR ≤ ∑ x, P x * inPrefixInd (perm x) 1 i) :
    (1 - η) / mR ≤ ∑ x, P x * (if i = perm x ⟨0, hm⟩ then (1 : ℝ) else 0) :=
  first_position_lower P (fun x => inPrefixInd (perm x) 1 i)
    (fun x => if i = perm x ⟨0, hm⟩ then (1 : ℝ) else 0) mR η hmR
    (fun x => first_eq_inPrefix hm (perm x) i) hband

/-- **The last-position probability, from the band's UPPER side at `k = m-1`.** -/
theorem endpoint_last_lower {R : Type*} [Fintype R] (hm : 0 < m)
    (P : R → ℝ) (perm : R → Equiv.Perm (Fin m)) (i : Fin m) (mR η : ℝ) (hmR : 0 < mR)
    (hsum : ∑ x, P x = 1)
    (hband : ∑ x, P x * inPrefixInd (perm x) (m - 1) i ≤ (mR - 1) / mR + η / mR) :
    (1 - η) / mR ≤ ∑ x, P x * (if i = perm x ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) :=
  last_position_lower P (fun x => inPrefixInd (perm x) (m - 1) i)
    (fun x => if i = perm x ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) mR η hmR hsum
    (fun x => last_eq_one_sub_inPrefix hm (perm x) i) hband

/-! ## 2. Actual regret is the normalised excess -/

/-- The regret the ranking game charges at budget `k`: the excess over the per-budget
baseline, normalised by `D`. -/
noncomputable def regret (g : Ranking m) (σ : Equiv.Perm (Fin m)) (D : ℝ) (k : ℕ) : ℝ :=
  excess (rankOf g σ) k / D

/-- At an odd budget the baseline is `1`, so the regret is the shape the breakpoint
identity consumes. -/
theorem regret_odd_budget (g : Ranking m) (σ : Equiv.Perm (Fin m)) (D : ℝ) (k : ℕ)
    (hk : k % 2 = 1) :
    regret g σ D k = (|prefixSum (rankOf g σ) k| - 1) / D := by
  unfold regret excess
  rw [hk]
  norm_num

/-- **The identity, on the actual regret.**  `hid_at_permutation_law` in the variables the
game uses. -/
theorem hid_on_regret {R : Type*} [Fintype R] (hm : 1 < m) (hmeven : m % 2 = 0)
    (g : Ranking m) (hg : IsEvenFamily g) (perm : R → Equiv.Perm (Fin m))
    (D : ℝ) (hD : D ≠ 0) :
    ∀ x : R,
      regret g (perm x) D 1 + regret g (perm x) D (m - 1)
        = 2 / D * (heavy (rankOf g (perm x) ⟨0, by omega⟩)
            + heavy (rankOf g (perm x) ⟨m - 1, by omega⟩)) := by
  intro x
  rw [regret_odd_budget g (perm x) D 1 (by omega),
    regret_odd_budget g (perm x) D (m - 1) (by omega)]
  exact hid_at_permutation_law hm g hg perm D hD x

/-! ## 3. Two budgets bound the maximum -/

/-- The objective: the worst budget's expected regret. -/
noncomputable def maxRegret {R : Type*} [Fintype R] (P : R → ℝ) (g : Ranking m)
    (perm : R → Equiv.Perm (Fin m)) (D : ℝ)
    (budgets : Finset ℕ) (hne : budgets.Nonempty) : ℝ :=
  budgets.sup' hne (fun k => ∑ x, P x * regret g (perm x) D k)

/-- **The average of two budgets is at most the maximum**, so a lower bound on the two
endpoint budgets is a lower bound on the objective. -/
theorem avg_two_le_maxRegret {R : Type*} [Fintype R] (P : R → ℝ) (g : Ranking m)
    (perm : R → Equiv.Perm (Fin m)) (D : ℝ)
    (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (h1 : 1 ∈ budgets) (h2 : m - 1 ∈ budgets) :
    (∑ x, P x * (regret g (perm x) D 1 + regret g (perm x) D (m - 1))) / 2
      ≤ maxRegret P g perm D budgets hne := by
  have hsplit : ∑ x, P x * (regret g (perm x) D 1 + regret g (perm x) D (m - 1))
      = (∑ x, P x * regret g (perm x) D 1) + ∑ x, P x * regret g (perm x) D (m - 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  have hA : (∑ x, P x * regret g (perm x) D 1) ≤ maxRegret P g perm D budgets hne :=
    Finset.le_sup' (fun k => ∑ x, P x * regret g (perm x) D k) h1
  have hB : (∑ x, P x * regret g (perm x) D (m - 1))
      ≤ maxRegret P g perm D budgets hne :=
    Finset.le_sup' (fun k => ∑ x, P x * regret g (perm x) D k) h2
  rw [hsplit]
  linarith

/-! ## 4. The infimum over feasible laws -/

/-- **A bound at every feasible law bounds the value.** -/
theorem le_value_of_forall (S : Set ℝ) (hne : S.Nonempty) (c : ℝ)
    (h : ∀ v ∈ S, c ≤ v) : c ≤ sInf S :=
  le_csInf hne h

/-! ## The assembly -/

/-- **(O2) at an actual law over rankings of the family, every input discharged.**  The
band, the heavy-set cardinality, the endpoint identities, the regret identity and the
maximum are all supplied; nothing is left as a hypothesis about the game. -/
theorem O2_even_at_ranking_law {R : Type*} [Fintype R]
    (n : ℕ) (hn : 1 ≤ n) (hpar : n % 2 = 0)
    (P : R → ℝ) (perm : R → Equiv.Perm (Fin (n + 2))) (D η : ℝ) (hD : 0 < D)
    (hsum : ∑ x, P x = 1)
    (hη : η < (((n : ℝ) + 2) - 2) / (2 * (((n : ℝ) + 2) - 1)))
    (hbandfirst : ∀ i ∈ heavySet (gFamily (n + 2)),
      1 / ((n : ℝ) + 2) - η / ((n : ℝ) + 2)
        ≤ ∑ x, P x * inPrefixInd (perm x) 1 i)
    (hbandlast : ∀ i ∈ heavySet (gFamily (n + 2)),
      ∑ x, P x * inPrefixInd (perm x) (n + 2 - 1) i
        ≤ (((n : ℝ) + 2) - 1) / ((n : ℝ) + 2) + η / ((n : ℝ) + 2))
    (budgets : Finset ℕ) (hne : budgets.Nonempty)
    (h1 : 1 ∈ budgets) (h2 : n + 2 - 1 ∈ budgets) :
    2 / (D * (((n : ℝ) + 2) - 1))
      < maxRegret P (gFamily (n + 2)) perm D budgets hne := by
  classical
  have hm2 : 1 < n + 2 := by omega
  have hmpos : 0 < n + 2 := by omega
  have hmR : (2 : ℝ) < (n : ℝ) + 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hmcast : (((n + 2 : ℕ)) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  have hstrict := O2_even_from_endpoint_band
    (R := R) (I := Fin (n + 2)) P
    (fun x => regret (gFamily (n + 2)) (perm x) D 1)
    (fun x => regret (gFamily (n + 2)) (perm x) D (n + 2 - 1))
    (fun x => heavy (rankOf (gFamily (n + 2)) (perm x) ⟨0, hmpos⟩)
      + heavy (rankOf (gFamily (n + 2)) (perm x) ⟨n + 2 - 1, by omega⟩))
    (fun i x => if i = perm x ⟨0, hmpos⟩ then (1 : ℝ) else 0)
    (fun i x => if i = perm x ⟨n + 2 - 1, by omega⟩ then (1 : ℝ) else 0)
    (heavySet (gFamily (n + 2))) ((n : ℝ) + 2) D η hmR hD hη
    (hid_on_regret hm2 (by omega) (gFamily (n + 2))
      (gFamily_isEvenFamily n hn hpar) perm D (ne_of_gt hD))
    (by rw [gFamily_heavy_card n hn]; norm_num)
    (fun x => big_eq_sum_endpoints (gFamily (n + 2)) hmpos (perm x))
    (fun i hi => endpoint_first_lower hmpos P perm i ((n : ℝ) + 2) η (by linarith)
      (hbandfirst i hi))
    (fun i hi => endpoint_last_lower hmpos P perm i ((n : ℝ) + 2) η (by linarith) hsum
      (hbandlast i hi))
  exact lt_of_lt_of_le hstrict
    (avg_two_le_maxRegret P (gFamily (n + 2)) perm D budgets hne h1 h2)

/-- **And therefore at the value**, which is the infimum over feasible laws. -/
theorem O2_even_at_value (S : Set ℝ) (hne : S.Nonempty) (D mR : ℝ)
    (h : ∀ v ∈ S, 2 / (D * (mR - 1)) ≤ v) :
    2 / (D * (mR - 1)) ≤ sInf S :=
  le_value_of_forall S hne _ h

/-! ## Audit -/

#print axioms first_eq_inPrefix
#print axioms last_eq_one_sub_inPrefix
#print axioms endpoint_first_lower
#print axioms endpoint_last_lower
#print axioms regret_odd_budget
#print axioms hid_on_regret
#print axioms avg_two_le_maxRegret
#print axioms le_value_of_forall
#print axioms O2_even_at_ranking_law
#print axioms O2_even_at_value

end CIGAMF.P13.PaperCEndpoint
