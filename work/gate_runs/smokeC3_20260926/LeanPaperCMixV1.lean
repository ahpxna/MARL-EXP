import «LeanPaperCEvenV1»

/-!
# Paper C: the even mixture's per-budget value

The even-`m` upper bound on `V_m(0)` mixes the `m-1` insertion rankings with the flat
ranking of `LeanPaperCEvenV1`, uniformly over the `m` of them.  Its per-budget value is what
the bound needs, and it follows from two results that already exist plus one arithmetic
step; nothing is re-proved here.

* `insMixture_free_value` (`LeanPaperCRankingV1`) says the `m-1` insertion rankings carry a
  total excess of `2` at EVERY budget --- each contributes a single spike, and the spikes
  cover the budgets exactly once.
* `flatEven_excess` (`LeanPaperCEvenV1`) says the extra ranking carries `2` at every budget,
  flat rather than spiked.

Mixing all `m` uniformly therefore gives `(2 + 2)/m` at every budget, i.e. `4/(m D)`.  At the
family's normaliser `D = m + 4` that is exactly

    V_m(0) <= 4 / (m (m+4)),      m even,

the value the breakpoint law claims.

WHAT IS NOT HERE.  The value, not the feasibility.  That the mixture's per-item RETAINED
MARGINALS are uniform --- which needs the sign flip at ratio `1/2` and uniform relabelling
within each weight type, and then `marginal_eq_occupancy_div_card` and
`relabelledLaw_invariant` of `LeanPaperCBreakpointV1`, both of which already exist --- is
not established in this file.  Without it the mixture is not shown to be feasible and the
upper bound does not follow.
-/

namespace CIGAMF.P13.PaperCMix

open Finset
open CIGAMF.P13.PaperCRanking
open CIGAMF.P13.PaperCEven

variable {m : ℕ}

/-- **The insertion rankings carry a total excess of `2` at every budget**, restated without
the mixing weight --- a rescaling of `insMixture_free_value`, not a new proof. -/
theorem insertion_total_excess (m : ℕ) (hm : 1 < m) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ m - 1) :
    ∑ a ∈ Finset.range (m - 1), excess (insRanking m a) k = 2 := by
  have hmr : ((m : ℝ) - 1) ≠ 0 := by
    have h1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have h := insMixture_free_value m hm 1 one_ne_zero k hk1 hk
  simp only [div_one] at h
  rw [← Finset.mul_sum] at h
  field_simp at h
  linarith [h]

/-- **The even mixture's per-budget value.**  Uniform over the `m-1` insertion rankings and
the flat one: `(2 + 2)/m` at every budget. -/
theorem evenMixture_value (m : ℕ) (hm : 1 < m) (D : ℝ) (hD : D ≠ 0) (k : ℕ)
    (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    (∑ a ∈ Finset.range (m - 1), (1 / (m : ℝ)) * (excess (insRanking m a) k / D))
        + (1 / (m : ℝ)) * (excess (flatEven m) k / D)
      = 4 / ((m : ℝ) * D) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hins : ∑ a ∈ Finset.range (m - 1), excess (insRanking m a) k = 2 :=
    insertion_total_excess m hm k hk1 hk
  have hflat : excess (flatEven m) k = 2 := flatEven_excess hm k hk1 hk
  have hpull : ∑ a ∈ Finset.range (m - 1), (1 / (m : ℝ)) * (excess (insRanking m a) k / D)
      = (1 / ((m : ℝ) * D)) * ∑ a ∈ Finset.range (m - 1), excess (insRanking m a) k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by ring
  rw [hpull, hins, hflat]
  field_simp
  ring

/-- **At the family's normaliser the value is the claimed one.** -/
theorem evenMixture_value_at_D (m : ℕ) (hm : 1 < m) (k : ℕ) (hk1 : 1 ≤ k)
    (hk : k ≤ m - 1) :
    (∑ a ∈ Finset.range (m - 1),
        (1 / (m : ℝ)) * (excess (insRanking m a) k / ((m : ℝ) + 4)))
        + (1 / (m : ℝ)) * (excess (flatEven m) k / ((m : ℝ) + 4))
      = 4 / ((m : ℝ) * ((m : ℝ) + 4)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  exact evenMixture_value m hm ((m : ℝ) + 4) (by positivity) k hk1 hk

/-- **The value does not depend on the budget**, which is what makes the maximum over
budgets equal to it rather than larger. -/
theorem evenMixture_value_constant (m : ℕ) (hm : 1 < m) (D : ℝ) (hD : D ≠ 0)
    (k l : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) (hl1 : 1 ≤ l) (hl : l ≤ m - 1) :
    (∑ a ∈ Finset.range (m - 1), (1 / (m : ℝ)) * (excess (insRanking m a) k / D))
        + (1 / (m : ℝ)) * (excess (flatEven m) k / D)
      = (∑ a ∈ Finset.range (m - 1), (1 / (m : ℝ)) * (excess (insRanking m a) l / D))
        + (1 / (m : ℝ)) * (excess (flatEven m) l / D) := by
  rw [evenMixture_value m hm D hD k hk1 hk, evenMixture_value m hm D hD l hl1 hl]

/-! ## Audit -/

#print axioms insertion_total_excess
#print axioms evenMixture_value
#print axioms evenMixture_value_at_D
#print axioms evenMixture_value_constant

end CIGAMF.P13.PaperCMix
