import «LeanPaperCBandV1»
import «LeanPaperCRankingV1»

/-!
# Paper C: the breakpoint hypotheses, instantiated at an actual ranking law

`O2_even_from_endpoint_band` (`LeanPaperCBandV1`) takes three things about the family it is
applied to: the endpoint identity `r_1 + r_{m-1} = (2/D) * big`, the fact that `big` is the
SUM of the four heavy-endpoint indicators, and the count of heavy items.  This module
supplies all three for a law over **actual permutations** of the signed-prefix family, so
the breakpoint conclusion no longer rests on hypotheses about an unnamed family.

The identity itself is NOT re-proved here: `two_budget_identity` and `hid_for_breakpoint`
in `LeanPaperCRankingV1` already have it, and what was missing was the bridge from those to
a law over permutations.  Two pieces do that.

* **A permutation of an even family is an even family.**  The weight condition is pointwise
  and the total is permutation-invariant, so `IsEvenFamily` transports along any relabelling
  of positions.  This is what lets `hid_for_breakpoint` be applied to `g ∘ σ` rather than to
  `g` alone.
* **The heavy endpoint count is the sum of four indicators.**  Exactly one item occupies the
  first position and exactly one the last, so `heavy` at an endpoint is the indicator that
  the occupying item lies in the heavy set — and summing over the heavy set turns the two
  `heavy` terms into the four indicators `big` is defined from.  No exclusivity between the
  four is claimed, and none holds: both heavy items can occupy the two ends at once.
-/

namespace CIGAMF.P13.PaperCInstantiation

open Finset
open CIGAMF.P13.PaperCRanking

variable {m : ℕ}

/-! ## The family transports along a permutation of the positions -/

/-- **A relabelling of positions preserves the even family.** -/
theorem isEvenFamily_comp (g : Ranking m) (hg : IsEvenFamily g) (σ : Equiv.Perm (Fin m)) :
    IsEvenFamily (fun i => g (σ i)) where
  weight := fun i => hg.weight (σ i)
  total := by
    rw [Equiv.sum_comp σ g]
    exact hg.total

/-- The ranking a permutation names: position `p` carries the weight of the item it holds. -/
noncomputable def rankOf (g : Ranking m) (σ : Equiv.Perm (Fin m)) : Ranking m :=
  fun p => g (σ p)

theorem rankOf_isEvenFamily (g : Ranking m) (hg : IsEvenFamily g) (σ : Equiv.Perm (Fin m)) :
    IsEvenFamily (rankOf g σ) := isEvenFamily_comp g hg σ

/-! ## The heavy endpoints, as a sum of indicators -/

/-- The heavy items of the base family. -/
noncomputable def heavySet (g : Ranking m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => heavy (g i) = 1)

theorem mem_heavySet {g : Ranking m} {i : Fin m} :
    i ∈ heavySet g ↔ heavy (g i) = 1 := by
  classical
  simp [heavySet]

/-- **`heavy` at a position is the indicator that the occupying item is heavy.** -/
theorem heavy_eq_sum_indicator (g : Ranking m) (σ : Equiv.Perm (Fin m)) (p : Fin m) :
    heavy (rankOf g σ p) = ∑ i ∈ heavySet g, (if i = σ p then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_ite_eq' (heavySet g) (σ p) (fun _ => (1 : ℝ))]
  unfold rankOf
  by_cases hmem : σ p ∈ heavySet g
  · rw [if_pos hmem]
    exact mem_heavySet.mp hmem
  · rw [if_neg hmem]
    rcases heavy_eq_zero_or_one (g (σ p)) with h0 | h1
    · exact h0
    · exact absurd (mem_heavySet.mpr h1) hmem

/-- **The endpoint count is the sum of the four indicators**, which is exactly the shape
`hband_even_of_endpoint_band` consumes.  `big` reaches `2` when both heavy items sit at the
two ends, and nothing here says otherwise. -/
theorem big_eq_sum_endpoints (g : Ranking m) (hm : 0 < m) (σ : Equiv.Perm (Fin m)) :
    heavy (rankOf g σ ⟨0, hm⟩) + heavy (rankOf g σ ⟨m - 1, by omega⟩)
      = ∑ i ∈ heavySet g,
          ((if i = σ ⟨0, hm⟩ then (1 : ℝ) else 0)
            + if i = σ ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) := by
  classical
  rw [Finset.sum_add_distrib, heavy_eq_sum_indicator g σ ⟨0, hm⟩,
      heavy_eq_sum_indicator g σ ⟨m - 1, by omega⟩]

/-- **The identity in the shape the breakpoint arithmetic consumes, at an actual law over
permutations.**  `hid_for_breakpoint` is applied to the permuted family; nothing is
re-proved. -/
theorem hid_at_permutation_law {R : Type*} [Fintype R] (hm : 1 < m)
    (g : Ranking m) (hg : IsEvenFamily g) (perm : R → Equiv.Perm (Fin m))
    (D : ℝ) (hD : D ≠ 0) :
    ∀ x : R,
      (|prefixSum (rankOf g (perm x)) 1| - 1) / D
        + (|prefixSum (rankOf g (perm x)) (m - 1)| - 1) / D
        = 2 / D * (heavy (rankOf g (perm x) ⟨0, by omega⟩)
            + heavy (rankOf g (perm x) ⟨m - 1, by omega⟩)) :=
  hid_for_breakpoint hm (fun x => rankOf g (perm x))
    (fun x => rankOf_isEvenFamily g hg (perm x)) D hD

/-! ## Audit -/

#print axioms isEvenFamily_comp
#print axioms rankOf_isEvenFamily
#print axioms heavy_eq_sum_indicator
#print axioms big_eq_sum_endpoints
#print axioms hid_at_permutation_law

end CIGAMF.P13.PaperCInstantiation
