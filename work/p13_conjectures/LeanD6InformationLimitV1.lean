import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Abstract subset-distance game: counting lemmas for a D6 information limit

Lower-bound skeleton for the D6 selection problem, with *no enumeration*:
nothing here is proved by `decide`, by `native_decide`, or by case explosion,
and there is no induction on the ground set.

Setting. A world label is an `r`-subset `T` of a ground set `U`; loss is
DEFINED to be `(S \ T).card`. Constancy of the observation map is a hypothesis
of `selector_constant_on_family`, not a construction proved in this module.

Scope. These lemmas prove an abstract counting identity and a deterministic
worst-case bound. This module does not define actual D6 worlds, prove equality
of their productResponse profiles, identify productCompressionLoss with this
loss, or prove a bound for randomized selectors. A D6 bridge must also cover
all legal retained sets (including choices of the distinguished coordinate).

* Link 1 -- indistinguishability (`selector_constant_on_family`).
* Link 2 -- regret is a distance (`regretOn`, a definition).
* Link 3 -- averaging (`sum_sdiff_card_powersetCard`), the combinatorial heart:
  `∑_{T ∈ C(U,r)} |S \ T| = |S| * C(|U|-1, r)` for every `S ⊆ U`, proved by
  exchanging the two sums and counting the `r`-subsets avoiding a fixed `i`.

Specialising to `|U| = 2j+1`, `r = j+1` gives the closed form
`(j+1)*j/(2j+1)`, stated as an exact product over `ℕ` so that neither
division nor truncated subtraction appears.

Every Mathlib name used below was checked against the pinned Mathlib in
`.lake/packages/mathlib` before writing:
`Finset.sdiff_eq_filter` (Data/Finset/Basic 388),
`Finset.card_filter` (Algebra/BigOperators/Group/Finset/Piecewise 278),
`Finset.card_powersetCard` (Data/Finset/Powerset 212),
`Finset.mem_powersetCard` (Powerset 202),
`Finset.subset_erase` (Data/Finset/Erase 92),
`Finset.card_erase_of_mem` (Data/Finset/Card 152),
`Finset.powersetCard_nonempty` (Powerset 292),
`Finset.exists_max_image` (Data/Finset/Max 528),
`Nat.choose_succ_succ'` (Data/Nat/Choose/Basic 66),
`Nat.add_one_mul_choose_eq` (Data/Nat/Choose/Basic 131).
-/

namespace CIGAMF.P13.InformationLimit

open scoped BigOperators
open Finset

variable {α : Type*} [DecidableEq α]

/-! ## Link 2: regret is the distance to the optimal set -/

/-- Abstract loss: selected elements outside `T`. For equal cardinalities this
also counts missed elements of `T`. This is a definition, not a D6 loss theorem. -/
def regretOn (S T : Finset α) : ℕ := (S \ T).card

theorem regretOn_eq_card_sdiff (S T : Finset α) :
    regretOn S T = (S \ T).card := rfl

/-! ## Link 1: indistinguishability -/

omit [DecidableEq α] in
/-- If the observation map is constant on a family of worlds, every selector
reading only that observation returns one fixed set across the family. -/
theorem selector_constant_on_family {O : Type*} (obs : Finset α → O)
    (selector : O → Finset α) (W : Finset (Finset α)) (o : O)
    (hconst : ∀ T ∈ W, obs T = o) :
    ∀ T ∈ W, selector (obs T) = selector o := by
  intro T hT
  rw [hconst T hT]

/-! ## Link 3: the averaging identity -/

/-- The `r`-subsets of `U` avoiding `i` are exactly the `r`-subsets of
`U.erase i`. -/
theorem filter_not_mem_powersetCard (U : Finset α) (r : ℕ) (i : α) :
    (U.powersetCard r).filter (fun T => i ∉ T) = (U.erase i).powersetCard r := by
  ext T
  simp only [mem_filter, mem_powersetCard, subset_erase]
  exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩

/-- Count of `r`-subsets of `U` avoiding a fixed member `i`. -/
theorem card_filter_not_mem (U : Finset α) (r : ℕ) {i : α} (hi : i ∈ U) :
    ((U.powersetCard r).filter (fun T => i ∉ T)).card = (U.card - 1).choose r := by
  rw [filter_not_mem_powersetCard, card_powersetCard, card_erase_of_mem hi]

/-- **The averaging identity.** -/
theorem sum_sdiff_card_powersetCard (U : Finset α) (r : ℕ) (S : Finset α)
    (hS : S ⊆ U) :
    ∑ T ∈ U.powersetCard r, (S \ T).card
      = S.card * (U.card - 1).choose r := by
  calc ∑ T ∈ U.powersetCard r, (S \ T).card
      = ∑ T ∈ U.powersetCard r, ∑ i ∈ S, if i ∉ T then 1 else 0 := by
        refine Finset.sum_congr rfl (fun T _ => ?_)
        rw [Finset.sdiff_eq_filter, Finset.card_filter]
    _ = ∑ i ∈ S, ∑ T ∈ U.powersetCard r, if i ∉ T then 1 else 0 := Finset.sum_comm
    _ = ∑ i ∈ S, ((U.powersetCard r).filter (fun T => i ∉ T)).card := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.card_filter]
    _ = ∑ _i ∈ S, (U.card - 1).choose r := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        exact card_filter_not_mem U r (hS hi)
    _ = S.card * (U.card - 1).choose r := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul]

/-! ## The closed form at the balanced width -/

/-- `(2j+1) * C(2j, j+1) = j * C(2j+1, j+1)`, i.e. `n*C(n-1,r) = (n-r)*C(n,r)`
at `n = 2j+1`, `r = j+1`.  Derived additively from the Pascal recurrence and
`(n+1)*C(n,k) = C(n+1,k+1)*(k+1)`; no subtraction in `ℕ`, and no `omega`
(the statement is nonlinear, so `omega` does not apply). -/
theorem choose_shift (j : ℕ) :
    (2 * j + 1) * (2 * j).choose (j + 1) = j * (2 * j + 1).choose (j + 1) := by
  have hrec : (2 * j + 1).choose (j + 1) = (2 * j).choose j + (2 * j).choose (j + 1) :=
    Nat.choose_succ_succ' (2 * j) j
  have hmul : (2 * j + 1) * (2 * j).choose j = (2 * j + 1).choose (j + 1) * (j + 1) :=
    Nat.add_one_mul_choose_eq (2 * j) j
  have hswap : (j + 1) * (2 * j + 1).choose (j + 1) = (2 * j + 1) * (2 * j).choose j := by
    rw [hmul, Nat.mul_comm]
  have key : (j + 1) * (2 * j + 1).choose (j + 1) + (2 * j + 1) * (2 * j).choose (j + 1)
      = (j + 1) * (2 * j + 1).choose (j + 1) + j * (2 * j + 1).choose (j + 1) := by
    calc (j + 1) * (2 * j + 1).choose (j + 1) + (2 * j + 1) * (2 * j).choose (j + 1)
        = (2 * j + 1) * (2 * j).choose j + (2 * j + 1) * (2 * j).choose (j + 1) := by
          rw [hswap]
      _ = (2 * j + 1) * ((2 * j).choose j + (2 * j).choose (j + 1)) := by ring
      _ = (2 * j + 1) * (2 * j + 1).choose (j + 1) := by rw [← hrec]
      _ = (j + 1) * (2 * j + 1).choose (j + 1) + j * (2 * j + 1).choose (j + 1) := by ring
  exact Nat.add_left_cancel key

/-- **The information limit in exact form.**  Total regret over the whole
family is the same for every choice `S` of `j+1` elements of a ground set of
size `2j+1`, and equals `(j+1)*j/(2j+1)` per world.  Written without division. -/
theorem information_limit_exact (U : Finset α) (j : ℕ) (hU : U.card = 2 * j + 1)
    (S : Finset α) (hS : S ⊆ U) (hcard : S.card = j + 1) :
    (2 * j + 1) * (∑ T ∈ U.powersetCard (j + 1), regretOn S T)
      = (j + 1) * j * (U.powersetCard (j + 1)).card := by
  have hsum : ∑ T ∈ U.powersetCard (j + 1), regretOn S T
      = (j + 1) * (2 * j).choose (j + 1) := by
    unfold regretOn
    rw [sum_sdiff_card_powersetCard U (j + 1) S hS, hcard, hU, Nat.add_sub_cancel]
  have hfam : (U.powersetCard (j + 1)).card = (2 * j + 1).choose (j + 1) := by
    rw [card_powersetCard, hU]
  rw [hsum, hfam]
  calc (2 * j + 1) * ((j + 1) * (2 * j).choose (j + 1))
      = (j + 1) * ((2 * j + 1) * (2 * j).choose (j + 1)) := by ring
    _ = (j + 1) * (j * (2 * j + 1).choose (j + 1)) := by rw [choose_shift]
    _ = (j + 1) * j * (2 * j + 1).choose (j + 1) := by ring

/-- **Worst case dominates the average** for each fixed feasible `S`.
The adversarial `T` may depend on `S`. A bound against a randomized strategy
requires a separate weighted-average argument with one `T` for the mixture. -/
theorem information_limit_worst_case (U : Finset α) (j : ℕ) (hU : U.card = 2 * j + 1)
    (S : Finset α) (hS : S ⊆ U) (hcard : S.card = j + 1) :
    ∃ T ∈ U.powersetCard (j + 1),
      (j + 1) * j * (U.powersetCard (j + 1)).card
        ≤ (2 * j + 1) * regretOn S T * (U.powersetCard (j + 1)).card := by
  have hne : (U.powersetCard (j + 1)).Nonempty := by
    refine Finset.powersetCard_nonempty.2 ?_
    omega
  obtain ⟨T, hT, hmax⟩ :=
    Finset.exists_max_image (U.powersetCard (j + 1)) (fun T => regretOn S T) hne
  refine ⟨T, hT, ?_⟩
  have hbound : ∑ T' ∈ U.powersetCard (j + 1), regretOn S T'
      ≤ (U.powersetCard (j + 1)).card * regretOn S T := by
    calc ∑ T' ∈ U.powersetCard (j + 1), regretOn S T'
        ≤ ∑ _T' ∈ U.powersetCard (j + 1), regretOn S T :=
          Finset.sum_le_sum (fun T' hT' => hmax T' hT')
      _ = (U.powersetCard (j + 1)).card * regretOn S T := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul]
  calc (j + 1) * j * (U.powersetCard (j + 1)).card
      = (2 * j + 1) * (∑ T' ∈ U.powersetCard (j + 1), regretOn S T') :=
        (information_limit_exact U j hU S hS hcard).symm
    _ ≤ (2 * j + 1) * ((U.powersetCard (j + 1)).card * regretOn S T) :=
        Nat.mul_le_mul (le_refl _) hbound
    _ = (2 * j + 1) * regretOn S T * (U.powersetCard (j + 1)).card := by ring

/-! ## Instances of the closed form

`(j+1)*j/(2j+1)` at `j = 2,3,4,5` is `6/5, 12/7, 20/9, 30/11`.
These are arithmetic checks only; they do not construct D6 worlds at those widths. -/

example : (2 + 1) * 2 * 5 = 6 * 5 := by norm_num
example : (3 + 1) * 3 * 7 = 12 * 7 := by norm_num
example : (4 + 1) * 4 * 9 = 20 * 9 := by norm_num
example : (5 + 1) * 5 * 11 = 30 * 11 := by norm_num

end CIGAMF.P13.InformationLimit
