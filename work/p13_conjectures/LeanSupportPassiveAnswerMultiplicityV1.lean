import «LeanSupportPassiveSamplingMassV1»

/-!
# Passive support learning with several safe answers

This file supplies the exact conditional symmetry and second-moment pieces of
the minimax formula.  A world `W` contains the unsafe tips; an observed set
`S ⊆ W` leaves `W \ S` unsafe candidates among `univ \ S` unseen decisions.

## WHAT THIS FILE IS NOT

It is NOT the minimax theorem `R_N^* = E[L_N/(a + L_N)]`, and a clean receipt on
it must not be read as closing that. What is here is set counting
(`unseen_card`, `remaining_unsafe_card`, `safe_unseen_card`), one bridge to the
real geometry (`unseen_unsafe_iff`, against `selectedRadius`), one algebraic
identity (`symmetric_posterior_value`), and two inequalities between real
numbers (`two_tip_miss_le_product`, `missing_second_moment_bound`).

FOUR OBLIGATIONS OF THE PACKAGE ARE NOT DISCHARGED ANYWHERE BELOW:

  1. the law of `N` i.i.d. draws over the anchor and the unsafe tips is not
     constructed here (`LeanSupportPassiveSamplingMassV1` has the product
     measure, but this file never uses it);
  2. the posterior under the uniform prior over unsafe sets of cardinality `b`
     is not defined, so "the posterior is uniform on the still-compatible sets"
     is not proved — `symmetric_posterior_value` ASSUMES a common posterior
     value `r` and only computes the average, which is an algebraic identity,
     not a symmetry theorem;
  3. the attaining policy (choose uniformly among the unseen) and the matching
     Bayes lower bound are not stated;
  4. `missing_second_moment_bound` is an inequality about the EXPRESSION
     `lambda + b(b-1)(1-2 gamma)^N`; that this expression is `E[L_N^2]` is not
     proved, because `L_N` is not defined as a random variable here.

Consequently `lambda/(a+1+lambda) ≤ R_N^* ≤ lambda/(a+lambda)` is NOT proved:
the two moment bounds are the analytic half only, and the minimax bridge that
turns them into a statement about `R_N^*` is missing. Do not cite this module
for a sample-size law.
-/
namespace CIGAMF.P13.SupportPassiveAnswerMultiplicity

open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportMultiTipGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
variable {m : ℕ}

def unseen (S : Finset (Fin m)) : Finset (Fin m) := Sᶜ
def remainingUnsafe (W S : Finset (Fin m)) : Finset (Fin m) := W \ S

theorem unseen_card (S : Finset (Fin m)) : (unseen S).card=m-S.card := by
  simp [unseen, Finset.card_compl]

theorem remaining_unsafe_card (W S : Finset (Fin m)) (hSW : S ⊆ W) :
    (remainingUnsafe W S).card=W.card-S.card := by
  rw [remainingUnsafe, Finset.card_sdiff, Finset.inter_eq_left.mpr hSW]

theorem safe_unseen_card (W S : Finset (Fin m)) (hSW : S ⊆ W) :
    ((unseen S) \ W).card=m-W.card := by
  have hset : unseen S \ W = (univ : Finset (Fin m)) \ W := by
    ext j
    simp [unseen]
    intro hjW
    exact fun hjS => hjW (hSW hjS)
  rw [hset, Finset.card_sdiff, Finset.inter_eq_left.mpr (subset_univ W)]
  simp

/-- In the actual support geometry an unseen decision is unsafe exactly when
it belongs to `remainingUnsafe W S`. -/
theorem unseen_unsafe_iff (hm : 2 ≤ m) (W S : Finset (Fin m)) (hSW : S ⊆ W)
    (j : Fin m) (hj : j ∈ unseen S) :
    selectedRadius (components W) {j} ≠ 0 ↔ j ∈ remainingUnsafe W S := by
  rw [ne_eq, zero_radius_iff hm, not_not]
  simp only [remainingUnsafe, Finset.mem_sdiff, unseen, Finset.mem_compl] at hj ⊢
  exact ⟨fun h => ⟨h, hj⟩, fun h => h.1⟩

/-- Under the uniform posterior on the unseen decisions, the conditional error
is exactly remaining-unsafe / unseen. -/
theorem uniform_unseen_error (W S : Finset (Fin m)) (hSW : S ⊆ W)
    (a b : ℕ) (hW : W.card=b) (hab : m=a+b) :
    ((remainingUnsafe W S).card : ℝ)/(unseen S).card =
      ((b-S.card : ℕ):ℝ)/(a+(b-S.card)) := by
  have hSb : S.card ≤ b := by rw [← hW]; exact Finset.card_le_card hSW
  have h1 : ((remainingUnsafe W S).card : ℝ) = ((b - S.card : ℕ) : ℝ) := by
    rw [remaining_unsafe_card W S hSW, hW]
  have h2 : (((unseen S).card : ℕ) : ℝ) = (a:ℝ) + ((b:ℝ) - (S.card:ℝ)) := by
    rw [unseen_card]
    have hnat : m - S.card = a + (b - S.card) := by omega
    rw [hnat]
    push_cast [Nat.cast_sub hSb]
    ring
  rw [h1, h2]

/-- Posterior symmetry lower bound: if every unseen decision has the same bad
posterior probability `r`, then randomising over unseen decisions cannot lower
the conditional error below `r` (indeed it is exactly `r`). -/
theorem symmetric_posterior_value (U : Finset (Fin m)) (w : Fin m → ℝ) (r : ℝ)
    (hsum : ∑ j ∈ U,w j=1) : ∑ j ∈ U,w j*r=r := by
  rw [← sum_mul,hsum,one_mul]

/-- Missing two specified tips is negatively correlated: their joint miss
probability `(1-2 gamma)^N` is no larger than the product of individual miss
probabilities. -/
theorem two_tip_miss_le_product (gamma : ℝ) (hg0 : 0≤gamma) (hg2 : gamma≤1/2)
    (N : ℕ) : (1-2*gamma)^N ≤ ((1-gamma)^N)^2 := by
  have hbase0 : 0≤1-2*gamma := by linarith
  have hbase : 1-2*gamma ≤ (1-gamma)^2 := by nlinarith [sq_nonneg gamma]
  have hp := pow_le_pow_left₀ hbase0 hbase N
  calc (1-2*gamma)^N ≤ ((1-gamma)^2)^N := hp
    _ = ((1-gamma)^N)^2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The exact first/second-moment expressions from the occupancy calculation
obey `E L² ≤ lambda + lambda²`. -/
theorem missing_second_moment_bound (b N : ℕ) (gamma : ℝ)
    (hg0 : 0≤gamma) (hg2 : gamma≤1/2) :
    let lambda := (b:ℝ)*(1-gamma)^N
    lambda + (b:ℝ)*(b-1)*(1-2*gamma)^N ≤ lambda+lambda^2 := by
  dsimp
  have hpow0 : 0≤(1-gamma)^N := pow_nonneg (by linarith) _
  have hpair := two_tip_miss_le_product gamma hg0 hg2 N
  have hb : (0:ℝ)≤b := Nat.cast_nonneg b
  have hbb : (0:ℝ) ≤ (b:ℝ)*((b:ℝ)-1) := by
    rcases Nat.eq_zero_or_pos b with h | h
    · simp [h]
    · have h1 : (1:ℝ) ≤ (b:ℝ) := by exact_mod_cast h
      nlinarith
  have hL : (b:ℝ)*((b:ℝ)-1)*(1-2*gamma)^N
      ≤ (b:ℝ)*((b:ℝ)-1)*(((1-gamma)^N)^2) :=
    mul_le_mul_of_nonneg_left hpair hbb
  have hR : (b:ℝ)*((b:ℝ)-1)*(((1-gamma)^N)^2)
      ≤ (b:ℝ)*(b:ℝ)*(((1-gamma)^N)^2) := by
    have h1 : (b:ℝ)*((b:ℝ)-1) ≤ (b:ℝ)*(b:ℝ) := by nlinarith
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hid : (b:ℝ)*(b:ℝ)*(((1-gamma)^N)^2) = ((b:ℝ)*(1-gamma)^N)^2 := by ring
  linarith [hL, hR, hid]

#print axioms unseen_card
#print axioms remaining_unsafe_card
#print axioms safe_unseen_card
#print axioms unseen_unsafe_iff
#print axioms uniform_unseen_error
#print axioms symmetric_posterior_value
#print axioms two_tip_miss_le_product
#print axioms missing_second_moment_bound

end
end CIGAMF.P13.SupportPassiveAnswerMultiplicity
