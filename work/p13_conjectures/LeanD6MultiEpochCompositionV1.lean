import Mathlib

/-! # What splitting into epochs costs

`LeanD6BudgetRegretTradeoffV1` bounds ONE epoch against a total budget.  The
adaptive algorithm runs many, because revalidation and tracking need them, so
the next question is what the composition costs.

This module answers the arithmetic half exactly.  Writing `epochBound q V` for
the one-epoch estimation bound at usable budget `V`, splitting a total usable
budget `T` across a finite set of epochs gives

  `card^2 * epochBound q T  <=  sum of epochBound q (U i)`,

with equality exactly at the equal split.  So `E` epochs cost `E^2` times one
epoch at the same total budget: the penalty is quadratic in the number of
epochs, not linear, and no allocation across epochs avoids it.  The escalating
revalidation term goes the other way and sums geometrically: with `s_e = s0+e`
rounds, the whole wrong-label series is at most `(4/3)` times its first term.

Together (`multi_epoch_total`): at the equal split,

  `sum_e [ estimation + label ]  <=  E^2 * epochBound q T + (4/3)*W*4^(-s0)`.

The mechanism of the `E^2` is elementary and worth naming: the estimation bound
is proportional to `1/U`, and `sum 1/U_i` is minimised, subject to `sum U_i = T`,
at `U_i = T/E`, where it equals `E^2/T`.  The proof uses the tangent line to
`1/x` at `T/E` rather than any inequality by name, so it is self-contained.

## What this does NOT establish

`split_penalty` bounds a SUM OF PER-EPOCH BOUNDS, not the regret of an adaptive
algorithm.  Summing the per-epoch expectations of
`LeanD6GrowingUnknownLabelPhaseRiskV1` requires that bound to hold CONDITIONALLY
on the history of earlier epochs -- a tower-property argument on a filtration
that does not exist yet in this corpus, since the existing theorem is stated for
one epoch on a fixed product measure.  Until that is built, the inequalities
here say what the composition WOULD cost, not what an adaptive run does cost.

Also absent, and not to be read in: phase-interval learning and boundary
crossings, the discovery/cyclic cost accounting across epochs, expected stopping
time, and the `Gamma` rate.  The `E^2` law is a reason to keep the epoch count
small, not a termination theorem.
-/
namespace CIGAMF.P13.D6MultiEpochComposition
open scoped BigOperators
open Finset
noncomputable section

/-- One-epoch estimation bound at usable budget `V`, from
`LeanD6BudgetRegretTradeoffV1.budget_regret_tradeoff`. -/
def epochBound (q V : ℝ) : ℝ := 128*(2*q+1)^2/(V*q^6)

/-- The tangent line to `1/x` at `1/a` lies below it on the positive reals.
This is the whole content of the splitting law; `(a*x-1)^2 >= 0` is the proof. -/
lemma tangent_inv (x a : ℝ) (hx : 0 < x) : 2*a-a^2*x ≤ 1/x := by
  rw [le_div_iff₀ hx]
  nlinarith [sq_nonneg (a*x-1)]

/-- Subject to a fixed total, the sum of reciprocals is at least `card^2/T`. -/
theorem split_penalty {ι : Type*} (s : Finset ι) (U : ι → ℝ)
    (hU : ∀ i ∈ s, 0 < U i) (T : ℝ) (hT : 0 < T) (hsum : ∑ i ∈ s, U i = T) :
    ((s.card : ℝ))^2/T ≤ ∑ i ∈ s, 1/U i := by
  have hTne : T ≠ 0 := hT.ne'
  have key : ∀ i ∈ s, 2*((s.card:ℝ)/T)-((s.card:ℝ)/T)^2*U i ≤ 1/U i := by
    intro i hi
    exact tangent_inv (U i) ((s.card:ℝ)/T) (hU i hi)
  have h := Finset.sum_le_sum key
  have hl : ∑ i ∈ s, (2*((s.card:ℝ)/T)-((s.card:ℝ)/T)^2*U i) = ((s.card:ℝ))^2/T := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum, hsum, nsmul_eq_mul]
    field_simp <;> ring
  rwa [hl] at h

/-- The equal split attains it, so the bound of `split_penalty` is sharp. -/
theorem equal_split_sum {ι : Type*} (s : Finset ι) (T : ℝ) (hT : 0 < T)
    (hc : 0 < s.card) :
    ∑ _i ∈ s, 1/(T/(s.card:ℝ)) = ((s.card:ℝ))^2/T := by
  have hcR : (0:ℝ) < (s.card:ℝ) := by exact_mod_cast hc
  have hcne : (s.card:ℝ) ≠ 0 := hcR.ne'
  have hTne : T ≠ 0 := hT.ne'
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp <;> ring

/-- `E` epochs cost `E^2` times one epoch at the same total usable budget, and
no allocation across epochs does better.  This is optimality of the BOUND over
splits, not a lower bound on regret. -/
theorem epoch_split_law {ι : Type*} (s : Finset ι) (U : ι → ℝ)
    (hU : ∀ i ∈ s, 0 < U i) (T q : ℝ) (hq : 8 ≤ q) (hT : 0 < T)
    (hsum : ∑ i ∈ s, U i = T) :
    ((s.card:ℝ))^2*epochBound q T ≤ ∑ i ∈ s, epochBound q (U i) := by
  have hq0 : (0:ℝ) < q := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  have hq6 : (0:ℝ) < q^6 := pow_pos hq0 6
  have hTne : T ≠ 0 := hT.ne'
  have hK : (0:ℝ) ≤ 128*(2*q+1)^2/q^6 := by
    apply div_nonneg _ hq6.le
    nlinarith [sq_nonneg (2*q+1)]
  have hsp := split_penalty s U hU T hT hsum
  have hsum2 : ∑ i ∈ s, epochBound q (U i)
      = (128*(2*q+1)^2/q^6)*∑ i ∈ s, 1/U i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hUi : U i ≠ 0 := (hU i hi).ne'
    unfold epochBound
    field_simp <;> ring
  have hb : epochBound q T = (128*(2*q+1)^2/q^6)*(1/T) := by
    unfold epochBound; field_simp <;> ring
  rw [hsum2, hb]
  calc ((s.card:ℝ))^2*((128*(2*q+1)^2/q^6)*(1/T))
      = (128*(2*q+1)^2/q^6)*(((s.card:ℝ))^2/T) := by ring
    _ ≤ (128*(2*q+1)^2/q^6)*∑ i ∈ s, 1/U i := mul_le_mul_of_nonneg_left hsp hK

/-! ## The revalidation series goes the other way -/

theorem quarter_geom (E : ℕ) :
    ∑ e ∈ Finset.range E, ((1:ℝ)/4)^e = (4/3)*(1-((1:ℝ)/4)^E) := by
  induction E with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-- Escalating the revalidation rounds as `s_e = s0+e` makes the whole
wrong-label series at most `4/3` times its first term, for every horizon. -/
theorem escalating_label_total (W : ℝ) (hW : 0 ≤ W) (s0 E : ℕ) :
    ∑ e ∈ Finset.range E, W/(4:ℝ)^(s0+e) ≤ (4/3)*(W/(4:ℝ)^s0) := by
  have h4 : (0:ℝ) < (4:ℝ)^s0 := by positivity
  have hc : 0 ≤ W/(4:ℝ)^s0 := div_nonneg hW h4.le
  have hrw : ∑ e ∈ Finset.range E, W/(4:ℝ)^(s0+e)
      = (W/(4:ℝ)^s0)*∑ e ∈ Finset.range E, ((1:ℝ)/4)^e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [pow_add, div_pow]
    field_simp <;> ring
  rw [hrw, quarter_geom]
  have hx : (0:ℝ) ≤ ((1:ℝ)/4)^E := by positivity
  nlinarith [hc, hx]

/-! ## The composition, at the equal split -/

/-- Total over `E` equal epochs: the estimation half pays `E^2`, the
revalidation half is a convergent series. -/
theorem multi_epoch_total (E : ℕ) (hE : 0 < E) (q T W : ℝ) (hq : 8 ≤ q)
    (hT : 0 < T) (hW : 0 ≤ W) (s0 : ℕ) :
    ∑ e ∈ Finset.range E, (epochBound q (T/(E:ℝ))+W/(4:ℝ)^(s0+e))
      ≤ (E:ℝ)^2*epochBound q T+(4/3)*(W/(4:ℝ)^s0) := by
  have hER : (0:ℝ) < (E:ℝ) := by exact_mod_cast hE
  have hEne : (E:ℝ) ≠ 0 := hER.ne'
  have hq0 : (0:ℝ) < q := by linarith
  have hqne : q ≠ 0 := hq0.ne'
  have hTne : T ≠ 0 := hT.ne'
  rw [Finset.sum_add_distrib]
  have hest : ∑ _e ∈ Finset.range E, epochBound q (T/(E:ℝ))
      = (E:ℝ)^2*epochBound q T := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    unfold epochBound
    field_simp <;> ring
  rw [hest]
  have hlab := escalating_label_total W hW s0 E
  linarith

#print axioms tangent_inv
#print axioms split_penalty
#print axioms equal_split_sum
#print axioms epoch_split_law
#print axioms quarter_geom
#print axioms escalating_label_total
#print axioms multi_epoch_total
end
end CIGAMF.P13.D6MultiEpochComposition
