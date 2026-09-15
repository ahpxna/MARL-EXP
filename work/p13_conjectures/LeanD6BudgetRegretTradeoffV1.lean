import Mathlib

/-! # One-epoch regret against TOTAL acquisition budget

`LeanD6GrowingUnknownLabelPhaseRiskV1.actual_unknown_label_explicit_bound`
bounds the expected one-epoch loss by

  `64*(2q+1)/(L*q^6) + V * eta * 4^(-s)`,

but says nothing about what the epoch costs.  The construction spends
`4*(2q+1)*r0*(s+1)` discovery queries and `(2q+1)*L` cyclic queries, so a bound
stated in `L` alone is not a statement about a budget.  Reading such a bound as
"matching" would repeat the scale error retracted in D6 Section 173.

This module is the arithmetic layer converting the two free parameters into one
budget `N`.  It is deliberately free of measure theory: every quantity is a real
number, and composing these inequalities with the expectation bound above is a
separate step, kept separate so that a failure localises.

Proved here:
* `estimation_budget_bound` -- when `L` is the largest cyclic block the budget
  allows after paying for `s` revalidation rounds, the estimation term is at
  most `64*(2q+1)^2 / ((N - discovery - (2q+1)) * q^6)`.
* `label_term_small` -- an explicit threshold on `4^s` making the wrong-label
  term no larger than the estimation term.  This is the design choice "spend
  enough revalidation rounds", with the threshold named rather than assumed.
* `budget_regret_tradeoff` -- the two together: total one-epoch regret at most
  `128*(2q+1)^2 / ((N - discovery - (2q+1)) * q^6)`.
* `budget_regret_eventually_small` -- that bound falls below any tolerance once
  the usable budget passes an explicit threshold.

NOT proved, and not to be read into it: this is still ONE epoch consuming the
whole budget, with the phase-III interval known.  It is not a multi-epoch
schedule, not an adaptive policy, and not a matching lower bound.  The `-(2q+1)`
is the rounding loss from an integer number of cyclic blocks, the same charge
the `+2` of `LeanD6IntegerBlockAllocationV1.d6_exchange` pays.
-/
namespace CIGAMF.P13.D6BudgetRegretTradeoff
noncomputable section

/-- Acquisition cost of one epoch: discovery plus cyclic queries. -/
def epochCost (q r0 : ℝ) (s : ℕ) (L : ℝ) : ℝ := 4*(2*q+1)*r0*((s:ℝ)+1)+(2*q+1)*L

/-- Budget left for cyclic blocks, after discovery and one block of rounding. -/
def usableBudget (q r0 : ℝ) (s : ℕ) (N : ℝ) : ℝ :=
  N-4*(2*q+1)*r0*((s:ℝ)+1)-(2*q+1)

/-- The estimation half of the one-epoch bound. -/
def estimationTerm (q L : ℝ) : ℝ := 64*(2*q+1)/(L*q^6)

lemma usable_lt (q r0 : ℝ) (s : ℕ) (L N : ℝ)
    (hgreedy : N < epochCost q r0 s (L+1)) :
    usableBudget q r0 s N < (2*q+1)*L := by
  unfold usableBudget epochCost at *
  nlinarith [hgreedy]

/-- Spending the whole budget on cyclic blocks converts the `1/L` rate into a
`1/N` rate, with the block size `(2q+1)` appearing squared. -/
theorem estimation_budget_bound (q r0 : ℝ) (s : ℕ) (L N : ℝ) (hq : 8 ≤ q)
    (hL : 0 < L) (hgreedy : N < epochCost q r0 s (L+1))
    (hpos : 0 < usableBudget q r0 s N) :
    estimationTerm q L ≤ 64*(2*q+1)^2/(usableBudget q r0 s N*q^6) := by
  have hq0 : (0:ℝ) < q := by linarith
  have hq6 : (0:ℝ) < q^6 := pow_pos hq0 6
  have hLq : (0:ℝ) < L*q^6 := mul_pos hL hq6
  have hDq : (0:ℝ) < usableBudget q r0 s N*q^6 := mul_pos hpos hq6
  have h1 := usable_lt q r0 s L N hgreedy
  have hmul : 64*(2*q+1)*q^6*usableBudget q r0 s N
      ≤ 64*(2*q+1)*q^6*((2*q+1)*L) :=
    mul_le_mul_of_nonneg_left h1.le
      (mul_nonneg (by linarith : (0:ℝ) ≤ 64*(2*q+1)) hq6.le)
  unfold estimationTerm
  rw [div_le_iff₀ hLq, div_mul_eq_mul_div, le_div_iff₀ hDq]
  nlinarith [hmul]

/-- Enough revalidation rounds make the wrong-label term no larger than the
estimation term.  The threshold is explicit: `4^s >= V*eta*L*q^6/(64*(2q+1))`.
No sign hypothesis on `V` or `eta` is needed; the step only multiplies through
by positive quantities. -/
theorem label_term_small (q L : ℝ) (s : ℕ) (V eta : ℝ) (hq : 8 ≤ q) (hL : 0 < L)
    (hthresh : V*eta*(L*q^6) ≤ 64*(2*q+1)*(4:ℝ)^s) :
    V*eta/(4:ℝ)^s ≤ estimationTerm q L := by
  have hq0 : (0:ℝ) < q := by linarith
  have hLq : (0:ℝ) < L*q^6 := mul_pos hL (pow_pos hq0 6)
  have h4 : (0:ℝ) < (4:ℝ)^s := by positivity
  unfold estimationTerm
  rw [div_le_iff₀ h4, div_mul_eq_mul_div, le_div_iff₀ hLq]
  nlinarith [hthresh]

/-- Total one-epoch regret as a function of the TOTAL acquisition budget, with
discovery and rounding charged.  Both halves are bounded by the same quantity,
so the total is twice it. -/
theorem budget_regret_tradeoff (q r0 : ℝ) (s : ℕ) (L N V eta : ℝ) (hq : 8 ≤ q)
    (hL : 0 < L) (hgreedy : N < epochCost q r0 s (L+1))
    (hpos : 0 < usableBudget q r0 s N)
    (hthresh : V*eta*(L*q^6) ≤ 64*(2*q+1)*(4:ℝ)^s) :
    estimationTerm q L+V*eta/(4:ℝ)^s
      ≤ 128*(2*q+1)^2/(usableBudget q r0 s N*q^6) := by
  have h2 := estimation_budget_bound q r0 s L N hq hL hgreedy hpos
  have h3 := label_term_small q L s V eta hq hL hthresh
  have hhalf : 128*(2*q+1)^2/(usableBudget q r0 s N*q^6)
      = 2*(64*(2*q+1)^2/(usableBudget q r0 s N*q^6)) := by ring
  rw [hhalf]
  linarith

/-- The budget form vanishes: past an explicit usable-budget threshold the whole
one-epoch regret is below any prescribed tolerance, at fixed `q`, `r0` and `s`. -/
theorem budget_regret_eventually_small (q r0 : ℝ) (s : ℕ) (V eta tol : ℝ)
    (hq : 8 ≤ q) (htol : 0 < tol) :
    ∃ B : ℝ, ∀ L N : ℝ, 0 < L → N < epochCost q r0 s (L+1) →
      0 < usableBudget q r0 s N → B ≤ usableBudget q r0 s N →
      V*eta*(L*q^6) ≤ 64*(2*q+1)*(4:ℝ)^s →
      estimationTerm q L+V*eta/(4:ℝ)^s ≤ tol := by
  have hq0 : (0:ℝ) < q := by linarith
  have hq6 : (0:ℝ) < q^6 := pow_pos hq0 6
  refine ⟨128*(2*q+1)^2/(tol*q^6),?_⟩
  intro L N hL hgreedy hpos hB hthresh
  refine (budget_regret_tradeoff q r0 s L N V eta hq hL hgreedy hpos hthresh).trans ?_
  have hDq : (0:ℝ) < usableBudget q r0 s N*q^6 := mul_pos hpos hq6
  have hb := (div_le_iff₀ (mul_pos htol hq6)).mp hB
  rw [div_le_iff₀ hDq]
  nlinarith [hb]

#print axioms usable_lt
#print axioms estimation_budget_bound
#print axioms label_term_small
#print axioms budget_regret_tradeoff
#print axioms budget_regret_eventually_small
end
end CIGAMF.P13.D6BudgetRegretTradeoff
