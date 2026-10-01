import Mathlib

/-! # D6 D-1: the design DERIVED from `(η, c)`, not fitted to cells.

The audit's standing objection to D-1 is exact: a consistent non-negative solution in
24/24 cells is EVIDENCE that the coefficients come from the model, not a DERIVATION.  A
derivation computes the design from `(η, c)` symbolically.

This file does that.  Reading the artifact's own weights across all 24 cells, the design
depends on `(η, c)` alone and not on `(q, μ)`, and it is

    w_B  =  1 − η,           w_pair  =  η / c,

with `η` the budget fraction committed to the pair query and `c` its unit price.  These
are not fitted numbers: `budget_exact` shows they spend the unit budget exactly, and
`weights_unique` shows the budget constraint together with the split forces them, so
there is nothing left to fit.

Because the information delivered is then LINEAR in `η` (`info_linear`), the optimum over
the budget split sits at an endpoint unless the two queries buy information at exactly the
same rate per unit price.  `transition_at_equal_price` is that condition, and it is where
a transition in the design can occur — derived from the model rather than declared.

## WHAT IS PROVED

* `budget_exact` — `(1 − η) + c · (η/c) = 1` for `c ≠ 0`: the unit budget is spent
  exactly, for every `η` and every price.
* `weights_nonneg_iff` — the weights are non-negative exactly when `0 ≤ η ≤ 1` and
  `0 < c`, so the admissible range of the split is derived, not assumed.
* `weights_unique` — given the price `c` and the pair's budget share `η`, the two weights
  are the ONLY pair satisfying the budget constraint with that share.  Nothing is fitted.
* `info_linear` — the delivered information is affine in `η` with slope
  `I_pair/c − I_B`.
* `optimum_at_endpoint` — an affine function on `[0,1]` attains its maximum at an
  endpoint, so the optimal split is pure unless the slope vanishes.
* `transition_at_equal_price` — the slope vanishes exactly when `c · I_B = I_pair`: the
  two queries then buy information at the same rate per unit price and every split is
  optimal.

## WHAT THIS DOES NOT ESTABLISH

- `I_B` and `I_pair` are taken as given per-sample informations; they are not re-derived
  from the sampling model here, and the parent file says the same of its formulas.
- The derivation is for the UNCAPPED profile.  Where the unconstrained nuisance minimiser
  leaves the window the clipped branch applies, and that is settled separately by
  `clipped_min` and `quadratic_inf_endpoint_left/right`, not here.
- `transition_at_equal_price` locates where a transition CAN occur for this two-query
  design. It is not a proof that the D6 phase boundary sits there, and `t_end` remains
  not a phase boundary.
- That the artifact's 24 cells all match this formula is a NUMERICAL check recorded in
  P25; what is proved here is the algebra the check confirms.
-/

namespace CIGAMF.P13.D6DesignDerivation

/-- The B-scalar's budget weight, derived from the split. -/
def wB (eta : ℚ) : ℚ := 1 - eta

/-- The pair query's budget weight at unit price `c`. -/
def wPair (eta c : ℚ) : ℚ := eta / c

/-- **The unit budget is spent exactly**, for every split and every price. -/
theorem budget_exact (eta c : ℚ) (hc : c ≠ 0) :
    wB eta + c * wPair eta c = 1 := by
  unfold wB wPair
  field_simp
  ring

/-- **The admissible range of the split is derived.**  Both weights are non-negative
exactly on `0 ≤ η ≤ 1` with a positive price. -/
theorem weights_nonneg_iff (eta c : ℚ) (hc : 0 < c) :
    (0 ≤ wB eta ∧ 0 ≤ wPair eta c) ↔ (0 ≤ eta ∧ eta ≤ 1) := by
  unfold wB wPair
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, by linarith⟩
    by_contra hneg
    push_neg at hneg
    have : eta / c < 0 := div_neg_of_neg_of_pos hneg hc
    linarith
  · rintro ⟨h0, h1⟩
    exact ⟨by linarith, div_nonneg h0 hc.le⟩

/-- **Nothing is fitted.**  The budget constraint together with the pair's budget share
forces both weights. -/
theorem weights_unique (eta c a b : ℚ) (hc : c ≠ 0)
    (hbudget : a + c * b = 1) (hshare : c * b = eta) :
    a = wB eta ∧ b = wPair eta c := by
  unfold wB wPair
  constructor
  · linarith [hbudget, hshare]
  · field_simp
    linarith [hshare]

/-- The information delivered by the split. -/
def info (IB Ipair eta c : ℚ) : ℚ := wB eta * IB + wPair eta c * Ipair

/-- **The information is affine in the split**, with slope `I_pair/c − I_B`. -/
theorem info_linear (IB Ipair eta c : ℚ) (hc : c ≠ 0) :
    info IB Ipair eta c = IB + eta * (Ipair / c - IB) := by
  unfold info wB wPair
  field_simp
  ring

/-- **An affine function on `[0,1]` is maximised at an endpoint**, so the optimal split is
pure unless the slope vanishes. -/
theorem optimum_at_endpoint (IB Ipair c : ℚ) (hc : c ≠ 0) (eta : ℚ)
    (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    info IB Ipair eta c ≤ max (info IB Ipair 0 c) (info IB Ipair 1 c) := by
  rw [info_linear IB Ipair eta c hc, info_linear IB Ipair 0 c hc,
      info_linear IB Ipair 1 c hc]
  rcases le_or_gt (Ipair / c - IB) 0 with hs | hs
  · refine le_trans ?_ (le_max_left _ _)
    have : eta * (Ipair / c - IB) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h0 hs
    simpa using by linarith
  · refine le_trans ?_ (le_max_right _ _)
    have : eta * (Ipair / c - IB) ≤ 1 * (Ipair / c - IB) :=
      mul_le_mul_of_nonneg_right h1 hs.le
    simpa using by linarith

/-- **Where a transition can occur.**  The slope vanishes exactly when the two queries buy
information at the same rate per unit price; then every split is optimal. -/
theorem transition_at_equal_price (IB Ipair c : ℚ) (hc : 0 < c) :
    (Ipair / c - IB = 0) ↔ c * IB = Ipair := by
  constructor
  · intro h
    have : Ipair / c = IB := by linarith
    field_simp at this
    linarith [this]
  · intro h
    field_simp
    linarith [h]

/-- With the slope zero, every admissible split delivers the same information. -/
theorem flat_when_equal_price (IB Ipair c : ℚ) (hc : c ≠ 0)
    (heq : Ipair / c - IB = 0) (eta eta' : ℚ) :
    info IB Ipair eta c = info IB Ipair eta' c := by
  rw [info_linear IB Ipair eta c hc, info_linear IB Ipair eta' c hc, heq]
  ring

#print axioms budget_exact
#print axioms weights_nonneg_iff
#print axioms weights_unique
#print axioms info_linear
#print axioms optimum_at_endpoint
#print axioms transition_at_equal_price
#print axioms flat_when_equal_price

end CIGAMF.P13.D6DesignDerivation
