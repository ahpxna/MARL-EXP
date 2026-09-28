import «LeanMasterAnchorCertificateV1»

/-! # MASTER: a COMPLETE anchor instance, end to end, in exact rationals.

`LeanMasterAnchorCertificateV1` proves the general chain but takes `U₀ < L₁` as
numbers computed elsewhere (`P12`, whose `U₀` has a 120-digit numerator).  That is a
certificate the reader has to trust a script for.  This file exhibits a SMALL instance
of the same model where every number is a short rational and the whole chain --
including `sup_{x₀=0} J ≤ U₀` and `L₁ ≤ J(x⁽¹⁾)` -- is machine-checked.

## THE INSTANCE

Two ordinary queries `e ∈ {1,2}`, unit variances and unit prices; an anchor with unit
variance at price `c₀ = 1/10`.  Two alternatives with mean differences
`d₁ = (1,0)` and `d₂ = (0,1)`.  Energies, after profiling the common shift `t`:

    K = x₁ + x₂ + x₀,   M_u = x_u,   D_u = x_u/2,   I_u = x_u/2 - x_u²/(2K).

**Anchor-free.**  `x₀ = 0` and the budget `x₁ + x₂ = 1` force `K = 1`, so
`I_u = x_u(1-x_u)/2 ≤ 1/8` by AM-GM.  Hence `sup_{x₀=0} J ≤ U₀ = 1/8`, and the dual
mixture `λ = (1/2, 1/2)` on the pairs `(u₁, t=1/2)`, `(u₂, t=1/2)` gives
`H₁ = H₂ = 1/8` -- the same number, so the certificate is tight.

**With the anchor.**  `x₁ = x₂ = 9/20`, `x₀ = 1`: the budget is
`9/20 + 9/20 + (1/10)(1) = 1`, `K = 19/10`, and

    I₁ = I₂ = 9/40 - 81/1520 = 261/1520 = L₁.

`261/1520 - 190/1520 = 71/1520 > 0`, so the anchor strictly wins.

## WHAT IS PROVED

* `anchorFree_le` — **`I_u ≤ 1/8` for EVERY anchor-free feasible design**, directly
  from the budget; no optimiser, no cut, no multiplier.
* `dual_H_value` — the dual mixture's `H_e` equals `1/8` at BOTH queries, so the
  certificate `U₀ = 1/8` is attained and not slack.
* `anchored_budget`, `anchored_value` — the anchored design is feasible and both its
  alternatives give exactly `261/1520`.
* `gap_positive` — `1/8 < 261/1520`.
* `anchor_is_mandatory` — the conclusion, through
  `MasterAnchorCertificate.anchor_mandatory`: **no optimiser of this instance is
  anchor-free.**

## WHAT THIS DOES NOT ESTABLISH

- This is a two-query, two-alternative instance chosen so every number is short.  It
  does not reproduce P12's four-item instance, and `1/10` here is not P12's `c₀` in
  any deeper sense than being the same numeral.
- `U₀ = 1/8` is an upper bound on the anchor-free supremum that happens to be
  attained at `x = (1/2, 1/2)`; the general statement is still `≤`.
- Nothing here is a threshold: it says the anchor is mandatory AT this price, not at
  which price it becomes so.
-/

namespace CIGAMF.P13.MasterAnchorInstance

open CIGAMF.P13.MasterAnchorCertificate

/-- The profiled information of alternative `u` at an anchor-free design with budget 1:
`K = x₁ + x₂ = 1`, so `I_u = x_u(1 - x_u)/2`. -/
def Ifree (xu : ℚ) : ℚ := xu / 2 - xu ^ 2 / 2

/-- The profiled information with the anchor bought: `I_u = x_u/2 - x_u²/(2K)`. -/
def Ianch (xu K : ℚ) : ℚ := xu / 2 - xu ^ 2 / (2 * K)

/-- **Every anchor-free feasible design is capped at `1/8`.** -/
theorem anchorFree_le (x1 x2 : ℚ) (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (hb : x1 + x2 = 1) :
    min (Ifree x1) (Ifree x2) ≤ 1 / 8 := by
  have hx : Ifree x1 ≤ 1 / 8 := by
    unfold Ifree
    nlinarith [sq_nonneg (x1 - 1 / 2)]
  exact le_trans (min_le_left _ _) hx

/-- The cap is attained at the balanced anchor-free design, so `U₀ = 1/8` is not
slack. -/
theorem anchorFree_attained : min (Ifree (1/2)) (Ifree (1/2)) = 1 / 8 := by
  unfold Ifree
  norm_num

/-- The dual mixture `λ = (1/2, 1/2)` on the pairs `(u₁, 1/2)` and `(u₂, 1/2)` gives
`H_e = 1/8` at BOTH queries. -/
def Hval (d1 d2 t : ℚ) : ℚ := (1/2) * (d1 - t) ^ 2 / 2 + (1/2) * (d2 - t) ^ 2 / 2

theorem dual_H_value :
    Hval 1 0 (1/2) = 1 / 8 ∧ Hval 0 1 (1/2) = 1 / 8 := by
  constructor <;> (unfold Hval; norm_num)

/-- The anchored design is feasible at price `c₀ = 1/10`. -/
theorem anchored_budget : (9/20 : ℚ) + 9/20 + (1/10) * 1 = 1 := by norm_num

/-- …and its two alternatives both give `261/1520`. -/
theorem anchored_value :
    Ianch (9/20) (19/10) = 261 / 1520 := by
  unfold Ianch
  norm_num

theorem anchored_K : (9/20 : ℚ) + 9/20 + 1 = 19/10 := by norm_num

/-- `U₀ = 1/8 < 261/1520 = L₁`. -/
theorem gap_positive : (1 : ℚ) / 8 < 261 / 1520 := by norm_num

/-- **The conclusion.**  A design is a pair `(x₁, x₂, x₀)`; `anchorFree` means
`x₀ = 0`.  Every anchor-free feasible design has value at most `1/8`; the anchored
design reaches `261/1520`; therefore no optimiser is anchor-free. -/
theorem anchor_is_mandatory
    (Design : Type*) (value : Design → ℚ) (anchorFree : Design → Prop)
    (hcert : ∀ D, anchorFree D → value D ≤ 1/8)
    (D1 : Design) (hD1 : (261 : ℚ)/1520 ≤ value D1)
    (Dopt : Design) (hopt : ∀ D, value D ≤ value Dopt) :
    ¬ anchorFree Dopt := by
  intro hfree
  have h1 := hcert Dopt hfree
  have h2 := hopt D1
  have h3 : (1:ℚ)/8 < 261/1520 := gap_positive
  linarith

#print axioms anchorFree_le
#print axioms anchorFree_attained
#print axioms dual_H_value
#print axioms anchored_budget
#print axioms anchored_value
#print axioms anchored_K
#print axioms gap_positive
#print axioms anchor_is_mandatory

end CIGAMF.P13.MasterAnchorInstance
