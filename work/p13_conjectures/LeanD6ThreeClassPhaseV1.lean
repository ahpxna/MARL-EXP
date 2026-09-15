import Mathlib

/-! # D6: the A-pair class, and why the new phase has to exist.

`scripts/P1_d6_phase_law.py` found that the scalar/pair certificate is not universal:
the binding dual orbit is ALWAYS `(s,t,b) = (2,0,0)` -- a width-2 query on two
coordinates of `A` -- and its slack changes sign at `T_c(mu)`, strictly below
`t_end`.  `scripts/P7_d6_full_design.py` then solved the whole design space and found
the two-phase law: below `T_c` the optimal support is `{scalar B, B-pair}`, above it
the support is `{B-pair, A-pair}` and the two-class value is strictly beaten.

THE ALGEBRA OF THE A-PAIR.  For a query class `(s,t,b)` the per-sample information
against the alternative at exchange distance `d` and nuisance `x = nu - mu` is
    I = [ x^2 ((t-b)^2 + 2(t-b) E u + E u^2) - 2 g x ((t-b) E u + E u^2) + g^2 E u^2 ]/2,
with `u = l - m`, `l ~ Hyp(q+1, d, s)`, `m ~ Hyp(q, d, t)`.  For the A-pair,
`t = b = 0`, so `t - b = 0` and the whole thing collapses to a PERFECT SQUARE:
    I_A(d, x) = cA(q,d) * (g - x)^2 / 2,     cA(q,d) = E[l^2],
and `E[l^2]` for `l ~ Hyp(q+1, d, 2)` is, after clearing denominators,
    cA(q,d) = (2(q^2-1) d + 2(q+1) d^2) / ((q+1)^2 q).
That closed form is checked against the hypergeometric moments in
`P7_d6_full_design.py` PART 0, by brute-force enumeration over actual coordinate
subsets and actual alternative labels.

## WHAT IS PROVED

* `cA_pos` — the coefficient is strictly positive for `1 ≤ d ≤ q`, `3 ≤ q`; the
  A-pair is never blind.
* `cA_mono` — it is increasing in `d`, with the exact difference
  `cA(d₂) - cA(d₁) = (d₂-d₁)(2(q²-1) + 2(q+1)(d₁+d₂))/((q+1)²q)`.
* `IA_binds_at_one` — hence the A-pair's worst alternative is `d = 1`, exactly as the
  scalar/pair family's is: the new class does not move the binding distance.
* `IA_eq_zero_iff` — the A-pair's information vanishes ONLY on the line `x = g`,
  i.e. `nu = 1`.  The B-scalar vanishes at `x = 0`.  The two classes therefore have
  DISJOINT blind directions, which is the structural reason a mixture of them can
  beat either alone.
* `mixture_positive` — and so any strictly positive mixture of the A-pair with a
  class that is positive at `x = g` is strictly positive at every legal `x`.

## WHAT THIS DOES NOT ESTABLISH

- The VALUE of the new phase, and the location of `T_c`, are numerical
  (`P7_d6_full_design.py`, certified there by a rational primal/dual pair).  Nothing
  here computes the optimum or proves the phase boundary.
- `cA` is transcribed and checked by the script against brute-force enumeration; the
  bridge from the corpus's `mean_query` to this formula is not formalised.
- Everything is over `ℚ` with `q`, `d` rational parameters; integrality is never used.
-/

namespace CIGAMF.P13.D6ThreeClassPhase

noncomputable section

variable (Q dd g x : ℚ)

/-- `E[l^2]` for `l ~ Hypergeometric(q+1, d, 2)`, cleared. -/
def cA : ℚ := (2*(Q^2 - 1)*dd + 2*(Q + 1)*dd^2) / ((Q + 1)^2*Q)

/-- The A-pair's information: a perfect square in `g - x`. -/
def IA : ℚ := cA Q dd * (g - x)^2 / 2

theorem cA_pos (hq : 3 ≤ Q) (h1 : 1 ≤ dd) : 0 < cA Q dd := by
  have hQ0 : (0:ℚ) < Q := by linarith
  have hQ1 : (0:ℚ) < Q + 1 := by linarith
  have hden : (0:ℚ) < (Q + 1)^2*Q := by positivity
  have hnum : (0:ℚ) < 2*(Q^2 - 1)*dd + 2*(Q + 1)*dd^2 := by nlinarith
  unfold cA
  exact div_pos hnum hden

theorem cA_diff (hq : 3 ≤ Q) (d1 d2 : ℚ) :
    cA Q d2 - cA Q d1
      = (d2 - d1)*(2*(Q^2 - 1) + 2*(Q + 1)*(d1 + d2)) / ((Q + 1)^2*Q) := by
  have hQ0 : (Q:ℚ) ≠ 0 := by intro h; rw [h] at hq; norm_num at hq
  have hQ1 : (Q + 1:ℚ) ≠ 0 := by intro h; nlinarith [h]
  unfold cA
  field_simp
  ring

theorem cA_mono (hq : 3 ≤ Q) (d1 d2 : ℚ) (h1 : 1 ≤ d1) (h12 : d1 ≤ d2) :
    cA Q d1 ≤ cA Q d2 := by
  have hQ1 : (0:ℚ) < Q + 1 := by linarith
  have hden : (0:ℚ) < (Q + 1)^2*Q := by positivity
  have hd : (0:ℚ) ≤ d2 - d1 := by linarith
  have hQ2 : (0:ℚ) ≤ 2*(Q^2 - 1) := by nlinarith [hq]
  have hs : (0:ℚ) ≤ 2*(Q + 1)*(d1 + d2) :=
    mul_nonneg (by linarith) (by linarith)
  have hnum : 0 ≤ (d2 - d1)*(2*(Q^2 - 1) + 2*(Q + 1)*(d1 + d2)) :=
    mul_nonneg hd (by linarith)
  have := cA_diff Q hq d1 d2
  have hq0 : 0 ≤ (d2 - d1)*(2*(Q^2 - 1) + 2*(Q + 1)*(d1 + d2)) / ((Q + 1)^2*Q) :=
    div_nonneg hnum (le_of_lt hden)
  linarith [this, hq0]

/-- The A-pair's worst alternative is `d = 1`. -/
theorem IA_binds_at_one (hq : 3 ≤ Q) (h1 : 1 ≤ dd) :
    IA Q 1 g x ≤ IA Q dd g x := by
  have hm := cA_mono Q hq 1 dd le_rfl h1
  have hsq : (0:ℚ) ≤ (g - x)^2 := sq_nonneg _
  unfold IA
  have : cA Q 1 * (g - x)^2 ≤ cA Q dd * (g - x)^2 :=
    mul_le_mul_of_nonneg_right hm hsq
  linarith

theorem IA_nonneg (hq : 3 ≤ Q) (h1 : 1 ≤ dd) : 0 ≤ IA Q dd g x := by
  have := le_of_lt (cA_pos Q dd hq h1)
  unfold IA
  have : 0 ≤ cA Q dd * (g - x)^2 := mul_nonneg this (sq_nonneg _)
  linarith

/-- The A-pair is blind ONLY at `x = g`. -/
theorem IA_eq_zero_iff (hq : 3 ≤ Q) (h1 : 1 ≤ dd) :
    IA Q dd g x = 0 ↔ x = g := by
  have hc := cA_pos Q dd hq h1
  unfold IA
  constructor
  · intro h
    have h2 : cA Q dd * (g - x)^2 = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 (ne_of_gt hc)
    · have : g - x = 0 := by
        have := sq_eq_zero_iff.mp h3
        exact this
      linarith
  · intro h
    rw [h]
    ring

/-- Disjoint blind directions: a positive mixture is positive everywhere the OTHER
class is positive at `x = g`. -/
theorem mixture_positive (wA wB other : ℚ) (hq : 3 ≤ Q) (h1 : 1 ≤ dd)
    (hwA : 0 < wA) (hwB : 0 < wB) (hother : 0 ≤ other)
    (hpos : x = g → 0 < other) :
    0 < wA * IA Q dd g x + wB * other := by
  by_cases hx : x = g
  · have := hpos hx
    have h0 : 0 ≤ wA * IA Q dd g x :=
      mul_nonneg (le_of_lt hwA) (IA_nonneg Q dd g x hq h1)
    nlinarith
  · have hne : g - x ≠ 0 := fun h => hx (by linarith [sub_eq_zero.mp h])
    have hc := cA_pos Q dd hq h1
    have hsq : 0 < (g - x)^2 := by positivity
    have : 0 < IA Q dd g x := by
      unfold IA
      have : 0 < cA Q dd * (g - x)^2 := mul_pos hc hsq
      linarith
    nlinarith [mul_nonneg (le_of_lt hwB) hother]

#print axioms cA_pos
#print axioms cA_diff
#print axioms cA_mono
#print axioms IA_binds_at_one
#print axioms IA_nonneg
#print axioms IA_eq_zero_iff
#print axioms mixture_positive

end
end CIGAMF.P13.D6ThreeClassPhase
