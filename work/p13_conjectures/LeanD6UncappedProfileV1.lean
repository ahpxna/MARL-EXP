import Mathlib

/-! # D6: the profile identity that REPLACES the cap.

The old proof of the width-transition lower bound ruled out exchange distances `d ≥ 2`
by restricting the design parameter to `eta ≤ cap`. `scripts/D8_uncapped_design.py`
shows that `cap` is not a legality constraint: at `(q, mu, h) = (8, 1/4, 1/10)` the
uncapped optimum sits at `eta* ≈ 0.6472 > cap ≈ 0.4827`, and a design there beats the
capped certificate by `+1.256e-5` in exact rationals. So the cap has to go, and this
file supplies the algebra that removes it.

THE OBJECTS. With `g = 1 - mu`, `c > 0` the pair charge and `x = nu - mu`, the
information of the scalar/pair design at exchange distance `d` is the quadratic
`A d * x^2 + 2 * B d * x + C d`, and profiling the nuisance over all of `ℝ` gives `P d`.
These are transcribed here and are checked against the corpus's own `general_poly` in
`D8_uncapped_design.py` on 7800 exact evaluations.

WHAT IS PROVED
* `Dd_pos` — the shared denominator is strictly positive on `q ≥ 3`, `1 ≤ d ≤ q`,
  `0 ≤ eta ≤ 1`, `0 < c`. Nothing below is vacuous.
* `profile_gap_factorization` — THE IDENTITY:
      `P d - d * P 1
         = d * eta * g^2 * (d-1) * (c(1-eta) + 4 eta) * (c(1-eta)(q-1) + 2 eta (q-2))
           / (c * q * D 1 * D d)`.
* `profile_gap_nonneg` — hence `d * P 1 ≤ P d`.
* `P1_nonneg` — `0 ≤ P 1`.
* `distance_one_active` — hence `P 1 ≤ P d` for every `1 ≤ d ≤ q`: distance one is the
  active alternative, with NO constraint on `eta` beyond `0 ≤ eta ≤ 1`.
* `quadratic_ge_profile` — `A d x^2 + 2 B d x + C d ≥ P d` for every real `x`, both for
  `d < q` (complete the square) and for `d = q` (where `A = B = 0` and `P = C`).
* `value_ge_P1` — putting them together: the information against EVERY alternative
  `(d, x)` is at least `P 1`, uncapped.

## WHAT THIS DOES NOT ESTABLISH

- THE BRIDGE TO THE ACTUAL MEANS IS NOT HERE. `A d`, `B d`, `C d` are transcribed, and
  their agreement with the corpus's `general_poly` is checked by the script, not by
  Lean. Until that bridge is formalised, this file is algebra about the stated
  quadratic, not about the D6 construction.
- `P 1` is a LOWER bound. That it is ATTAINED needs the unconstrained minimiser
  `x = -2 eta g / D 1` to lie in the legal nuisance window `nu ∈ [0,1]`, i.e.
  `2 eta g / D 1 ≤ mu`. That side condition is NOT proved here; when it fails the
  clipped branch at `nu = 0` has to be used instead.
- Nothing here is about optimality of the scalar/pair family over all designs. That is
  the full-query dual, which lives in the script and is not formalised.
- Everything is over `ℚ`, and `q`, `d` are RATIONAL parameters with `3 ≤ q` and
  `1 ≤ d ≤ q`. Integrality is never used, so nothing is lost; it removes every
  `Nat.cast` from the algebra, which is what let `field_simp` close these identities
  at all.
-/

namespace CIGAMF.P13.D6UncappedProfile
noncomputable section

variable (Q dd c eta mu : ℚ)

/-- The shared denominator. -/
def Dd : ℚ := c * (1 - eta) * (Q - 1) + 2 * eta * (2 * Q - dd - 2)

/-- Coefficient of `x^2`. -/
def Ad : ℚ := (Q - dd) * Dd Q dd c eta / (2 * c * Q * (Q - 1))

/-- Half the coefficient of `x`. -/
def Bd : ℚ := eta * (1 - mu) * dd * (Q - dd) / (c * Q * (Q - 1))

/-- Constant term. -/
def Cd : ℚ :=
  (1 - eta) * dd * mu ^ 2 / (2 * Q)
    + eta * (1 - mu) ^ 2 * dd * (Q + dd - 2) / (c * Q * (Q - 1))

/-- The nuisance-profiled value, `C - B^2 / A`, written so that `dd = Q` is fine. -/
def Pd : ℚ :=
  Cd Q dd c eta mu
    - 2 * eta ^ 2 * (1 - mu) ^ 2 * dd ^ 2 * (Q - dd)
      / (c * Q * (Q - 1) * Dd Q dd c eta)

variable {Q dd c eta mu}

theorem Dd_pos (hq : 3 ≤ Q) (hd1 : 1 ≤ dd) (hdq : dd ≤ Q)
    (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) : 0 < Dd Q dd c eta := by
  have h2 : (1 : ℚ) ≤ 2 * Q - dd - 2 := by linarith
  have e2 : 0 ≤ 2 * eta * (2 * Q - dd - 2) := mul_nonneg (by linarith) (by linarith)
  rcases lt_or_eq_of_le h1 with he | he
  · have e1 : 0 < c * (1 - eta) * (Q - 1) :=
      mul_pos (mul_pos hc (by linarith)) (by linarith)
    unfold Dd; linarith
  · subst he; unfold Dd; linarith

/-- Step one: clear the denominators only. Here `Dd Q 1 c eta` and `Dd Q dd c eta` are
opaque ATOMS -- their definitions are not needed yet, and keeping them opaque is what
lets `field_simp` see the very hypotheses it was given. -/
theorem gap_times_denominator (hq : 3 ≤ Q) (hd1 : 1 ≤ dd) (hdq : dd ≤ Q)
    (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    (Pd Q dd c eta mu - dd * Pd Q 1 c eta mu)
      * (2 * c * Q * (Q - 1) * Dd Q 1 c eta * Dd Q dd c eta)
      = 2 * eta * (1 - mu) ^ 2 * dd
        * ((dd - 1) * Dd Q 1 c eta * Dd Q dd c eta
           - 2 * eta * dd * (Q - dd) * Dd Q 1 c eta
           + 2 * eta * (Q - 1) * Dd Q dd c eta) := by
  have hqne : Q ≠ 0 := by intro h; rw [h] at hq; linarith
  have hq1ne : Q - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hD1 : Dd Q 1 c eta ≠ 0 := ne_of_gt (Dd_pos hq le_rfl (by linarith) hc h0 h1)
  have hDd : Dd Q dd c eta ≠ 0 := ne_of_gt (Dd_pos hq hd1 hdq hc h0 h1)
  unfold Pd Cd
  field_simp
  ring

/-- Step two: the part that DOES need the definition of `Dd`, as a pure polynomial
identity. No division, so `ring` decides it. -/
theorem denominator_polynomial (Q dd c eta mu D1 Dv : ℚ)
    (hD1 : D1 = c * (1 - eta) * (Q - 1) + 2 * eta * (2 * Q - 1 - 2))
    (hDv : Dv = c * (1 - eta) * (Q - 1) + 2 * eta * (2 * Q - dd - 2)) :
    2 * eta * (1 - mu) ^ 2 * dd
      * ((dd - 1) * D1 * Dv - 2 * eta * dd * (Q - dd) * D1 + 2 * eta * (Q - 1) * Dv)
      = 2 * (Q - 1)
        * (dd * eta * (1 - mu) ^ 2 * (dd - 1)
           * (c * (1 - eta) + 4 * eta)
           * (c * (1 - eta) * (Q - 1) + 2 * eta * (Q - 2))) := by
  subst hD1; subst hDv; ring

/-- The cleared form of the identity: no division anywhere. -/
theorem profile_gap_cleared (hq : 3 ≤ Q) (hd1 : 1 ≤ dd) (hdq : dd ≤ Q)
    (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    (Pd Q dd c eta mu - dd * Pd Q 1 c eta mu)
      * (2 * c * Q * (Q - 1) * Dd Q 1 c eta * Dd Q dd c eta)
      = 2 * (Q - 1)
        * (dd * eta * (1 - mu) ^ 2 * (dd - 1)
           * (c * (1 - eta) + 4 * eta)
           * (c * (1 - eta) * (Q - 1) + 2 * eta * (Q - 2))) := by
  rw [gap_times_denominator hq hd1 hdq hc h0 h1]
  exact denominator_polynomial Q dd c eta mu (Dd Q 1 c eta) (Dd Q dd c eta) rfl rfl

/-- THE IDENTITY that replaces the cap. -/
theorem profile_gap_factorization (hq : 3 ≤ Q) (hd1 : 1 ≤ dd) (hdq : dd ≤ Q)
    (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    Pd Q dd c eta mu - dd * Pd Q 1 c eta mu
      = dd * eta * (1 - mu) ^ 2 * (dd - 1)
          * (c * (1 - eta) + 4 * eta)
          * (c * (1 - eta) * (Q - 1) + 2 * eta * (Q - 2))
        / (c * Q * Dd Q 1 c eta * Dd Q dd c eta) := by
  have hqne : Q ≠ 0 := by intro h; rw [h] at hq; linarith
  have hq1ne : Q - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hD1 : Dd Q 1 c eta ≠ 0 := ne_of_gt (Dd_pos hq le_rfl (by linarith) hc h0 h1)
  have hDd : Dd Q dd c eta ≠ 0 := ne_of_gt (Dd_pos hq hd1 hdq hc h0 h1)
  have hcl := profile_gap_cleared (mu := mu) hq hd1 hdq hc h0 h1
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hcne hqne) hD1) hDd)]
  have h2 : (2 : ℚ) * (Q - 1) ≠ 0 := mul_ne_zero two_ne_zero hq1ne
  apply mul_left_cancel₀ h2
  calc 2 * (Q - 1) * ((Pd Q dd c eta mu - dd * Pd Q 1 c eta mu)
        * (c * Q * Dd Q 1 c eta * Dd Q dd c eta))
      = (Pd Q dd c eta mu - dd * Pd Q 1 c eta mu)
        * (2 * c * Q * (Q - 1) * Dd Q 1 c eta * Dd Q dd c eta) := by ring
    _ = 2 * (Q - 1)
        * (dd * eta * (1 - mu) ^ 2 * (dd - 1) * (c * (1 - eta) + 4 * eta)
           * (c * (1 - eta) * (Q - 1) + 2 * eta * (Q - 2))) := hcl

theorem profile_gap_nonneg (hq : 3 ≤ Q) (hd1 : 1 ≤ dd) (hdq : dd ≤ Q)
    (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    dd * Pd Q 1 c eta mu ≤ Pd Q dd c eta mu := by
  have hD1 := Dd_pos (Q := Q) (dd := 1) hq le_rfl (by linarith) hc h0 h1
  have hDd := Dd_pos (Q := Q) (dd := dd) hq hd1 hdq hc h0 h1
  have hnum : 0 ≤ dd * eta * (1 - mu) ^ 2 * (dd - 1)
      * (c * (1 - eta) + 4 * eta)
      * (c * (1 - eta) * (Q - 1) + 2 * eta * (Q - 2)) := by
    have hf1 : (0 : ℚ) ≤ c * (1 - eta) + 4 * eta := by nlinarith
    have hcq : (0 : ℚ) ≤ c * (1 - eta) * (Q - 1) :=
      mul_nonneg (mul_nonneg (le_of_lt hc) (by linarith)) (by linarith)
    have hf2 : (0 : ℚ) ≤ c * (1 - eta) * (Q - 1) + 2 * eta * (Q - 2) := by nlinarith
    have p1 : (0 : ℚ) ≤ dd * eta := mul_nonneg (by linarith) h0
    have p2 : (0 : ℚ) ≤ dd * eta * (1 - mu) ^ 2 := mul_nonneg p1 (sq_nonneg _)
    have p3 : (0 : ℚ) ≤ dd * eta * (1 - mu) ^ 2 * (dd - 1) :=
      mul_nonneg p2 (by linarith)
    exact mul_nonneg (mul_nonneg p3 hf1) hf2
  have hden : (0 : ℚ) < 2 * c * Q * (Q - 1) * Dd Q 1 c eta * Dd Q dd c eta :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos
      (by norm_num : (0 : ℚ) < 2) hc) (by linarith)) (by linarith)) hD1) hDd
  have hcl := profile_gap_cleared (mu := mu) hq hd1 hdq hc h0 h1
  have hRHS : 0 ≤ 2 * (Q - 1)
      * (dd * eta * (1 - mu) ^ 2 * (dd - 1) * (c * (1 - eta) + 4 * eta)
         * (c * (1 - eta) * (Q - 1) + 2 * eta * (Q - 2))) :=
    mul_nonneg (by linarith) hnum
  have hprod : (0 : ℚ) * (2 * c * Q * (Q - 1) * Dd Q 1 c eta * Dd Q dd c eta)
      ≤ (Pd Q dd c eta mu - dd * Pd Q 1 c eta mu)
        * (2 * c * Q * (Q - 1) * Dd Q 1 c eta * Dd Q dd c eta) := by
    rw [zero_mul, hcl]; exact hRHS
  have := le_of_mul_le_mul_right hprod hden
  linarith

theorem P1_nonneg (hq : 3 ≤ Q) (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    0 ≤ Pd Q 1 c eta mu := by
  have hqpos : (0 : ℚ) < Q := by linarith
  have hqne : Q ≠ 0 := ne_of_gt hqpos
  have hq1ne : Q - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hD1 := Dd_pos (Q := Q) (dd := 1) hq le_rfl (by linarith) hc h0 h1
  have hD1ne : Dd Q 1 c eta ≠ 0 := ne_of_gt hD1
  have hkey : 2 * eta ≤ Dd Q 1 c eta := by
    unfold Dd
    have : (0 : ℚ) ≤ c * (1 - eta) * (Q - 1) :=
      mul_nonneg (mul_nonneg (le_of_lt hc) (by linarith)) (by linarith)
    nlinarith
  have hrepr : Pd Q 1 c eta mu
      = (1 - eta) * mu ^ 2 / (2 * Q)
        + eta * (1 - mu) ^ 2 / (c * Q) * (1 - 2 * eta / Dd Q 1 c eta) := by
    unfold Pd Cd
    field_simp
    ring
  rw [hrepr]
  have t1 : 0 ≤ (1 - eta) * mu ^ 2 / (2 * Q) :=
    div_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)
  have t2 : 0 ≤ 1 - 2 * eta / Dd Q 1 c eta := by
    rw [sub_nonneg, div_le_one hD1]; exact hkey
  have t3 : 0 ≤ eta * (1 - mu) ^ 2 / (c * Q) :=
    div_nonneg (mul_nonneg h0 (sq_nonneg _)) (le_of_lt (mul_pos hc hqpos))
  have := mul_nonneg t3 t2
  linarith

/-- DISTANCE ONE IS ACTIVE, with no cap on `eta`. -/
theorem distance_one_active (hq : 3 ≤ Q) (hd1 : 1 ≤ dd) (hdq : dd ≤ Q)
    (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    Pd Q 1 c eta mu ≤ Pd Q dd c eta mu := by
  have hP1 := P1_nonneg (Q := Q) (c := c) (eta := eta) (mu := mu) hq hc h0 h1
  have hgap := profile_gap_nonneg (Q := Q) (dd := dd) (c := c) (eta := eta) (mu := mu)
    hq hd1 hdq hc h0 h1
  nlinarith

/-- The exact square identity: the excess of the quadratic over its profiled value,
with denominators cleared, is a single square. -/
theorem quadratic_minus_profile (hq : 3 ≤ Q) (hd1 : 1 ≤ dd) (hdq : dd ≤ Q)
    (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (x : ℚ) :
    (Ad Q dd c eta * x ^ 2 + 2 * Bd Q dd c eta mu * x + Cd Q dd c eta mu
     - Pd Q dd c eta mu) * (2 * c * Q * (Q - 1) * Dd Q dd c eta)
      = (Q - dd) * (Dd Q dd c eta * x + 2 * eta * (1 - mu) * dd) ^ 2 := by
  have hqpos : (0 : ℚ) < Q := by linarith
  have hqne : Q ≠ 0 := ne_of_gt hqpos
  have hq1ne : Q - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hDne : Dd Q dd c eta ≠ 0 := ne_of_gt (Dd_pos hq hd1 hdq hc h0 h1)
  unfold Ad Bd Pd Cd
  field_simp
  ring

/-- ATTAINMENT. At the unconstrained nuisance minimiser of distance one the bound `P 1`
is achieved with equality -- so `P 1` is not merely a floor, it is the value. -/
theorem distance_one_attained (hq : 3 ≤ Q) (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    Ad Q 1 c eta * (-(2 * eta * (1 - mu) / Dd Q 1 c eta)) ^ 2
      + 2 * Bd Q 1 c eta mu * (-(2 * eta * (1 - mu) / Dd Q 1 c eta))
      + Cd Q 1 c eta mu = Pd Q 1 c eta mu := by
  have hqpos : (0 : ℚ) < Q := by linarith
  have hD1 := Dd_pos (Q := Q) (dd := 1) hq le_rfl (by linarith) hc h0 h1
  have hDne : Dd Q 1 c eta ≠ 0 := ne_of_gt hD1
  have hM : (0 : ℚ) < 2 * c * Q * (Q - 1) * Dd Q 1 c eta :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℚ) < 2) hc) hqpos)
      (by linarith)) hD1
  have hzero : Dd Q 1 c eta * (-(2 * eta * (1 - mu) / Dd Q 1 c eta))
      + 2 * eta * (1 - mu) * 1 = 0 := by
    field_simp
    ring
  have hid := quadratic_minus_profile (Q := Q) (dd := 1) (c := c) (eta := eta)
    (mu := mu) hq le_rfl (by linarith) hc h0 h1 (-(2 * eta * (1 - mu) / Dd Q 1 c eta))
  have hRHS : (Q - 1) * (Dd Q 1 c eta * (-(2 * eta * (1 - mu) / Dd Q 1 c eta))
      + 2 * eta * (1 - mu) * 1) ^ 2 = 0 := by rw [hzero]; ring
  rw [hRHS] at hid
  have hfac := (mul_eq_zero.mp hid).resolve_right (ne_of_gt hM)
  linarith [hfac]

/-- The quadratic never goes below its profiled value. One square covers both `dd < Q`
and `dd = Q`: at `dd = Q` the factor `(Q - dd)` vanishes, which is exactly the
degenerate branch. -/
theorem quadratic_ge_profile (hq : 3 ≤ Q) (hd1 : 1 ≤ dd) (hdq : dd ≤ Q)
    (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (x : ℚ) :
    Pd Q dd c eta mu
      ≤ Ad Q dd c eta * x ^ 2 + 2 * Bd Q dd c eta mu * x + Cd Q dd c eta mu := by
  have hqpos : (0 : ℚ) < Q := by linarith
  have hqne : Q ≠ 0 := ne_of_gt hqpos
  have hq1ne : Q - 1 ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  have hcne : c ≠ 0 := ne_of_gt hc
  have hDd := Dd_pos (Q := Q) (dd := dd) hq hd1 hdq hc h0 h1
  have hDne : Dd Q dd c eta ≠ 0 := ne_of_gt hDd
  have hM : (0 : ℚ) < 2 * c * Q * (Q - 1) * Dd Q dd c eta :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℚ) < 2) hc) hqpos)
      (by linarith)) hDd
  have hid := quadratic_minus_profile (Q := Q) (dd := dd) (c := c) (eta := eta)
    (mu := mu) hq hd1 hdq hc h0 h1 x
  have hR : (0 : ℚ) ≤ (Q - dd) * (Dd Q dd c eta * x + 2 * eta * (1 - mu) * dd) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hmul : (0 : ℚ) * (2 * c * Q * (Q - 1) * Dd Q dd c eta)
      ≤ (Ad Q dd c eta * x ^ 2 + 2 * Bd Q dd c eta mu * x + Cd Q dd c eta mu
         - Pd Q dd c eta mu) * (2 * c * Q * (Q - 1) * Dd Q dd c eta) := by
    rw [zero_mul, hid]; exact hR
  have := le_of_mul_le_mul_right hmul hM
  linarith

/-- EVERY alternative `(dd, x)` costs at least `P 1`, with no cap. -/
theorem value_ge_P1 (hq : 3 ≤ Q) (hd1 : 1 ≤ dd) (hdq : dd ≤ Q)
    (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) (x : ℚ) :
    Pd Q 1 c eta mu
      ≤ Ad Q dd c eta * x ^ 2 + 2 * Bd Q dd c eta mu * x + Cd Q dd c eta mu :=
  le_trans (distance_one_active hq hd1 hdq hc h0 h1)
    (quadratic_ge_profile hq hd1 hdq hc h0 h1 x)

/-- THE UNCAPPED VALUE. When the distance-one nuisance minimiser is LEGAL
(`delta = 2 eta g / D 1 <= mu`, i.e. `nu = mu - delta >= 0`), the design's value
against every alternative is EXACTLY `P 1`: it is attained at a legal nuisance and no
alternative does better. No cap on `eta` is used anywhere. -/
theorem uncapped_value_exact (hq : 3 ≤ Q) (hc : 0 < c) (h0 : 0 ≤ eta) (h1 : eta ≤ 1)
    (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hleg : 2 * eta * (1 - mu) / Dd Q 1 c eta ≤ mu) :
    (∃ x : ℚ, 0 ≤ mu + x ∧ mu + x ≤ 1 ∧
       Ad Q 1 c eta * x ^ 2 + 2 * Bd Q 1 c eta mu * x + Cd Q 1 c eta mu
         = Pd Q 1 c eta mu)
    ∧ (∀ dd x : ℚ, 1 ≤ dd → dd ≤ Q →
        Pd Q 1 c eta mu
          ≤ Ad Q dd c eta * x ^ 2 + 2 * Bd Q dd c eta mu * x + Cd Q dd c eta mu) := by
  have hD1 := Dd_pos (Q := Q) (dd := 1) hq le_rfl (by linarith) hc h0 h1
  have hdel0 : 0 ≤ 2 * eta * (1 - mu) / Dd Q 1 c eta :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (le_of_lt hD1)
  refine ⟨⟨-(2 * eta * (1 - mu) / Dd Q 1 c eta), by linarith, by linarith,
    distance_one_attained hq hc h0 h1⟩, ?_⟩
  intro dd x hd1 hdq
  exact value_ge_P1 hq hd1 hdq hc h0 h1 x

#print axioms Dd_pos
#print axioms gap_times_denominator
#print axioms denominator_polynomial
#print axioms profile_gap_cleared
#print axioms profile_gap_factorization
#print axioms profile_gap_nonneg
#print axioms P1_nonneg
#print axioms distance_one_active
#print axioms quadratic_minus_profile
#print axioms distance_one_attained
#print axioms quadratic_ge_profile
#print axioms value_ge_P1
#print axioms uncapped_value_exact

end
end CIGAMF.P13.D6UncappedProfile
