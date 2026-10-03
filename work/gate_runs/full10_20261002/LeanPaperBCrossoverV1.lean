import Mathlib

/-!
# Paper B, the query-class crossover: the mechanism, not a sweep

The widened probe `g_eta = (z4 + z5 + z6 + eta z4 z5)/(3+eta)` is conjectured to give
`H^2 ≍ h^6 + eta^2 h^4`.  A sweep of fitted slopes cannot tell whether the two scales add
or interfere: that turns on whether a cross term survives.  This module settles the
algebra and the parity, which is the part a sweep cannot supply.

  * the three moments against the hidden character are computed exactly;
  * the cross term of the leading quadratic form vanishes because `A` is odd, `B` is even
    and the base density is even, so `A B / p0` is odd;
  * with the cross term gone the quadratic form splits, and substituting the density
    expansion's own coefficients gives exactly the shape `h^6 + eta^2 h^4`.

What is NOT proved here: that `A` and `B` are not identically zero, that the two
integrals are finite, and that the remainder is bounded uniformly in `(h, eta)`.  Those
three are what stand between this mechanism and the law.
-/

namespace CIGAMF.P13.PaperBCrossover

open MeasureTheory

/-! ## The three moments, exactly -/

/-- Rademacher values. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- The widened probe of the crossover family. -/
noncomputable def gEta (η : ℝ) (x y z : Bool) : ℝ :=
  (sgn x + sgn y + sgn z + η * (sgn x * sgn y)) / (3 + η)

/-- The hidden parity character. -/
def chi (x y z : Bool) : ℝ := sgn x * sgn y * sgn z

/-- Expectation over three independent Rademacher bits, written out. -/
noncomputable def E (F : Bool → Bool → Bool → ℝ) : ℝ :=
  (F true true true + F true true false + F true false true + F true false false
    + F false true true + F false true false + F false false true
    + F false false false) / 8

/-- **First moment: zero.**  The widened probe is still orthogonal to the character. -/
theorem moment_one (η : ℝ) (hη : 3 + η ≠ 0) :
    E (fun x y z => chi x y z * gEta η x y z) = 0 := by
  simp only [E, chi, gEta, sgn]
  norm_num
  field_simp
  ring

/-- **Second moment: the `eta` channel.**  It opens linearly in `eta` and is the term the
crossover is about. -/
theorem moment_two (η : ℝ) (hη : 3 + η ≠ 0) :
    E (fun x y z => chi x y z * (gEta η x y z) ^ 2) = 2 * η / (3 + η) ^ 2 := by
  simp only [E, chi, gEta, sgn]
  norm_num
  field_simp
  ring

/-- **Third moment: the original channel**, which survives at `eta = 0`. -/
theorem moment_three (η : ℝ) (hη : 3 + η ≠ 0) :
    E (fun x y z => chi x y z * (gEta η x y z) ^ 3) = 6 / (3 + η) ^ 3 := by
  simp only [E, chi, gEta, sgn]
  norm_num
  field_simp
  ring

/-! ## The parity cancellation -/

/-- An odd integrable function integrates to zero over the line. -/
theorem integral_odd_eq_zero (f : ℝ → ℝ) (hf : ∀ y, f (-y) = -f y) :
    ∫ y, f y = 0 := by
  have h1 : ∫ y, f (-y) = ∫ y, f y := integral_neg_eq_self f volume
  have h2 : ∫ y, f (-y) = ∫ y, -f y := by simp_rw [hf]
  rw [integral_neg] at h2
  linarith [h1, h2]

/-- **The cross term vanishes.**  `A` odd, `B` even and the base density even make
`A B / p0` odd, so the quadratic form's middle term is zero -- for parity reasons, with no
estimate and no cancellation by size. -/
theorem cross_term_vanishes (A B p0 : ℝ → ℝ)
    (hA : ∀ y, A (-y) = -A y) (hB : ∀ y, B (-y) = B y) (hp : ∀ y, p0 (-y) = p0 y) :
    ∫ y, A y * B y / p0 y = 0 := by
  refine integral_odd_eq_zero _ (fun y => ?_)
  rw [hA, hB, hp]
  ring

/-- **The quadratic form splits.**  With no cross term the two channels add; they do not
interfere, at either sign of the coefficients. -/
theorem quadratic_splits (A B p0 : ℝ → ℝ) (α β : ℝ)
    (hA : ∀ y, A (-y) = -A y) (hB : ∀ y, B (-y) = B y) (hp : ∀ y, p0 (-y) = p0 y)
    (hAA : Integrable (fun y => α ^ 2 * ((A y) ^ 2 / p0 y)))
    (hAB : Integrable (fun y => 2 * α * β * (A y * B y / p0 y)))
    (hBB : Integrable (fun y => β ^ 2 * ((B y) ^ 2 / p0 y))) :
    ∫ y, (α * A y + β * B y) ^ 2 / p0 y
      = α ^ 2 * (∫ y, (A y) ^ 2 / p0 y) + β ^ 2 * (∫ y, (B y) ^ 2 / p0 y) := by
  have hexp : (fun y => (α * A y + β * B y) ^ 2 / p0 y)
      = fun y => α ^ 2 * ((A y) ^ 2 / p0 y) + 2 * α * β * (A y * B y / p0 y)
        + β ^ 2 * ((B y) ^ 2 / p0 y) := by
    funext y
    ring
  have e1 : ∫ y, α ^ 2 * ((A y) ^ 2 / p0 y) = α ^ 2 * ∫ y, (A y) ^ 2 / p0 y :=
    integral_const_mul _ _
  have e2 : ∫ y, 2 * α * β * (A y * B y / p0 y)
      = 2 * α * β * ∫ y, A y * B y / p0 y := integral_const_mul _ _
  have e3 : ∫ y, β ^ 2 * ((B y) ^ 2 / p0 y) = β ^ 2 * ∫ y, (B y) ^ 2 / p0 y :=
    integral_const_mul _ _
  have hAB' : Integrable (fun y => α ^ 2 * ((A y) ^ 2 / p0 y)
      + 2 * α * β * (A y * B y / p0 y)) := hAA.add hAB
  have s1 : ∫ y, (α ^ 2 * ((A y) ^ 2 / p0 y) + 2 * α * β * (A y * B y / p0 y)
        + β ^ 2 * ((B y) ^ 2 / p0 y))
      = (∫ y, (α ^ 2 * ((A y) ^ 2 / p0 y) + 2 * α * β * (A y * B y / p0 y)))
        + ∫ y, β ^ 2 * ((B y) ^ 2 / p0 y) := integral_add hAB' hBB
  have s2 : ∫ y, (α ^ 2 * ((A y) ^ 2 / p0 y) + 2 * α * β * (A y * B y / p0 y))
      = (∫ y, α ^ 2 * ((A y) ^ 2 / p0 y)) + ∫ y, 2 * α * β * (A y * B y / p0 y) :=
    integral_add hAA hAB
  rw [hexp, s1, s2, e1, e2, e3, cross_term_vanishes A B p0 hA hB hp]
  ring

/-- **The two scales, named.**  Substituting the coefficients the density expansion
produces -- `eta h^2/(3+eta)^2` on the odd channel and `h^3/(3+eta)^3` on the even one --
turns the split form into exactly `eta^2 h^4` plus `h^6`, with constants free of `h`. -/
theorem two_scale_shape (h η IA IB : ℝ) (hη : 3 + η ≠ 0) :
    (η * h ^ 2 / (3 + η) ^ 2) ^ 2 * IA + (h ^ 3 / (3 + η) ^ 3) ^ 2 * IB
      = η ^ 2 * h ^ 4 * (IA / (3 + η) ^ 4) + h ^ 6 * (IB / (3 + η) ^ 6) := by
  field_simp

/-- At `eta = 0` only the `h^6` channel survives, and at `h` fixed the `eta` channel grows
quadratically: the crossover is where the two are equal. -/
theorem crossover_balance (h IA IB : ℝ) (hh : 0 < h) (hIA : 0 < IA) (hIB : 0 < IB) :
    ∃ η : ℝ, 0 < η ∧ η ^ 2 * h ^ 4 * IA = h ^ 6 * IB := by
  refine ⟨h * Real.sqrt (IB / IA), by positivity, ?_⟩
  have hsq : (Real.sqrt (IB / IA)) ^ 2 = IB / IA := Real.sq_sqrt (by positivity)
  rw [mul_pow, hsq]
  field_simp

/-! ## Audit -/

#print axioms moment_one
#print axioms moment_two
#print axioms moment_three
#print axioms integral_odd_eq_zero
#print axioms cross_term_vanishes
#print axioms quadratic_splits
#print axioms two_scale_shape
#print axioms crossover_balance

end CIGAMF.P13.PaperBCrossover
