import Mathlib

/-!
# Paper B: the cube identity behind the characteristic-function attainment

The attainment argument for the tail signal needs the characteristic function of

    Y = F_{u,v}(Z) + h g(Z) + noise,     Z uniform on the cube {-1, +1}^r,

and specifically the exact difference between `v = +1` and `v = -1`.  The usual route
expands the `2^r` terms.  It is unnecessary: the product character `P = prod_l z_l` takes
only the values `+-1`, so `P^2 = 1`, and therefore

    exp(a P) = cosh a + P sinh a

**exactly**, with no series truncation and no case analysis on `r`.  The cube expectation
then factorises coordinate by coordinate, because a sum over the cube of a product of
per-coordinate terms is the product of the per-coordinate sums.

    sum over the cube of exp(a P + c S)
      = 2^r ( cosh a * (cosh c)^r + sinh a * (sinh c)^r ),     S = sum_l z_l.

Taking `a = i t v`, `c = i t h / r` and subtracting the two values of `v` kills the `cosh`
term and doubles the `sinh` one --- which is the claimed identity, and the `(i sin(th/r))^r`
factor is what makes the difference of order `h^r`.  The statement below is the algebraic
core; it holds for every `r` and every complex `a, c`, which a numerical check cannot give.

WHAT THIS IS AND IS NOT.  This is the cube half of the attainment argument.  The Gaussian
factor, the choice of `t_0` away from the zeros, the real/imaginary part according to the
parity of `r`, the bounded-statistic concentration and the decoder's sample budget are all
still to be written; none of them is here.
-/

namespace CIGAMF.P13.PaperBCube

open Finset

variable {r : ℕ}

/-- The `+-1` value of a coordinate. -/
noncomputable def sgn (b : Bool) : ℂ := if b then 1 else -1

theorem sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  unfold sgn; cases b <;> norm_num

/-- The product character of a cube point. -/
noncomputable def chr (z : Fin r → Bool) : ℂ := ∏ i, sgn (z i)

/-- The coordinate sum of a cube point. -/
noncomputable def csum (z : Fin r → Bool) : ℂ := ∑ i, sgn (z i)

theorem chr_sq (z : Fin r → Bool) : chr z * chr z = 1 := by
  unfold chr
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one (fun i _ => sgn_sq (z i))

/-- **`exp(a x) = cosh a + x sinh a` whenever `x^2 = 1`.**  No series manipulation: `x` is
`+1` or `-1`, and the two cases are the addition formulas. -/
theorem exp_of_sq_one (x a : ℂ) (hx : x * x = 1) :
    Complex.exp (a * x) = Complex.cosh a + x * Complex.sinh a := by
  rcases mul_self_eq_one_iff.mp hx with rfl | rfl
  · rw [mul_one, one_mul, Complex.cosh_add_sinh]
  · rw [mul_neg, mul_one, neg_one_mul, ← sub_eq_add_neg, Complex.cosh_sub_sinh]

/-- The per-coordinate sums: `2 cosh c` without the character, `2 sinh c` with it. -/
theorem sum_bool_exp (c : ℂ) :
    ∑ b : Bool, Complex.exp (c * sgn b) = 2 * Complex.cosh c := by
  have h1 : sgn true = 1 := by simp [sgn]
  have h0 : sgn false = -1 := by simp [sgn]
  have e1 : c * (1 : ℂ) = c := by ring
  have e0 : c * (-1 : ℂ) = -c := by ring
  rw [Fintype.sum_bool, h1, h0, e1, e0, ← Complex.two_cosh]

theorem sum_bool_sgn_exp (c : ℂ) :
    ∑ b : Bool, sgn b * Complex.exp (c * sgn b) = 2 * Complex.sinh c := by
  have h1 : sgn true = 1 := by simp [sgn]
  have h0 : sgn false = -1 := by simp [sgn]
  have e1 : c * (1 : ℂ) = c := by ring
  have e0 : c * (-1 : ℂ) = -c := by ring
  rw [Fintype.sum_bool, h1, h0, e1, e0, Complex.two_sinh]
  ring

/-- **The cube expectation, exactly.**  For every `r` and every `a, c`. -/
theorem cube_sum (r : ℕ) (a c : ℂ) :
    ∑ z : Fin r → Bool, Complex.exp (a * chr z + c * csum z)
      = 2 ^ r * (Complex.cosh a * Complex.cosh c ^ r
          + Complex.sinh a * Complex.sinh c ^ r) := by
  classical
  have hterm : ∀ z : Fin r → Bool,
      Complex.exp (a * chr z + c * csum z)
        = (Complex.cosh a) * ∏ i, Complex.exp (c * sgn (z i))
          + Complex.sinh a * ∏ i, (sgn (z i) * Complex.exp (c * sgn (z i))) := by
    intro z
    have hsplit : Complex.exp (a * chr z + c * csum z)
        = Complex.exp (a * chr z) * Complex.exp (c * csum z) := Complex.exp_add _ _
    have hprod : Complex.exp (c * csum z) = ∏ i, Complex.exp (c * sgn (z i)) := by
      unfold csum
      rw [Finset.mul_sum, Complex.exp_sum]
    have hchr : ∏ i, (sgn (z i) * Complex.exp (c * sgn (z i)))
        = chr z * ∏ i, Complex.exp (c * sgn (z i)) := by
      rw [Finset.prod_mul_distrib]
      rfl
    rw [hsplit, hprod, exp_of_sq_one (chr z) a (chr_sq z), hchr]
    ring
  rw [Finset.sum_congr rfl (fun z _ => hterm z), Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
  have h1 : ∑ z : Fin r → Bool, ∏ i, Complex.exp (c * sgn (z i))
      = (2 * Complex.cosh c) ^ r := by
    have hps := Finset.prod_univ_sum (fun _ : Fin r => (Finset.univ : Finset Bool))
      (fun (_ : Fin r) (b : Bool) => Complex.exp (c * sgn b))
    rw [Fintype.piFinset_univ] at hps
    rw [← hps, Finset.prod_congr rfl (fun i _ => sum_bool_exp c), Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
  have h2 : ∑ z : Fin r → Bool, ∏ i, (sgn (z i) * Complex.exp (c * sgn (z i)))
      = (2 * Complex.sinh c) ^ r := by
    have hps := Finset.prod_univ_sum (fun _ : Fin r => (Finset.univ : Finset Bool))
      (fun (_ : Fin r) (b : Bool) => sgn b * Complex.exp (c * sgn b))
    rw [Fintype.piFinset_univ] at hps
    rw [← hps, Finset.prod_congr rfl (fun i _ => sum_bool_sgn_exp c), Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
  rw [h1, h2, mul_pow, mul_pow]
  ring

/-- **The difference between the two signs of the hidden bit.**  The `cosh` term is even in
`a` and cancels; the `sinh` term is odd and doubles.  This is the identity the attainment
argument uses, and the `sinh c ^ r` factor is what makes it of order `h^r`. -/
theorem cube_difference (r : ℕ) (a c : ℂ) :
    (∑ z : Fin r → Bool, Complex.exp (a * chr z + c * csum z))
        - ∑ z : Fin r → Bool, Complex.exp (-a * chr z + c * csum z)
      = 2 ^ r * (2 * Complex.sinh a * Complex.sinh c ^ r) := by
  rw [cube_sum r a c, cube_sum r (-a) c, Complex.cosh_neg, Complex.sinh_neg]
  ring

/-- **Only the character-carrying factor survives.**  Stated separately because it is the
mechanism: the hidden bit enters exactly once, multiplying `sinh a`. -/
theorem cube_difference_factor (r : ℕ) (a c : ℂ) (hc : Complex.sinh c = 0) :
    (∑ z : Fin r → Bool, Complex.exp (a * chr z + c * csum z))
        - ∑ z : Fin r → Bool, Complex.exp (-a * chr z + c * csum z)
      = if r = 0 then 2 ^ r * (2 * Complex.sinh a) else 0 := by
  rw [cube_difference r a c, hc]
  by_cases hr : r = 0
  · subst hr; simp
  · rw [if_neg hr, zero_pow hr]
    ring

/-! ## Audit -/

#print axioms exp_of_sq_one
#print axioms sum_bool_exp
#print axioms sum_bool_sgn_exp
#print axioms cube_sum
#print axioms cube_difference

end CIGAMF.P13.PaperBCube
