import «LeanD6SameResponseMarginGameV1»

/-! Algebraic game for the reference scale t=tau/k.
This is the reduced bilinear game, NOT yet a Lean bridge from productResponse
at non-corner references. The actual finite-cube bridge and approximation error
are derived separately and checked by run_d6_reference_phase_reduction.py.
-/
namespace CIGAMF.P13.D6ReferenceReducedGame
noncomputable section

def payoff (k a b rho h d : ℝ) : ℝ :=
  ((rho-2*b)*d-2*(a-b)*h*d/k+(2*a-rho)*h)/2

def value (k a b rho : ℝ) : ℝ :=
  k*(rho-2*b)*(2*a-rho)/(4*(a-b))

def pZero (a b rho : ℝ) : ℝ := (rho-2*b)/(2*(a-b))

theorem weights_valid (a b rho : ℝ) (hab : b < a)
    (hlo : 2*b ≤ rho) (hhi : rho ≤ 2*a) :
    0 ≤ pZero a b rho ∧ pZero a b rho ≤ 1 := by
  unfold pZero
  have hd : 0 < 2*(a-b) := by linarith
  constructor
  · exact div_nonneg (by linarith) hd.le
  · apply (div_le_one hd).mpr
    linarith

theorem primal_equalizer (k a b rho h : ℝ) (hk : k ≠ 0) (hab : a ≠ b) :
    pZero a b rho * payoff k a b rho h 0 +
      (1-pZero a b rho)*payoff k a b rho h k = value k a b rho := by
  unfold pZero payoff value
  have hc : a-b ≠ 0 := sub_ne_zero.mpr hab
  field_simp
  <;> ring

theorem dual_equalizer (k a b rho d : ℝ) (hk : k ≠ 0) (hab : a ≠ b) :
    pZero a b rho * payoff k a b rho k d +
      (1-pZero a b rho)*payoff k a b rho 0 d = value k a b rho := by
  unfold pZero payoff value
  have hc : a-b ≠ 0 := sub_ne_zero.mpr hab
  field_simp
  <;> ring

/-- Moving the missing h=0 dual world to h=1 costs at most a-b.
This addresses the actual combinatorial restriction |A intersect T| >= 1.
-/
theorem replace_zero_world (k a b rho d : ℝ) (hk : 0 < k) (hab : b < a)
    (hlo : 2*b ≤ rho) (hhi : rho ≤ 2*a) (hd : 0 ≤ d) (hdk : d ≤ k) :
    |payoff k a b rho 1 d-payoff k a b rho 0 d| ≤ a-b := by
  have hc : 0 ≤ a-b := by linarith
  have hz : 0 ≤ d/k := div_nonneg hd hk.le
  have ho : d/k ≤ 1 := (div_le_one hk).mpr hdk
  have hp : 0 ≤ (a-b)*(d/k) := mul_nonneg hc hz
  have hu : (a-b)*(d/k) ≤ a-b := by nlinarith
  have he : payoff k a b rho 1 d-payoff k a b rho 0 d =
      (2*a-rho)/2-(a-b)*(d/k) := by unfold payoff;ring
  rw [he,abs_le]
  constructor <;> nlinarith

/-- The known corner law is recovered at a=1, b=0. -/
theorem corner_value (k rho : ℝ) : value k 1 0 rho=k*rho*(2-rho)/4 := by
  unfold value
  ring

#print axioms weights_valid
#print axioms primal_equalizer
#print axioms dual_equalizer
#print axioms replace_zero_world
#print axioms corner_value
end
end CIGAMF.P13.D6ReferenceReducedGame
