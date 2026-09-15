import Mathlib

/-! # MASTER P8, steps 1a-1d: the anchor is MANDATORY, by two separated certificates.

The audit's M2: `LeanMasterActiveSetV1` still reads "the threshold is 0.118", treats
support-in-active-set as optimality, and infers from the existence of a design with
`M = 0` that no anchor is needed.  None of those follow.  The correct argument needs no
optimiser at all:

    sup_{x : x₀ = 0} J(x)  ≤  U₀  <  L₁  ≤  J(x⁽¹⁾)   for one anchored design x⁽¹⁾,

and then every optimiser has `x₀ > 0`.  Note the INEQUALITY on the left: the
certificate gives an upper bound on the anchor-free supremum, never an equality.

## STEP 1a -- the energy from the real query means

With `d_{u,e} = m_θ(e) - m_{θ_u}(e)`, variances `v_e`, prices `κ_e`, anchor variance
`v₀`,

    E_u(x, x₀; t) = (1/2) ∑_e (x_e/v_e)(d_{u,e} - t)² + x₀t²/(2v₀)
                  = D_u - M_u t + K t²/2
                  = D_u - M_u²/(2K) + (K/2)(t - M_u/K)²,

so `I_u = inf_t E_u = D_u - M_u²/(2K)`, attained at `t = M_u/K`.  `K` is the only place
the anchor enters, which is exactly why buying it can help.

## STEP 1b -- one upper certificate for ALL anchor-free designs

Take any rational distribution `λ` over PAIRS `(u_j, t_j)` -- several shifts per
alternative are allowed, which is precisely the multiplier-extraction bug the audit
found in `P8`.  Put `H_e = ∑_j λ_j (d_{u_j,e} - t_j)²/(2v_e)` and `U₀ = max_e H_e/κ_e`.
Then for every `x ≥ 0` with `∑ κ_e x_e = 1`,

    J(x, 0) ≤ ∑_j λ_j E_{u_j}(x,0;t_j) = ∑_e x_e H_e ≤ U₀ ∑_e κ_e x_e = U₀.

No complementary slackness, no claim that any cut is active.

## WHAT IS PROVED

* `energy_expand`, `energy_completed` — step 1a, including the square completion.
* `profiled_le`, `profiled_attained` — `I_u = D_u - M_u²/(2K)`, and it IS attained.
* `anchor_free_upper` — **step 1b, for every anchor-free design.**
* `anchor_mandatory` — **step 1d**: with `U₀ < L₁` and one anchored design reaching
  `L₁`, no optimiser is anchor-free.

## WHAT THIS DOES NOT ESTABLISH

- The numbers `U₀ = 0.013773103739935157` and `L₁ = 0.014042993093731984` at price
  `c₀ = 1/10` are exact rational certificates computed by
  `scripts/P12_master_anchor_required.py`; they are inputs here, not proved in Lean.
- `U₀` is an UPPER bound on the anchor-free supremum, not its value.
- This says nothing about the symmetric-family price threshold
  `c* = (m-1)²/(m+3)²`, nor about the earlier `0.118`.  They are different problems.
-/

namespace CIGAMF.P13.MasterAnchorCertificate

open Finset

noncomputable section

variable {E U J : Type*} [Fintype E] [Fintype U] [Fintype J]

/-- Step 1a: the energy of a design against alternative `u` at nuisance shift `t`. -/
def energy (v : E → ℝ) (d : E → ℝ) (x : E → ℝ) (x0 v0 t : ℝ) : ℝ :=
  (∑ e, x e / v e * (d e - t) ^ 2) / 2 + x0 * t ^ 2 / (2 * v0)

/-- `K = ∑ x_e/v_e + x₀/v₀`: the only place the anchor enters. -/
def Kcap (v : E → ℝ) (x : E → ℝ) (x0 v0 : ℝ) : ℝ := (∑ e, x e / v e) + x0 / v0

def Mval (v : E → ℝ) (d : E → ℝ) (x : E → ℝ) : ℝ := ∑ e, x e * d e / v e

def Dval (v : E → ℝ) (d : E → ℝ) (x : E → ℝ) : ℝ := (∑ e, x e * (d e) ^ 2 / v e) / 2

/-- Step 1a, expansion. -/
theorem energy_expand (v d x : E → ℝ) (x0 v0 t : ℝ) (hv0 : v0 ≠ 0) :
    energy v d x x0 v0 t
      = Dval v d x - Mval v d x * t + Kcap v x x0 v0 * t ^ 2 / 2 := by
  unfold energy Dval Mval Kcap
  have hsum : ∑ e, x e / v e * (d e - t) ^ 2
      = (∑ e, x e * (d e) ^ 2 / v e) - 2 * t * (∑ e, x e * d e / v e)
        + t ^ 2 * (∑ e, x e / v e) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [hsum]
  field_simp
  ring

/-- Step 1a, square completion. -/
theorem energy_completed (v d x : E → ℝ) (x0 v0 t : ℝ) (hv0 : v0 ≠ 0)
    (hK : Kcap v x x0 v0 ≠ 0) :
    energy v d x x0 v0 t
      = Dval v d x - (Mval v d x) ^ 2 / (2 * Kcap v x x0 v0)
        + Kcap v x x0 v0 / 2 * (t - Mval v d x / Kcap v x x0 v0) ^ 2 := by
  rw [energy_expand v d x x0 v0 t hv0]
  field_simp
  ring

/-- The profiled information is a genuine infimum. -/
theorem profiled_le (v d x : E → ℝ) (x0 v0 t : ℝ) (hv0 : v0 ≠ 0)
    (hK : 0 < Kcap v x x0 v0) :
    Dval v d x - (Mval v d x) ^ 2 / (2 * Kcap v x x0 v0) ≤ energy v d x x0 v0 t := by
  rw [energy_completed v d x x0 v0 t hv0 (ne_of_gt hK)]
  have : 0 ≤ Kcap v x x0 v0 / 2 * (t - Mval v d x / Kcap v x x0 v0) ^ 2 := by positivity
  linarith

/-- …and it is attained. -/
theorem profiled_attained (v d x : E → ℝ) (x0 v0 : ℝ) (hv0 : v0 ≠ 0)
    (hK : 0 < Kcap v x x0 v0) :
    energy v d x x0 v0 (Mval v d x / Kcap v x x0 v0)
      = Dval v d x - (Mval v d x) ^ 2 / (2 * Kcap v x x0 v0) := by
  rw [energy_completed v d x x0 v0 _ hv0 (ne_of_gt hK)]
  simp

/-- **Step 1b: one upper certificate for EVERY anchor-free design.**  `lam` may put
several shifts on the same alternative -- keeping every cut the LP used is exactly the
fix to the multiplier-extraction bug. -/
theorem anchor_free_upper
    (v kap : E → ℝ) (dd : J → E → ℝ) (lam : J → ℝ) (tj : J → ℝ)
    (x : E → ℝ) (Ival : J → ℝ) (Jval U0 : ℝ)
    (hlam : ∀ j, 0 ≤ lam j) (hlamsum : ∑ j, lam j = 1)
    (hx : ∀ e, 0 ≤ x e)
    (hbudget : ∑ e, kap e * x e = 1)
    (hIe : ∀ j, Ival j ≤ (∑ e, x e / v e * (dd j e - tj j) ^ 2) / 2)
    (hJval : ∀ j, Jval ≤ Ival j)
    (hU0 : ∀ e, (∑ j, lam j * ((dd j e - tj j) ^ 2 / (2 * v e))) ≤ U0 * kap e) :
    Jval ≤ U0 := by
  classical
  have h1 : Jval ≤ ∑ j, lam j * ((∑ e, x e / v e * (dd j e - tj j) ^ 2) / 2) := by
    have hstep : ∑ j, lam j * Jval
        ≤ ∑ j, lam j * ((∑ e, x e / v e * (dd j e - tj j) ^ 2) / 2) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (le_trans (hJval j) (hIe j)) (hlam j)
    have hc : ∑ j, lam j * Jval = Jval := by rw [← Finset.sum_mul, hlamsum, one_mul]
    linarith [hc ▸ hstep]
  have hswap : (∑ j, lam j * ((∑ e, x e / v e * (dd j e - tj j) ^ 2) / 2))
      = ∑ e, x e * (∑ j, lam j * ((dd j e - tj j) ^ 2 / (2 * v e))) := by
    have hl : ∀ j : J, lam j * ((∑ e, x e / v e * (dd j e - tj j) ^ 2) / 2)
        = ∑ e, x e * (lam j * ((dd j e - tj j) ^ 2 / (2 * v e))) := by
      intro j
      rw [Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      field_simp
      try ring
    simp_rw [hl]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
  have h2 : (∑ e, x e * (∑ j, lam j * ((dd j e - tj j) ^ 2 / (2 * v e))))
      ≤ ∑ e, x e * (U0 * kap e) :=
    Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hU0 e) (hx e)
  have h3 : ∑ e, x e * (U0 * kap e) = U0 := by
    have hrw : ∑ e, x e * (U0 * kap e) = U0 * ∑ e, kap e * x e := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [hrw, hbudget, mul_one]
  linarith [h1, hswap ▸ h1, h2, h3]

/-- **Step 1d: the anchor is mandatory.**  No optimality of `x⁽¹⁾` is assumed, and no
value of the game is needed. -/
theorem anchor_mandatory {Design : Type*} (value : Design → ℝ) (anchorFree : Design → Prop)
    (U0 L1 : ℝ) (hgap : U0 < L1)
    (hcert : ∀ D, anchorFree D → value D ≤ U0)
    (D1 : Design) (hD1 : L1 ≤ value D1)
    (Dopt : Design) (hopt : ∀ D, value D ≤ value Dopt) :
    ¬ anchorFree Dopt := by
  intro hfree
  have h1 := hcert Dopt hfree
  have h2 := hopt D1
  linarith

end

#print axioms energy_expand
#print axioms energy_completed
#print axioms profiled_le
#print axioms profiled_attained
#print axioms anchor_free_upper
#print axioms anchor_mandatory

end CIGAMF.P13.MasterAnchorCertificate
