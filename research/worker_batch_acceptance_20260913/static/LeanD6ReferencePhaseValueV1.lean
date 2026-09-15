import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Reference-dependent phase value: two-action dominance, endpoint worlds,
and the matching 2x2 certificate WITH the correction term.

This closes the purely algebraic segment named as the next Lean target in
`D6_REFERENCE_PHASE_DERIVATION_20260911.md`:

    two-action dominance -> endpoint-world reduction -> finite minimax value.

Everything is stated over abstract slope data `(p, r, c, e, b)`, so it applies at
every product reference, not only the corner. `LeanD6ReferenceReducedGameV1`
proves the value for the special case `e = 0`; the theorems here carry the
correction `e = min a (2 * b)` that the actual oscillation formula produces, and
`corner_value` recovers `k * rho * (2 - rho) / 4` at `a = 1, b = 0`.

NOT closed here, deliberately:
* the product-sum computation of the three slopes at a general reference, and
* the exact oscillation formula producing `risk0 / riskOne / riskGen`.
Those remain the open bridge. Every statement below is an algebraic consequence
of the loss SHAPE, with that shape taken as a definition, not as a theorem about
`productResponse`. Do not read this module as the general-reference minimax
theorem; read it as the half of that theorem which is now machine-checked.
-/

namespace CIGAMF.P13.D6ReferencePhaseValue
noncomputable section

/-! ## The symmetrised risk shape -/

/-- The `u`-free part of twice-the-regret after symmetrising over `T`:
`d` coordinates dropped, hidden intersection `h`, expected overlap `h * d / k`. -/
def base (k p c e r h d : ℝ) : ℝ := (p*d-2*c*(h*d/k)+max e (r*h))/2

/-- Decision `d = 0`; its correction is the full `e`. -/
def risk0 (e r h : ℝ) : ℝ := (max e (r*h)-e)/2

/-- Decision `d = 1`; its expected correction is `b * (k - h) / k`. -/
def riskOne (k p c e r b h : ℝ) : ℝ := base k p c e r h 1-b*(k-h)/k/2

/-- Any decision `2 <= d <= k`; no correction. -/
def riskGen (k p c e r h d : ℝ) : ℝ := base k p c e r h d

theorem risk0_eq (k p c e r h : ℝ) : risk0 e r h = base k p c e r h 0-e/2 := by
  unfold risk0 base; ring

/-- `base` is affine in `d`: mixing `d = 0` and `d = k` reproduces it exactly. -/
theorem base_affine (k p c e r h d : ℝ) (hk : k ≠ 0) :
    (1-d/k)*base k p c e r h 0+(d/k)*base k p c e r h k = base k p c e r h d := by
  unfold base; field_simp; ring

/-! ## L1: two-action dominance -/

/-- Every decision `2 <= d <= k` is no better than the mixture of `d = 0` and
`d = k` with weights `1 - d/k` and `d/k`. The whole gap is the correction `e`
that only the `d = 0` action pays. -/
theorem dominance_gen (k p c e r h d : ℝ) (hk : 0 < k) (he : 0 ≤ e)
    (hdk : d ≤ k) :
    (1-d/k)*risk0 e r h+(d/k)*base k p c e r h k ≤ riskGen k p c e r h d := by
  have hne : k ≠ 0 := ne_of_gt hk
  have haff := base_affine k p c e r h d hne
  have hw : 0 ≤ 1-d/k := by
    have hle : d/k ≤ 1 := (div_le_one hk).mpr hdk
    linarith
  have hpos : 0 ≤ (1-d/k)*(e/2) := mul_nonneg hw (by linarith)
  have hexp : (1-d/k)*(base k p c e r h 0-e/2)+(d/k)*base k p c e r h k
      = ((1-d/k)*base k p c e r h 0+(d/k)*base k p c e r h k)-(1-d/k)*(e/2) := by ring
  unfold riskGen
  rw [risk0_eq k p c e r h, hexp, haff]
  linarith

/-- The decision `d = 1` is dominated by the same mixture, because its expected
correction `b (k - h) / k` never exceeds the mixture's `(k - 1) e / k`.
This is the step the LP tables cannot supply. -/
theorem dominance_one (k p c e r b h : ℝ) (hk : 0 < k) (hb : 0 ≤ b) (hbe : b ≤ e)
    (hh1 : 1 ≤ h) (hhk : h ≤ k) :
    (1-1/k)*risk0 e r h+(1/k)*base k p c e r h k ≤ riskOne k p c e r b h := by
  have hne : k ≠ 0 := ne_of_gt hk
  have he : 0 ≤ e := le_trans hb hbe
  have hkh : 0 ≤ k-h := by linarith
  have haff := base_affine k p c e r h 1 hne
  have hexp : (1-1/k)*(base k p c e r h 0-e/2)+(1/k)*base k p c e r h k
      = ((1-1/k)*base k p c e r h 0+(1/k)*base k p c e r h k)-(1-1/k)*(e/2) := by ring
  have hnum : 0 ≤ e*(k-1)-b*(k-h) := by
    nlinarith [mul_nonneg he (by linarith : (0:ℝ) ≤ h-1),
      mul_nonneg (by linarith : (0:ℝ) ≤ e-b) hkh]
  have hsplit : (1-1/k)*(e/2)-b*(k-h)/k/2 = (e*(k-1)-b*(k-h))/(2*k) := by
    field_simp <;> ring
  have hkey : b*(k-h)/k/2 ≤ (1-1/k)*(e/2) := by
    have hdiv : 0 ≤ (e*(k-1)-b*(k-h))/(2*k) := div_nonneg hnum (by linarith)
    linarith
  unfold riskOne
  rw [risk0_eq k p c e r h, hexp, haff]
  linarith

/-! ## L2: the endpoint-world reduction -/

/-- `x ↦ max e (r * x)` is convex, in the explicit segment form needed below. -/
theorem max_affine_convex (e r x y l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    max e (r*((1-l)*x+l*y)) ≤ (1-l)*max e (r*x)+l*max e (r*y) := by
  have hx : r*x ≤ max e (r*x) := le_max_right _ _
  have hy : r*y ≤ max e (r*y) := le_max_right _ _
  have hex : e ≤ max e (r*x) := le_max_left _ _
  have hey : e ≤ max e (r*y) := le_max_left _ _
  have hl' : 0 ≤ 1-l := by linarith
  rcases le_total (r*((1-l)*x+l*y)) e with hcase|hcase
  · rw [max_eq_left hcase]
    nlinarith [mul_nonneg hl' (sub_nonneg.mpr hex), mul_nonneg hl0 (sub_nonneg.mpr hey)]
  · rw [max_eq_right hcase]
    nlinarith [mul_nonneg hl' (sub_nonneg.mpr hx), mul_nonneg hl0 (sub_nonneg.mpr hy)]

/-- The two-action decision: `d = 0` with probability `q`, `d = k` otherwise. -/
def mixRisk (k p c e r q h : ℝ) : ℝ := q*risk0 e r h+(1-q)*base k p c e r h k

theorem mixRisk_convex (k p c e r q x y l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) :
    mixRisk k p c e r q ((1-l)*x+l*y)
      ≤ (1-l)*mixRisk k p c e r q x+l*mixRisk k p c e r q y := by
  have key := max_affine_convex e r x y l hl0 hl1
  have hid : (1-l)*mixRisk k p c e r q x+l*mixRisk k p c e r q y
      -mixRisk k p c e r q ((1-l)*x+l*y)
      = ((1-l)*max e (r*x)+l*max e (r*y)-max e (r*((1-l)*x+l*y)))/2 := by
    unfold mixRisk risk0 base; ring
  linarith

/-- Hence the worst hidden intersection is an endpoint: `h = 1` or `h = k`.
No world in the interior can beat both. -/
theorem endpoint_max (k p c e r q h : ℝ) (hk : 1 < k) (hh1 : 1 ≤ h) (hhk : h ≤ k) :
    mixRisk k p c e r q h ≤ max (mixRisk k p c e r q 1) (mixRisk k p c e r q k) := by
  have hk1 : (0:ℝ) < k-1 := by linarith
  have hne : k-1 ≠ 0 := ne_of_gt hk1
  set l : ℝ := (h-1)/(k-1) with hldef
  have hl0 : 0 ≤ l := div_nonneg (by linarith) hk1.le
  have hl1 : l ≤ 1 := (div_le_one hk1).mpr (by linarith)
  have hlk : l*(k-1) = h-1 := by rw [hldef]; field_simp
  have hz : (1-l)*1+l*k = h := by linarith
  have hc := mixRisk_convex k p c e r q 1 k l hl0 hl1
  rw [hz] at hc
  have hA : mixRisk k p c e r q 1 ≤ max (mixRisk k p c e r q 1) (mixRisk k p c e r q k) :=
    le_max_left _ _
  have hB : mixRisk k p c e r q k ≤ max (mixRisk k p c e r q 1) (mixRisk k p c e r q k) :=
    le_max_right _ _
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1-l) (sub_nonneg.mpr hA),
    mul_nonneg hl0 (sub_nonneg.mpr hB)]

/-! ## L3: the matching 2x2 certificate -/

def uOne (r e : ℝ) : ℝ := (max 0 (r-e))/2
def vTerm (k p e r : ℝ) : ℝ := (p*(k-1)+max 0 (e-r))/2
def uTop (k r e : ℝ) : ℝ := (k*r-e)/2
def phaseValue (k p c e r : ℝ) : ℝ := uTop k r e*vTerm k p e r/(c*(k-1))

/-- The full formula, valid on both sides of the threshold. -/
def phaseValueFull (k p c e r : ℝ) : ℝ :=
  (max 0 (k*r-e))*(p*(k-1)+max 0 (e-r))/(4*(c*(k-1)))

theorem max_diff (x y : ℝ) : max 0 (y-x)-max 0 (x-y) = y-x := by
  rcases le_total x y with h|h
  · rw [max_eq_right (by linarith : (0:ℝ) ≤ y-x), max_eq_left (by linarith : x-y ≤ (0:ℝ))]
    ring
  · rw [max_eq_left (by linarith : y-x ≤ (0:ℝ)), max_eq_right (by linarith : (0:ℝ) ≤ x-y)]
    ring

/-- The denominator of the game value is exactly `c (k - 1)`. This is where
`p + r = 2c` (i.e. `(rho - 2b) + (2a - rho) = 2(a - b)`) does all the work, and
it is why the correction `e` cancels out of the denominator but not the value. -/
theorem denom_eq (k p c e r : ℝ) (hpr : p+r = 2*c) :
    uTop k r e-uOne r e+vTerm k p e r = c*(k-1) := by
  unfold uTop uOne vTerm
  have h := max_diff r e
  have hmul : (p+r)*(k-1) = 2*c*(k-1) := by rw [hpr]
  linarith

/-- Both equalisers for an abstract 2x2 matrix `[[u, v], [U, 0]]` whose
denominator is `D = U - u + v`. Primal mixes the two decisions, dual mixes the
two endpoint worlds; all four products equal `U v / D`. -/
theorem equalizer_generic (U u v D : ℝ) (hD : D ≠ 0) (hDef : U = D+u-v) :
    ((v/D)*u+(1-v/D)*v = U*v/D) ∧ ((v/D)*U+(1-v/D)*0 = U*v/D) ∧
    ((1-(v-u)/D)*u+((v-u)/D)*U = U*v/D) ∧ ((1-(v-u)/D)*v+((v-u)/D)*0 = U*v/D) := by
  subst hDef
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp <;> ring
  · field_simp <;> ring
  · field_simp <;> ring
  · field_simp <;> ring

theorem phase_equalizers (k p c e r : ℝ) (hpr : p+r = 2*c) (hD : c*(k-1) ≠ 0) :
    ((vTerm k p e r/(c*(k-1)))*uOne r e
        +(1-vTerm k p e r/(c*(k-1)))*vTerm k p e r = phaseValue k p c e r) ∧
    ((vTerm k p e r/(c*(k-1)))*uTop k r e
        +(1-vTerm k p e r/(c*(k-1)))*0 = phaseValue k p c e r) ∧
    ((1-(vTerm k p e r-uOne r e)/(c*(k-1)))*uOne r e
        +((vTerm k p e r-uOne r e)/(c*(k-1)))*uTop k r e = phaseValue k p c e r) ∧
    ((1-(vTerm k p e r-uOne r e)/(c*(k-1)))*vTerm k p e r
        +((vTerm k p e r-uOne r e)/(c*(k-1)))*0 = phaseValue k p c e r) := by
  have hd := denom_eq k p c e r hpr
  have hDef : uTop k r e = c*(k-1)+uOne r e-vTerm k p e r := by linarith
  exact equalizer_generic (uTop k r e) (uOne r e) (vTerm k p e r) (c*(k-1)) hD hDef

/-! ## Weights are legitimate probabilities -/

theorem uOne_le_uTop (k r e : ℝ) (hk : 1 ≤ k) (hr : 0 ≤ r) (hact : e ≤ k*r) :
    uOne r e ≤ uTop k r e := by
  unfold uOne uTop
  rcases le_total r e with h|h
  · rw [max_eq_left (by linarith : r-e ≤ (0:ℝ))]; linarith
  · rw [max_eq_right (by linarith : (0:ℝ) ≤ r-e)]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ k-1) hr]

theorem uOne_le_vTerm (k p e r : ℝ) (hk : 3 ≤ k) (hp : 1/2 ≤ p) (hr1 : r ≤ 1)
    (he : 0 ≤ e) : uOne r e ≤ vTerm k p e r := by
  unfold uOne vTerm
  rcases le_total r e with h|h
  · rw [max_eq_left (by linarith : r-e ≤ (0:ℝ))]
    have : 0 ≤ max 0 (e-r) := le_max_left _ _
    nlinarith
  · rw [max_eq_right (by linarith : (0:ℝ) ≤ r-e)]
    have hm : 0 ≤ max 0 (e-r) := le_max_left _ _
    nlinarith

theorem uTop_nonneg (k r e : ℝ) (hact : e ≤ k*r) : 0 ≤ uTop k r e := by
  unfold uTop; linarith

theorem vTerm_nonneg (k p e r : ℝ) (hk : 1 ≤ k) (hp : 0 ≤ p) : 0 ≤ vTerm k p e r := by
  unfold vTerm
  have hm : 0 ≤ max 0 (e-r) := le_max_left _ _
  nlinarith

theorem weights_valid (k p c e r : ℝ) (hk : 3 ≤ k) (he : 0 ≤ e) (hr : 0 ≤ r)
    (hr1 : r ≤ 1) (hp : 1/2 ≤ p) (hact : e ≤ k*r) (hpr : p+r = 2*c)
    (hc : 0 < c*(k-1)) :
    0 ≤ vTerm k p e r/(c*(k-1)) ∧ vTerm k p e r/(c*(k-1)) ≤ 1 ∧
    0 ≤ (vTerm k p e r-uOne r e)/(c*(k-1)) ∧
    (vTerm k p e r-uOne r e)/(c*(k-1)) ≤ 1 := by
  have hd := denom_eq k p c e r hpr
  have hv := vTerm_nonneg k p e r (by linarith) (by linarith)
  have hU := uTop_nonneg k r e hact
  have h1 := uOne_le_uTop k r e (by linarith) hr hact
  have h2 := uOne_le_vTerm k p e r hk hp hr1 he
  refine ⟨div_nonneg hv hc.le, (div_le_one hc).mpr (by linarith),
    div_nonneg (by linarith) hc.le, (div_le_one hc).mpr (by linarith)⟩

/-! ## The value, the threshold, and the corner specialisation -/

theorem phaseValueFull_eq (k p c e r : ℝ) (hact : e ≤ k*r) (hD : c*(k-1) ≠ 0) :
    phaseValueFull k p c e r = phaseValue k p c e r := by
  unfold phaseValueFull phaseValue uTop vTerm
  rw [max_eq_right (by linarith : (0:ℝ) ≤ k*r-e)]
  field_simp
  ring

/-- Above the phase boundary `k r <= e` the value collapses to zero: the
decision `d = 0` is optimal in every world. This is the finite-`k` form of
`2 (1 + tau) exp (-2 tau) = rho`. -/
theorem phaseValueFull_zero (k p c e r : ℝ) (hinact : k*r ≤ e) :
    phaseValueFull k p c e r = 0 := by
  unfold phaseValueFull
  rw [max_eq_left (by linarith : k*r-e ≤ (0:ℝ))]
  simp

/-- At the corner reference `a = 1, b = 0` we have `c = 1`, `e = 0`, `p = rho`,
`r = 2 - rho`, and the general value collapses to the already published corner
law. The corner law is therefore a special case, not an independent result. -/
theorem corner_value (k rho : ℝ) (hk : 1 < k) (hr1 : 1 ≤ rho) (hr2 : rho ≤ 2) :
    phaseValueFull k rho 1 0 (2-rho) = k*rho*(2-rho)/4 := by
  have hk1 : (0:ℝ) < k-1 := by linarith
  have hne : k-1 ≠ 0 := ne_of_gt hk1
  unfold phaseValueFull
  rw [max_eq_right (by nlinarith : (0:ℝ) ≤ k*(2-rho)-0),
    max_eq_left (by linarith : (0:ℝ)-(2-rho) ≤ (0:ℝ))]
  field_simp
  ring

#print axioms risk0_eq
#print axioms base_affine
#print axioms dominance_gen
#print axioms dominance_one
#print axioms max_affine_convex
#print axioms mixRisk_convex
#print axioms endpoint_max
#print axioms max_diff
#print axioms denom_eq
#print axioms equalizer_generic
#print axioms phase_equalizers
#print axioms uOne_le_uTop
#print axioms uOne_le_vTerm
#print axioms uTop_nonneg
#print axioms vTerm_nonneg
#print axioms weights_valid
#print axioms phaseValueFull_eq
#print axioms phaseValueFull_zero
#print axioms corner_value

end
end CIGAMF.P13.D6ReferencePhaseValue
