import LeanMasterAnchorCertificateV1

/-!
A genuine two-sided calibration threshold for a finite Gaussian model.
There are m+1 ordinary queries, all with unit variance/price. At the true
world the mean vector is a*e_0; alternative u has mean a*e_u. A common
unknown offset is profiled out. The anchor observes that offset with unit
variance and price c. Thus these are distinct-answer worlds, not tie points.

For m >= 2 the anchor-free value is V = a^2*(m+3)^2/(8*(m+1)^2).
The exact critical price is cStar = (m-1)^2/(m+3)^2. Above it a dual
bounds EVERY allocation. Below it an explicit feasible allocation improves
EVERY alternative. No numerical optimizer, active-set tolerance, or
assumed optimal value enters these statements.
-/
namespace CIGAMF.P13.MasterAnchorThreshold
open Finset
open scoped BigOperators
noncomputable section

def xWeight (m : ℝ) := (m^2+m+2)/(2*(m+1)^2)
def yWeight (m : ℝ) := (m+3)/(2*(m+1)^2)
def baseValue (m a : ℝ) := a^2*(m+3)^2/(8*(m+1)^2)
def criticalPrice (m : ℝ) := (m-1)^2/(m+3)^2
def shift (m a : ℝ) := a*(m-1)/(2*(m+1))
def profile (a x y K : ℝ) := a^2*(x+y)/2 - (a*(x-y))^2/(2*K)
def energy (a x y K t : ℝ) := a^2*(x+y)/2 - a*(x-y)*t + K*t^2/2

/-- The profiled quantity is the actual infimum of the scalar nuisance quadratic. -/
theorem profile_le_energy (a x y K t : ℝ) (hK : 0 < K) :
    profile a x y K ≤ energy a x y K t := by
  have hKne : K ≠ 0 := ne_of_gt hK
  have hsq : 0 ≤ (K/2)*(t - a*(x-y)/K)^2 := by positivity
  have hexp : (K/2)*(t - a*(x-y)/K)^2
      = K*t^2/2 - a*(x-y)*t + (a*(x-y))^2/(2*K) := by
    field_simp
    ring
  rw [hexp] at hsq
  unfold profile energy
  linarith

theorem profile_attained (a x y K : ℝ) (hK : 0 < K) :
    energy a x y K (a*(x-y)/K) = profile a x y K := by
  unfold energy profile
  field_simp
  <;> ring

/-- Original per-query Gaussian information, before profiling the common offset. -/
def queryEnergy {m : ℕ} (a x : ℝ) (w : Fin m → ℝ) (x0 : ℝ)
    (u : Fin m) (t : ℝ) : ℝ :=
  x*(a-t)^2/2 + (∑ i, w i*((if i = u then -a else 0)-t)^2/2) + x0*t^2/2

theorem queryEnergy_eq {m : ℕ} (a x : ℝ) (w : Fin m → ℝ) (x0 : ℝ)
    (u : Fin m) (t : ℝ) :
    queryEnergy a x w x0 u t = energy a x (w u) (x + ∑ i, w i + x0) t := by
  classical
  have hi : ∀ i : Fin m, w i*((if i = u then -a else 0)-t)^2/2 =
      w i*t^2/2 + if i = u then w i*(a^2+2*a*t)/2 else 0 := by
    intro i
    by_cases h : i = u <;> simp [h] <;> ring
  unfold queryEnergy energy
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  ring

theorem weights (m : ℝ) (hm : 2 ≤ m) :
    0 < xWeight m ∧ 0 < yWeight m ∧ xWeight m + m*yWeight m = 1 := by
  have h1 : 0 < m+1 := by linarith
  have h3 : 0 < m+3 := by linarith
  have hmpos : 0 < m := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold xWeight
    positivity
  · unfold yWeight
    positivity
  · unfold xWeight yWeight
    field_simp
    <;> ring

theorem base_positive (m a : ℝ) (hm : 2 ≤ m) (ha : 0 < a) :
    0 < baseValue m a := by
  unfold baseValue
  have : 0 < m+1 := by linarith
  have : 0 < m+3 := by linarith
  positivity

theorem critical_range (m : ℝ) (hm : 2 ≤ m) :
    0 < criticalPrice m ∧ criticalPrice m < 1 := by
  have h1 : 0 < m-1 := by linarith
  have h3 : 0 < m+3 := by linarith
  unfold criticalPrice
  constructor
  · positivity
  · apply (div_lt_one (sq_pos_of_pos h3)).2
    nlinarith

theorem base_attained (m a : ℝ) (hm : 2 ≤ m) :
    profile a (xWeight m) (yWeight m) 1 = baseValue m a := by
  have h1 : m+1 ≠ 0 := by linarith
  unfold profile xWeight yWeight baseValue
  field_simp
  <;> ring

/-- Every ordinary query has the SAME dual coefficient, not merely the support queries. -/
theorem ordinary_dual (m a : ℝ) (hm : 2 ≤ m) :
    (a-shift m a)^2/2 = baseValue m a ∧
    ((a+shift m a)^2+(m-1)*(shift m a)^2)/(2*m) = baseValue m a := by
  have h1 : m+1 ≠ 0 := by linarith
  have hm0 : m ≠ 0 := by linarith
  unfold shift baseValue
  constructor <;> field_simp <;> ring

theorem anchor_dual (m a : ℝ) (hm : 2 ≤ m) :
    (shift m a)^2/2 = criticalPrice m * baseValue m a := by
  have h1 : m+1 ≠ 0 := by linarith
  have h3 : m+3 ≠ 0 := by linarith
  unfold shift criticalPrice baseValue
  field_simp
  <;> ring

/-- Averaging the actual nuisance quadratics over all alternative worlds. -/
theorem sum_energy {m : ℕ} (a x : ℝ) (w : Fin m → ℝ) (x0 t : ℝ) :
    (∑ u, energy a x (w u) (x + ∑ i, w i + x0) t) =
    (m:ℝ)*((a-t)^2/2)*x + ((a+t)^2+((m:ℝ)-1)*t^2)/2*(∑ i, w i)
      + (m:ℝ)*x0*t^2/2 := by
  have he : ∀ u : Fin m,
      energy a x (w u) (x + ∑ i, w i + x0) t =
      (a^2*x/2-a*x*t+(x + ∑ i, w i + x0)*t^2/2) +
        (a^2/2+a*t)*w u := by
    intro u
    unfold energy
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring

/-- Global dual: valid for EVERY feasible allocation, including nonsymmetric ones. -/
theorem global_upper {m : ℕ} (hm : 2 ≤ m) (a c x x0 : ℝ) (w : Fin m → ℝ)
    (hx0 : 0 ≤ x0) (hbudget : x + ∑ i, w i + c*x0 = 1)
    (hK : 0 < x + ∑ i, w i + x0)
    (hc : criticalPrice m ≤ c) :
    ∃ u, profile a x (w u) (x + ∑ i, w i + x0) ≤ baseValue m a := by
  have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hb : 0 ≤ baseValue m a := by unfold baseValue; positivity
  have hd := ordinary_dual (m:ℝ) a hmr
  have hda := anchor_dual (m:ℝ) a hmr
  have hcoef : ((a+shift m a)^2+((m:ℝ)-1)*(shift m a)^2)/2 =
      (m:ℝ)*baseValue m a := by
    have he := hd.2
    field_simp at he
    nlinarith
  have hsum := sum_energy a x w x0 (shift m a)
  rw [hd.1, hcoef] at hsum
  have hanchor : x0*(shift m a)^2/2 ≤ c*x0*baseValue m a := by
    have he : x0*(shift m a)^2/2 = x0*(criticalPrice m*baseValue m a) := by
      rw [← hda]; ring
    rw [he]
    nlinarith [mul_nonneg hx0 hb, mul_nonneg (sub_nonneg.mpr hc) (mul_nonneg hx0 hb)]
  have hcap : (∑ u, energy a x (w u) (x + ∑ i, w i + x0) (shift m a))
      ≤ (m:ℝ)*baseValue m a := by
    calc
      (∑ u, energy a x (w u) (x + ∑ i, w i + x0) (shift m a)) =
          (m:ℝ)*baseValue m a*x + (m:ℝ)*baseValue m a*(∑ i, w i) +
            (m:ℝ)*(x0*(shift m a)^2/2) := by rw [hsum]; ring
      _ ≤ (m:ℝ)*baseValue m a*x + (m:ℝ)*baseValue m a*(∑ i, w i) +
            (m:ℝ)*(c*x0*baseValue m a) :=
        by have hmul := mul_le_mul_of_nonneg_left hanchor (le_of_lt hmpos); linarith
      _ = (m:ℝ)*baseValue m a*(x + ∑ i, w i + c*x0) := by ring
      _ = (m:ℝ)*baseValue m a := by rw [hbudget, mul_one]
  by_contra hn
  push_neg at hn
  have hlt : (∑ _u : Fin m, baseValue m a) <
      ∑ u, energy a x (w u) (x + ∑ i, w i + x0) (shift m a) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    · intro u _
      exact lt_of_lt_of_le (hn u) (profile_le_energy a x (w u) _ _ hK)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  linarith

/-- The polynomial core of the gain, with every denominator already cleared. -/
theorem gain_poly (m c z : ℝ) :
    2*(1-c*z)*(m^2+2*m+5)*(1+(1-c)*z) - (1-c*z)^2*(m-1)^2
      - (m+3)^2*(1+(1-c)*z)
      = z*((m-1)^2 - c*(m+3)^2 - c*((1-c)*(m+3)^2+(m-1)^2)*z) := by
  ring

theorem weight_sum (m : ℝ) (h1 : m+1 ≠ 0) :
    xWeight m + yWeight m = (m^2+2*m+5)/(2*(m+1)^2) := by
  unfold xWeight yWeight
  field_simp
  ring

theorem weight_diff (m : ℝ) (h1 : m+1 ≠ 0) :
    xWeight m - yWeight m = (m-1)/(2*(m+1)) := by
  unfold xWeight yWeight
  field_simp
  ring

/-- The gain with every denominator cleared, for an ARBITRARY non-zero `K`.  Keeping
`K` an atom is what lets `field_simp` finish: the only inverses are `m+1` and `K`, and
both have a hypothesis in exactly that shape. -/
theorem gain_cleared (m a c z K : ℝ) (h1 : m+1 ≠ 0) (hK : K ≠ 0) :
    (profile a ((1-c*z)*xWeight m) ((1-c*z)*yWeight m) K - baseValue m a) * K
      * (8*(m+1)^2)
      = a^2 * (2*(1-c*z)*(m^2+2*m+5)*K - (1-c*z)^2*(m-1)^2 - (m+3)^2*K) := by
  unfold profile xWeight yWeight baseValue
  field_simp
  ring

/-- Exact gain on the explicit ray that scales ordinary queries to buy the anchor. -/
theorem gain_identity (m a c z : ℝ) (hm : 2 ≤ m)
    (hden : 1+(1-c)*z ≠ 0) :
    (profile a ((1-c*z)*xWeight m) ((1-c*z)*yWeight m) (1+(1-c)*z)
      - baseValue m a) * (1+(1-c)*z) * (8*(m+1)^2)
      = a^2 * z * ((m-1)^2 - c*(m+3)^2 - c*((1-c)*(m+3)^2+(m-1)^2)*z) := by
  have h1 : m+1 ≠ 0 := by linarith
  rw [gain_cleared m a c z (1+(1-c)*z) h1 hden, gain_poly m c z]
  ring

def purchase (m c : ℝ) := (criticalPrice m-c)/(2*c*(1-c+criticalPrice m))

theorem purchase_properties (m c : ℝ) (hm : 2 ≤ m)
    (hc : 0 < c) (hlt : c < criticalPrice m) :
    0 < purchase m c ∧ c*purchase m c < 1 ∧
    0 < (criticalPrice m-c)-c*(1-c+criticalPrice m)*purchase m c := by
  have hr := critical_range m hm
  have hd : 0 < 1-c+criticalPrice m := by linarith
  have hz : 0 < purchase m c := by unfold purchase; positivity
  have he : c*(1-c+criticalPrice m)*purchase m c = (criticalPrice m-c)/2 := by
    unfold purchase
    field_simp
    <;> ring
  refine ⟨hz, ?_, ?_⟩
  · nlinarith [mul_pos hc hz]
  · rw [he]; linarith

/-- Explicit lower certificate below the price threshold, valid for every alternative. -/
theorem below_threshold (m a c : ℝ) (hm : 2 ≤ m) (ha : 0 < a)
    (hc : 0 < c) (hlt : c < criticalPrice m) :
    let z := purchase m c
    0 < z ∧ 0 < (1-c*z)*xWeight m ∧ 0 < (1-c*z)*yWeight m ∧
    (1-c*z)*xWeight m + m*((1-c*z)*yWeight m) + c*z = 1 ∧
    baseValue m a < profile a ((1-c*z)*xWeight m) ((1-c*z)*yWeight m)
      ((1-c*z)*xWeight m + m*((1-c*z)*yWeight m) + z) := by
  dsimp only
  have hp := purchase_properties m c hm hc hlt
  have hw := weights m hm
  have hr := critical_range m hm
  have hzden : 0 < 1+(1-c)*purchase m c := by nlinarith
  have hscale : 0 < 1-c*purchase m c := by linarith
  have hbudget : (1-c*purchase m c)*xWeight m +
      m*((1-c*purchase m c)*yWeight m) + c*purchase m c = 1 := by
    nlinarith [hw.2.2]
  refine ⟨hp.1, mul_pos hscale hw.1, mul_pos hscale hw.2.1, hbudget, ?_⟩
  have hK : (1-c*purchase m c)*xWeight m +
      m*((1-c*purchase m c)*yWeight m) + purchase m c =
      1+(1-c)*purchase m c := by nlinarith [hbudget]
  rw [hK]
  have hg := gain_identity m a c (purchase m c) hm (ne_of_gt hzden)
  have h3 : (0:ℝ) < (m+3)^2 := by nlinarith
  have hbr : 0 < (m-1)^2 - c*(m+3)^2
      - c*((1-c)*(m+3)^2+(m-1)^2)*(purchase m c) := by
    have hcp : criticalPrice m * (m+3)^2 = (m-1)^2 := by
      unfold criticalPrice
      field_simp
    nlinarith [hp.2.2, h3, hcp]
  have hpos : 0 < a^2 * purchase m c
      * ((m-1)^2 - c*(m+3)^2 - c*((1-c)*(m+3)^2+(m-1)^2)*(purchase m c)) := by
    have ha2 : 0 < a^2 := by positivity
    exact mul_pos (mul_pos ha2 hp.1) hbr
  have h8 : (0:ℝ) < 8*(m+1)^2 := by nlinarith
  have hprod : 0 < (profile a ((1-c*purchase m c)*xWeight m)
      ((1-c*purchase m c)*yWeight m) (1+(1-c)*purchase m c) - baseValue m a)
      * (1+(1-c)*purchase m c) * (8*(m+1)^2) := by
    rw [hg]
    calc (0:ℝ) < a^2 * purchase m c
          * ((m-1)^2 - c*(m+3)^2
             - c*((1-c)*(m+3)^2+(m-1)^2)*(purchase m c)) := hpos
      _ = a^2 * purchase m c
          * ((m-1)^2 - c*(m+3)^2
             - c*((1-c)*(m+3)^2+(m-1)^2)*(purchase m c)) := rfl
  by_contra hcon
  push_neg at hcon
  have step1 : 0 ≤ baseValue m a
      - profile a ((1-c*purchase m c)*xWeight m) ((1-c*purchase m c)*yWeight m)
        (1+(1-c)*purchase m c) := by linarith
  have step2 : 0 ≤ (baseValue m a
      - profile a ((1-c*purchase m c)*xWeight m) ((1-c*purchase m c)*yWeight m)
        (1+(1-c)*purchase m c)) * (1+(1-c)*purchase m c) :=
    mul_nonneg step1 (le_of_lt hzden)
  have step3 : 0 ≤ (baseValue m a
      - profile a ((1-c*purchase m c)*xWeight m) ((1-c*purchase m c)*yWeight m)
        (1+(1-c)*purchase m c)) * (1+(1-c)*purchase m c) * (8*(m+1)^2) :=
    mul_nonneg step2 (le_of_lt h8)
  nlinarith [hprod, step3]

/-- Mandatory purchase needs only separated certificates, not an exact full optimum. -/
theorem anchor_required {Design : Type*} (feasible : Design → Prop)
    (exposure value : Design → ℝ) (U L : ℝ)
    (hfree : ∀ d, feasible d → exposure d = 0 → value d ≤ U)
    (hgap : U < L) (d : Design) (hd : feasible d)
    (hx : 0 ≤ exposure d) (hv : L ≤ value d) : 0 < exposure d := by
  by_contra hn
  have hz : exposure d = 0 := le_antisymm (le_of_not_gt hn) hx
  have := hfree d hd hz
  linarith

#print axioms queryEnergy_eq
#print axioms profile_le_energy
#print axioms profile_attained
#print axioms weights
#print axioms base_attained
#print axioms ordinary_dual
#print axioms anchor_dual
#print axioms global_upper
#print axioms gain_poly
#print axioms gain_cleared
#print axioms weight_sum
#print axioms weight_diff
#print axioms gain_identity
#print axioms purchase_properties
#print axioms below_threshold
#print axioms anchor_required
end
end CIGAMF.P13.MasterAnchorThreshold
