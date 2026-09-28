import Mathlib

/-!
# A finite exact region of the Functional extrema-crossover game

This module closes the three-cost algebra after the symmetry/interval-oracle
reduction.  The reduction itself is intentionally not smuggled in: the theorem
is stated for the reduced score `min JEE (min JEM JMM)`.
-/
namespace CIGAMF.P13.FunctionalCrossoverExactRegion

noncomputable section

def JEE (Delta p q : ℝ) : ℝ := p*q*Delta^2/(8*(p+q))
def JEM (x a p q u : ℝ) : ℝ :=
  a*p*q*u/(2*(x^2*p*q+2*p*u+4*q*u))
def JMM (x p u : ℝ) : ℝ := p*u/(4*(x^2*p+2*u))
def reducedScore (x a Delta p q u : ℝ) : ℝ :=
  min (JEE Delta p q) (min (JEM x a p q u) (JMM x p u))

def H (x : ℝ) : ℝ := x+2+Real.sqrt 2
def pStar (x : ℝ) : ℝ := 2/H x
def qStar (x : ℝ) : ℝ := Real.sqrt 2/H x
def uStar (x : ℝ) : ℝ := x/H x

lemma sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
lemma sqrt_two_sq : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)

theorem star_simplex (x : ℝ) (hx : 0 < x) :
    0 < pStar x ∧ 0 < qStar x ∧ 0 < uStar x ∧
      pStar x+qStar x+uStar x=1 := by
  have hH : 0 < H x := by unfold H; positivity
  unfold pStar qStar uStar
  refine ⟨by positivity,by positivity,by positivity,?_⟩
  unfold H
  field_simp
  ring

/-- Three-variable Engel/Cauchy identity used for the global `JEM` cap. -/
theorem three_cost_identity (x p q u : ℝ) (hp : p≠0) (hq : q≠0) (hu : u≠0) :
    (x^2/u+2/q+4/p)*(p+q+u)-(H x)^2 =
      (x*q-Real.sqrt 2*u)^2/(u*q) +
      (x*p-2*u)^2/(u*p) +
      (Real.sqrt 2*p-2*q)^2/(q*p) := by
  unfold H
  field_simp
  linear_combination (-(q*u*p) - u*p^2 - u^2*p) * sqrt_two_sq

theorem three_cost_lower (x p q u : ℝ) (hp : 0<p) (hq : 0<q) (hu : 0<u)
    (hsum : p+q+u=1) : (H x)^2 ≤ x^2/u+2/q+4/p := by
  have hid := three_cost_identity x p q u (ne_of_gt hp) (ne_of_gt hq) (ne_of_gt hu)
  rw [hsum,mul_one] at hid
  have h1 : 0 ≤ (x*q-Real.sqrt 2*u)^2/(u*q) := by positivity
  have h2 : 0 ≤ (x*p-2*u)^2/(u*p) := by positivity
  have h3 : 0 ≤ (Real.sqrt 2*p-2*q)^2/(q*p) := by positivity
  linarith

theorem JEM_reciprocal (x a p q u : ℝ)
    (ha : a≠0) (hp : p≠0) (hq : q≠0) (hu : u≠0) :
    1/JEM x a p q u = (2/a)*(x^2/u+2/q+4/p) := by
  unfold JEM
  field_simp

theorem JEM_upper (x a p q u : ℝ) (hx : 0<x) (ha : 0<a)
    (hp : 0<p) (hq : 0<q) (hu : 0<u) (hsum : p+q+u=1) :
    JEM x a p q u ≤ a/(2*(H x)^2) := by
  have hH : 0 < H x := by unfold H; positivity
  have hcost : 0 < x^2/u+2/q+4/p := by positivity
  have hc := three_cost_lower x p q u hp hq hu hsum
  have hformula : JEM x a p q u = a/(2*(x^2/u+2/q+4/p)) := by
    unfold JEM
    field_simp
  rw [hformula]
  apply (div_le_div_iff₀ (by positivity : 0 < 2*(x^2/u+2/q+4/p))
    (by positivity : 0 < 2*(H x)^2)).2
  nlinarith

theorem star_JEM (x a : ℝ) (hx : 0<x) :
    JEM x a (pStar x) (qStar x) (uStar x)=a/(2*(H x)^2) := by
  have hH : 0 < H x := by unfold H; positivity
  unfold JEM pStar qStar uStar
  field_simp
  unfold H
  linear_combination (2*a) * sqrt_two_sq

theorem star_JEE_lower (x a Delta : ℝ) (hx : 0<x) (ha : 0≤a)
    (hregion : (2+2*Real.sqrt 2)*a ≤ Delta^2*H x) :
    a/(2*(H x)^2) ≤ JEE Delta (pStar x) (qStar x) := by
  have hH : 0 < H x := by unfold H; positivity
  have hs := sqrt_two_pos
  unfold JEE pStar qStar
  field_simp
  nlinarith [sqrt_two_sq]

theorem star_JMM_lower (x a : ℝ) (hx : 0<x) (ha : 0≤a)
    (hregion : 2*a*(x+1) ≤ H x) :
    a/(2*(H x)^2) ≤ JMM x (pStar x) (uStar x) := by
  have hH : 0 < H x := by unfold H; positivity
  unfold JMM pStar uStar
  field_simp
  nlinarith

/-- Exact reduced optimum on the region where EE and MM are above the EM
bottleneck. -/
theorem exact_reduced_region (x a Delta : ℝ) (hx : 0<x) (ha : 0<a)
    (hEE : (2+2*Real.sqrt 2)*a ≤ Delta^2*H x)
    (hMM : 2*a*(x+1) ≤ H x) :
    IsGreatest
      {v | ∃ p q u : ℝ, 0<p ∧ 0<q ∧ 0<u ∧ p+q+u=1 ∧
        v=reducedScore x a Delta p q u}
      (a/(2*(H x)^2)) := by
  have hs := star_simplex x hx
  refine ⟨⟨pStar x,qStar x,uStar x,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,?_⟩,?_⟩
  · unfold reducedScore
    rw [star_JEM x a hx]
    rw [min_eq_left (star_JMM_lower x a hx ha.le hMM)]
    rw [min_eq_right (star_JEE_lower x a Delta hx ha.le hEE)]
  · rintro v ⟨p,q,u,hp,hq,hu,hsum,rfl⟩
    exact (min_le_right _ _).trans ((min_le_left _ _).trans
      (JEM_upper x a p q u hx ha hp hq hu hsum))

#print axioms three_cost_identity
#print axioms three_cost_lower
#print axioms JEM_upper
#print axioms star_JEM
#print axioms star_JEE_lower
#print axioms star_JMM_lower
#print axioms exact_reduced_region

end
end CIGAMF.P13.FunctionalCrossoverExactRegion
