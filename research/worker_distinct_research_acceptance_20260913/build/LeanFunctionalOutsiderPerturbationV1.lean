import «LeanFunctionalFlatOutsiderRateV1»

/-! Uniform-in-K robustness of the flat-outsider benchmark. The incumbent
stays at (0,1); outsider means may vary within any interval of width rho<1. -/
namespace CIGAMF.P13.FunctionalOutsiderPerturbation
open scoped BigOperators
open CIGAMF.P13.FunctionalFlatOutsiderRate
noncomputable section

def PerturbedAlternative {K : ℕ} (theta : Fin K → ℝ) (x y : ℝ) (z : Fin K → ℝ) : Prop :=
  ∃ a b,a ≠ b ∧ |y-x| ≤ (theta a+z a)-(theta b+z b)

lemma scaled_square_lower (s delta u d : ℝ) (hs : 0 < s) (hd : 0 < delta)
    (h : delta ≤ u+d) :
    delta^2*rate s ≤ u^2/(4*(2+s))+d^2/(2*s*(2+s)) := by
  have hn : 1 ≤ u/delta+d/delta := by
    rw [← add_div,le_div_iff₀ hd]
    simpa using h
  have hh := mul_le_mul_of_nonneg_left (weighted_square_lower s (u/delta) (d/delta) hs hn)
    (sq_nonneg delta)
  have hH : 0 < 2+s := by linarith
  have he : delta^2*((u/delta)^2/(4*(2+s))+(d/delta)^2/(2*s*(2+s))) =
      u^2/(4*(2+s))+d^2/(2*s*(2+s)) := by
    field_simp
    <;> ring
  rw [he] at hh
  exact hh

theorem uniform_perturbation_lower {K : ℕ} (s rho : ℝ) (hs : 0 < s) (hr : rho<1)
    (theta : Fin K → ℝ) (htheta : ∀ a b, theta a-theta b ≤ rho)
    (x y : ℝ) (z : Fin K → ℝ) (ha : PerturbedAlternative theta x y z) :
    (1-rho)^2*rate s ≤ uniformEnergy s x y z := by
  obtain ⟨a,b,hab,hgap⟩ := ha
  have hsum : 1-rho ≤ (x-(y-1))+(z a-z b) := by
    have hh := (le_abs_self (y-x)).trans hgap
    linarith [htheta a b]
  have hi : (x-(y-1))^2/2 ≤ x^2+(y-1)^2 := by nlinarith [sq_nonneg (x+(y-1))]
  have hj := two_cell_square z a b hab
  have hH : 0 < 2+s := by linarith
  have hl := add_le_add (div_le_div_of_nonneg_right hi (by positivity : 0 ≤ 2*(2+s)))
    (div_le_div_of_nonneg_right hj (by positivity : 0 ≤ s*(2+s)))
  have hlo := scaled_square_lower s (1-rho) (x-(y-1)) (z a-z b) hs (by linarith) hsum
  have he : (x-(y-1))^2/2/(2*(2+s))+(z a-z b)^2/2/(s*(2+s)) =
      (x-(y-1))^2/(4*(2+s))+(z a-z b)^2/(2*s*(2+s)) := by field_simp <;> ring
  rw [he] at hl
  exact hlo.trans hl

theorem perturbation_allocation_upper {K : ℕ} (hK : 2 ≤ K) (s : ℝ) (hs : 0 < s)
    (hsq : s^2=2*K) (theta : Fin K → ℝ) (p t : ℝ) (w : Fin K → ℝ)
    (hm : p+t+∑ i,w i=1) :
    ∃ x y z, PerturbedAlternative theta x y z ∧ energy p t w x y z ≤ rate s := by
  obtain ⟨a0,b0,hab0,hpair0⟩ := two_small_cells hK w
  have hp : ∃ a b,a ≠ b ∧ theta b ≤ theta a ∧ (K:ℝ)*(w a+w b) ≤ 2*∑ i,w i := by
    by_cases h : theta b0 ≤ theta a0
    · exact ⟨a0,b0,hab0,h,hpair0⟩
    · exact ⟨b0,a0,Ne.symm hab0,(lt_of_not_ge h).le,by simpa [add_comm] using hpair0⟩
  obtain ⟨a,b,hab,htheta,hpair⟩ := hp
  let z : Fin K → ℝ := fun i => (if i=a then s/(2*(2+s)) else 0)-
    (if i=b then s/(2*(2+s)) else 0)
  have hH : 0 < 2+s := by linarith
  have hzdiff : z a-z b=s/(2+s) := by
    dsimp [z]
    simp [hab,hab.symm]
    field_simp
    <;> ring
  have hxy : 1-1/(2+s)-1/(2+s)=s/(2+s) := by field_simp <;> ring
  refine ⟨1/(2+s),1-1/(2+s),z,⟨a,b,hab,?_⟩,?_⟩
  · rw [hxy,abs_of_nonneg (by positivity)]
    linarith [hzdiff]
  · rw [explicit_pair_energy a b hab s p t hs w]
    unfold rate
    have he : (p+t)/(2*(2+s)^2)+(w a+w b)*s^2/(8*(2+s)^2) =
      (4*(p+t)+(w a+w b)*s^2)/(8*(2+s)^2) := by field_simp <;> ring
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [hsq]
    have hpos : 0 ≤ 4-(4*(p+t)+2*(K:ℝ)*(w a+w b)) := by linarith
    nlinarith [mul_nonneg (sq_nonneg (2+s)) hpos]

theorem sup_norm_implies_range_bound {K : ℕ} (theta : Fin K → ℝ) (eta : ℝ)
    (h : ∀ i, |theta i| ≤ eta) : ∀ a b,theta a-theta b ≤ 2*eta := by
  intro a b
  have ha := abs_le.mp (h a)
  have hb := abs_le.mp (h b)
  linarith

#print axioms scaled_square_lower
#print axioms uniform_perturbation_lower
#print axioms perturbation_allocation_upper
#print axioms sup_norm_implies_range_bound
end
end CIGAMF.P13.FunctionalOutsiderPerturbation
