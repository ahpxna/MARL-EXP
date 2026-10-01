import «LeanFunctionalContrastDesignV1»

/-! R1 continued: the effective-resistance bridge, by two elementary certificates.

`LeanFunctionalContrastDesignV1` settles the two ends of the target: a zero cut
gives information `0`, and the complete graph at uniform exposure gives exactly
`delta^2/(2(K-1))`. What remained open was the connected case

    J_c = delta^2 / (2 * max_{a != b} R_eff(a,b)).

This file supplies both halves as CERTIFICATES, which is what makes the
pseudoinverse unnecessary:

* `potential_upper` — any potential `p` with `p a - p b > 0` is rescaled to close
  the gap, giving an admissible alternative of energy
  `delta^2 * contrastEnergy c p / (p a - p b)^2`. Minimising over `p` is the
  Dirichlet characterisation of `R_eff`, so this is the upper half.

* `flow_lower` — any unit flow from `a` to `b` bounds the energy below by
  `delta^2 / (2 * flowResistance c f)`. The proof is the discrete Green identity
  plus Cauchy-Schwarz; Thomson's principle says the best flow gives `R_eff`, so
  this is the lower half.

Together they BRACKET `J_c` for every finite graph: exhibit a potential and a
flow whose values agree and the pair is a complete proof of `J_c` for that graph,
with no linear solve in the kernel of the argument.

WHAT IS STILL NOT PROVED. That the two optima meet - i.e. `min_p = 1/(2 R_eff) =
max_f` - is Thomson/Dirichlet duality and is NOT proved here; without it these
are two bounds, not the formula. Neither is the maximisation over pairs `(a,b)`,
nor any statement about which topology is optimal when the extrema are unknown.
The star and path rows of the topology table remain certified numerically only
(the exact Fraction probe at `K = 3,4,6,8,12`), not in Lean.
-/

namespace CIGAMF.P13.FunctionalContrastPotential
open Finset
open scoped BigOperators
open CIGAMF.P13.FunctionalContrastDesign
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-! ## Upper certificate: rescale any potential -/

theorem contrastEnergy_smul (c : I → I → ℝ) (t : ℝ) (p : I → ℝ) :
    contrastEnergy c (fun i => t*p i) = t^2*contrastEnergy c p := by
  unfold contrastEnergy
  have hstep : ∀ a : I, (∑ b, c a b*(t*p a-t*p b)^2)
      = t^2*∑ b, c a b*(p a-p b)^2 := by
    intro a
    rw [mul_sum]
    exact sum_congr rfl (fun b _ => by ring)
  rw [sum_congr rfl (fun a _ => hstep a), ← mul_sum]
  ring

/-- Any potential separating `a` from `b` yields an admissible alternative. -/
theorem potential_upper (c : I → I → ℝ) (p : I → ℝ) (a b : I) (delta : ℝ)
    (hp : 0 < p a-p b) :
    ∃ z : I → ℝ, Alternative delta z ∧
      contrastEnergy c z = delta^2*contrastEnergy c p/(p a-p b)^2 := by
  have hne : p a-p b ≠ 0 := ne_of_gt hp
  refine ⟨fun i => (delta/(p a-p b))*p i, ⟨a, b, ?_⟩, ?_⟩
  · have h : (delta/(p a-p b))*p a-(delta/(p a-p b))*p b = delta := by
      field_simp
    exact le_of_eq h.symm
  · rw [contrastEnergy_smul, div_pow]
    ring

/-! ## Lower certificate: any unit flow -/

/-- `f` is a unit flow from `a` to `b`: antisymmetric, with divergence `+1` at
`a`, `-1` at `b` and `0` elsewhere. -/
structure UnitFlow (a b : I) (f : I → I → ℝ) : Prop where
  anti : ∀ i j, f j i = -f i j
  div : ∀ i, (∑ j, f i j) = if i = a then 1 else if i = b then -1 else 0

/-- The flow's resistance, `(1/2) * sum f^2 / c` over ordered pairs. -/
def flowResistance (c : I → I → ℝ) (f : I → I → ℝ) : ℝ :=
  (∑ i, ∑ j, if c i j = 0 then 0 else f i j^2/c i j)/2

/-- Discrete Green identity: a unit flow reads off the potential difference. -/
theorem flow_green (a b : I) (f : I → I → ℝ) (hf : UnitFlow a b f) (hab : a ≠ b)
    (z : I → ℝ) : (∑ i, ∑ j, f i j*(z i-z j))/2 = z a-z b := by
  classical
  have hS1 : (∑ i, ∑ j, f i j*z i) = z a-z b := by
    have h : ∀ i : I, (∑ j, f i j*z i)
        = (if i = a then z a else 0)-(if i = b then z b else 0) := by
      intro i
      rw [← sum_mul, hf.div i]
      by_cases h1 : i = a
      · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hab]; ring
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : i = b
        · subst h2; rw [if_pos rfl, if_pos rfl]; ring
        · rw [if_neg h2, if_neg h2]; ring
    rw [sum_congr rfl (fun i _ => h i), sum_sub_distrib,
      Finset.sum_ite_eq' univ a (fun _ => z a), Finset.sum_ite_eq' univ b (fun _ => z b)]
    simp
  have hS2 : (∑ i, ∑ j, f i j*z j) = -(∑ i, ∑ j, f i j*z i) := by
    have hcomm : (∑ i, ∑ j, f i j*z j) = ∑ i, ∑ j, -(f i j*z i) := by
      rw [Finset.sum_comm]
      exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by
        rw [hf.anti j i]; ring))
    rw [hcomm]
    simp
  have hsplit : (∑ i, ∑ j, f i j*(z i-z j))
      = (∑ i, ∑ j, f i j*z i)-(∑ i, ∑ j, f i j*z j) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun i _ => by
      rw [← sum_sub_distrib]
      exact sum_congr rfl (fun j _ => by ring))
  rw [hsplit, hS2, hS1]
  ring

/-- Cauchy-Schwarz against a unit flow: every admissible alternative pays at
least `delta^2/(2 * flowResistance)`. With the best flow this is Thomson's
principle, so this is the lower half of the effective-resistance formula. -/
theorem flow_lower (c : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (a b : I) (f : I → I → ℝ) (hf : UnitFlow a b f) (hab : a ≠ b)
    (hsupp : ∀ i j, c i j = 0 → f i j = 0)
    (delta : ℝ) (hd : 0 ≤ delta) (z : I → ℝ) (hz : delta ≤ z a-z b) :
    delta^2 ≤ 2*flowResistance c f*contrastEnergy c z := by
  classical
  set S : Finset (I × I) := univ ×ˢ univ with hS
  set u : I × I → ℝ :=
    fun p => if c p.1 p.2 = 0 then 0 else f p.1 p.2/Real.sqrt (c p.1 p.2) with hu
  set v : I × I → ℝ := fun p => Real.sqrt (c p.1 p.2)*(z p.1-z p.2) with hv
  have huv : ∀ p : I × I, u p*v p = f p.1 p.2*(z p.1-z p.2) := by
    intro p
    by_cases h : c p.1 p.2 = 0
    · rw [hu, hv]; simp only [if_pos h]; rw [hsupp p.1 p.2 h]; ring
    · have hpos : 0 < c p.1 p.2 := lt_of_le_of_ne (hc p.1 p.2) (Ne.symm h)
      have hsq : Real.sqrt (c p.1 p.2) ≠ 0 := by
        simpa using (Real.sqrt_pos.mpr hpos).ne'
      rw [hu, hv]; simp only [if_neg h]
      field_simp
  have hu2 : ∀ p : I × I,
      u p^2 = if c p.1 p.2 = 0 then 0 else f p.1 p.2^2/c p.1 p.2 := by
    intro p
    by_cases h : c p.1 p.2 = 0
    · rw [hu]; simp [h]
    · have hpos : 0 < c p.1 p.2 := lt_of_le_of_ne (hc p.1 p.2) (Ne.symm h)
      rw [hu]; simp only [if_neg h]
      rw [div_pow, Real.sq_sqrt hpos.le]
  have hv2 : ∀ p : I × I, v p^2 = c p.1 p.2*(z p.1-z p.2)^2 := by
    intro p
    rw [hv]
    simp only [mul_pow, Real.sq_sqrt (hc p.1 p.2)]
  have hcs := sum_mul_sq_le_sq_mul_sq S u v
  rw [sum_congr rfl (fun p _ => huv p), sum_congr rfl (fun p _ => hu2 p),
    sum_congr rfl (fun p _ => hv2 p)] at hcs
  rw [hS, Finset.sum_product, Finset.sum_product, Finset.sum_product] at hcs
  have hG : (∑ i, ∑ j, f i j*(z i-z j)) = 2*(z a-z b) := by
    have h := flow_green a b f hf hab z
    field_simp at h
    linarith
  rw [hG] at hcs
  have hR : (∑ i, ∑ j, if c i j = 0 then 0 else f i j^2/c i j) = 2*flowResistance c f := by
    unfold flowResistance; ring
  have hE : (∑ i, ∑ j, c i j*(z i-z j)^2) = 4*contrastEnergy c z := by
    unfold contrastEnergy; ring
  rw [hR, hE] at hcs
  have hstep : (2*delta)^2 ≤ (2*(z a-z b))^2 := by nlinarith
  nlinarith [hcs, hstep]

/-- The bracket, stated as the two-sided certificate pair: a flow lower-bounds
and a potential upper-bounds the same quantity. -/
theorem flow_lower_div (c : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (a b : I) (f : I → I → ℝ) (hf : UnitFlow a b f) (hab : a ≠ b)
    (hsupp : ∀ i j, c i j = 0 → f i j = 0)
    (delta : ℝ) (hd : 0 ≤ delta) (z : I → ℝ) (hz : delta ≤ z a-z b)
    (hR : 0 < flowResistance c f) :
    delta^2/(2*flowResistance c f) ≤ contrastEnergy c z := by
  rw [div_le_iff₀ (by linarith)]
  have h := flow_lower c hc a b f hf hab hsupp delta hd z hz
  linarith

#print axioms contrastEnergy_smul
#print axioms potential_upper
#print axioms flow_green
#print axioms flow_lower
#print axioms flow_lower_div

end
end CIGAMF.P13.FunctionalContrastPotential
