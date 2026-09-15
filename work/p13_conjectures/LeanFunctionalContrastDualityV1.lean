import «LeanFunctionalContrastPotentialV1»

/-! # R1: the two certificates pinch — `J_c` for a connected measurement graph.

`LeanFunctionalContrastPotentialV1` gives two one-sided certificates:

    potential_upper : a potential `p` separating `a` from `b` yields an
                      admissible alternative of energy `delta^2 E(p)/(p a - p b)^2`;
    flow_lower      : a unit flow `f` from `a` to `b` forces every admissible
                      alternative to cost at least `delta^2/(2 * flowResistance)`.

Left open was whether the two optima meet, i.e. Dirichlet/Thomson duality. This
file closes it WITHOUT any duality theorem and without a pseudoinverse, by the
observation that one object produces both certificates at once.

THE MECHANISM. Let `p` be HARMONIC for the pair `(a,b)`:

    for every i,   sum_j c i j * (p i - p j)  =  [i = a] - [i = b]

(the discrete equation `L p = e_a - e_b`). Define the INDUCED flow
`f i j = c i j * (p i - p j)`. Then

  * `induced_unitFlow`     — `f` is a unit flow from `a` to `b`;
  * `harmonic_energy`      — `2 * contrastEnergy c p = p a - p b`;
  * `induced_flowResistance` — `flowResistance c f = p a - p b`.

Write `R = p a - p b`. The upper certificate becomes
`delta^2 * (R/2) / R^2 = delta^2/(2R)`, and the lower certificate becomes
`delta^2/(2 * R)`. They are the SAME number, so

    `pair_infimum_exact` :  the cheapest alternative that opens the pair `(a,b)`
                            to `delta` costs exactly `delta^2 / (2R)`,

attained, with a matching lower bound over every admissible alternative. `R` is
the effective resistance of the pair, so this is the target formula
`J = delta^2 / (2 R_eff)` for that pair.

WHAT IS ASSUMED, AND WHAT IS NOT PROVED.

- The harmonic potential is a HYPOTHESIS (`Harmonic`), not constructed. Existence
  for a connected positive-weight graph is the linear-algebra step `L p = e_a-e_b`
  and is not proved here; that is the one place a solve is still needed. Given
  such a `p`, nothing else about the graph is used — not connectivity, not
  positivity of every weight.
- The result is PER PAIR. `J_c` is the minimum over pairs `(a,b)`, so turning
  this into `J_c = delta^2/(2 max_{a≠b} R_eff(a,b))` needs a harmonic potential
  for each pair and a minimisation over them. That assembly is not in this file.
- `Alternative` in `LeanFunctionalContrastDesignV1` quantifies over SOME pair;
  the statements here use the pair-restricted form `delta ≤ z a - z b`, which is
  what a single flow can bound. The two agree only after the minimisation above.
- Nothing here concerns unknown extrema, edge costs, or which topology is best.
-/

namespace CIGAMF.P13.FunctionalContrastDuality
open Finset
open scoped BigOperators
open CIGAMF.P13.FunctionalContrastDesign
open CIGAMF.P13.FunctionalContrastPotential
noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

/-- `p` solves `L p = e_a - e_b` on a symmetric conductance graph. -/
structure Harmonic (c : I → I → ℝ) (a b : I) (p : I → ℝ) : Prop where
  sym : ∀ i j, c i j = c j i
  div : ∀ i, (∑ j, c i j*(p i-p j)) = if i = a then 1 else if i = b then -1 else 0

/-- The flow carried by a harmonic potential is a unit flow. -/
theorem induced_unitFlow (c : I → I → ℝ) (a b : I) (p : I → ℝ) (hp : Harmonic c a b p) :
    UnitFlow a b (fun i j => c i j*(p i-p j)) where
  anti := by
    intro i j
    rw [hp.sym j i]
    ring
  div := hp.div

/-- The Dirichlet energy of a harmonic potential is half the potential drop. -/
theorem harmonic_energy (c : I → I → ℝ) (a b : I) (p : I → ℝ) (hab : a ≠ b)
    (hp : Harmonic c a b p) : 2*contrastEnergy c p = p a-p b := by
  classical
  have hS1 : (∑ i, ∑ j, c i j*(p i-p j)*p i) = p a-p b := by
    have h : ∀ i : I, (∑ j, c i j*(p i-p j)*p i)
        = (if i = a then p a else 0)-(if i = b then p b else 0) := by
      intro i
      rw [← sum_mul, hp.div i]
      by_cases h1 : i = a
      · subst h1; rw [if_pos rfl, if_pos rfl, if_neg hab]; ring
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : i = b
        · subst h2; rw [if_pos rfl, if_pos rfl]; ring
        · rw [if_neg h2, if_neg h2]; ring
    rw [sum_congr rfl (fun i _ => h i), sum_sub_distrib,
      Finset.sum_ite_eq' univ a (fun _ => p a), Finset.sum_ite_eq' univ b (fun _ => p b)]
    simp
  have hS2 : (∑ i, ∑ j, c i j*(p i-p j)*p j) = -(∑ i, ∑ j, c i j*(p i-p j)*p i) := by
    have hcomm : (∑ i, ∑ j, c i j*(p i-p j)*p j) = ∑ i, ∑ j, -(c i j*(p i-p j)*p i) := by
      rw [Finset.sum_comm]
      exact sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => by
        rw [hp.sym j i]; ring))
    rw [hcomm]
    simp
  have hsplit : (∑ i, ∑ j, c i j*(p i-p j)^2)
      = (∑ i, ∑ j, c i j*(p i-p j)*p i)-(∑ i, ∑ j, c i j*(p i-p j)*p j) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun i _ => by
      rw [← sum_sub_distrib]
      exact sum_congr rfl (fun j _ => by ring))
  unfold contrastEnergy
  rw [hsplit, hS2, hS1]
  ring

/-- The induced flow's resistance is exactly the potential drop. -/
theorem induced_flowResistance (c : I → I → ℝ) (a b : I) (p : I → ℝ) (hab : a ≠ b)
    (hp : Harmonic c a b p) :
    flowResistance c (fun i j => c i j*(p i-p j)) = p a-p b := by
  classical
  have hterm : ∀ i j : I,
      (if c i j = 0 then 0 else (c i j*(p i-p j))^2/c i j) = c i j*(p i-p j)^2 := by
    intro i j
    by_cases h : c i j = 0
    · rw [if_pos h, h]; ring
    · rw [if_neg h]
      field_simp
  have hE := harmonic_energy c a b p hab hp
  unfold flowResistance
  rw [sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => hterm i j))]
  unfold contrastEnergy at hE
  linarith

/-! ## The pinch -/

/-- Both certificates give the same number, so the pair-restricted infimum is
exact and attained: the cheapest way to open `(a,b)` by `delta` costs
`delta^2/(2R)` with `R = p a - p b` the effective resistance of the pair. -/
theorem pair_infimum_exact (c : I → I → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (a b : I) (hab : a ≠ b) (p : I → ℝ) (hp : Harmonic c a b p)
    (delta : ℝ) (hd : 0 ≤ delta) (hR : 0 < p a-p b) :
    (∃ z : I → ℝ, delta ≤ z a-z b ∧
        contrastEnergy c z = delta^2/(2*(p a-p b))) ∧
    (∀ z : I → ℝ, delta ≤ z a-z b →
        delta^2/(2*(p a-p b)) ≤ contrastEnergy c z) := by
  classical
  have hRne : (p a-p b) ≠ 0 := ne_of_gt hR
  have hE : contrastEnergy c p = (p a-p b)/2 := by
    have := harmonic_energy c a b p hab hp
    linarith
  constructor
  · -- the rescaled potential attains the value
    refine ⟨fun i => (delta/(p a-p b))*p i, ?_, ?_⟩
    · have h : (delta/(p a-p b))*p a-(delta/(p a-p b))*p b = delta := by
        field_simp
      exact le_of_eq h.symm
    · rw [contrastEnergy_smul, hE, div_pow]
      field_simp
  · -- the induced flow forces the same value
    intro z hz
    have hflow := induced_unitFlow c a b p hp
    have hres := induced_flowResistance c a b p hab hp
    have hsupp : ∀ i j : I, c i j = 0 → c i j*(p i-p j) = 0 := by
      intro i j h; rw [h]; ring
    have hlow := flow_lower c hc a b (fun i j => c i j*(p i-p j)) hflow hab hsupp
      delta hd z hz
    rw [hres] at hlow
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 2*(p a-p b))]
    linarith

#print axioms induced_unitFlow
#print axioms harmonic_energy
#print axioms induced_flowResistance
#print axioms pair_infimum_exact

end
end CIGAMF.P13.FunctionalContrastDuality
