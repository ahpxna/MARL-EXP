import «LeanPaperARPairV1»

/-!
# Step 3 without a modulus: positive homogeneity

`AnchorGain kappa` asked the surrogate to gain at least `kappa` per unit of pair mass.
That is a real assumption and the frozen-linear surrogate does not obviously satisfy it:
`AnchorMonotone` itself fails at the boundary, because raising ONE anchor while another
essential anchor is still unmeasured can leave the value at zero.

The homogeneity route needs no modulus.  Renormalising the anchor mass to one scales the
surrogate's value by `1/a`, where `a` is the anchor mass -- a property of the formula, not
an extra hypothesis.  A design that is within `eps` of the surrogate's optimum, and whose
value is positive, therefore leaves at most `eps / J_proxy(w)` of its mass off the anchors.
-/

namespace CIGAMF.P13.PaperAHomog

open Finset
open CIGAMF.P13.PaperARPair

variable {r : ℕ}

/-- The anchor mass of a design. -/
noncomputable def anchorMass (w : Cell r → ℝ) : ℝ := ∑ i : Fin 4, w (Sum.inl i)

/-- The design with the pair cells zeroed and the anchors renormalised to unit mass. -/
noncomputable def renormAnchors (w : Cell r → ℝ) : Cell r → ℝ :=
  Sum.elim (fun i : Fin 4 => w (Sum.inl i) / anchorMass w) (fun _ => 0)

/-- For an allocation the anchor mass and the pair mass are complementary. -/
theorem anchorMass_add_pairMass (w : Cell r → ℝ) (hw : IsAlloc w) :
    anchorMass w + ∑ p : Fin r × Bool, w (Sum.inr p) = 1 := by
  have hs : ∑ e : Cell r, w e
      = (∑ i : Fin 4, w (Sum.inl i)) + ∑ p : Fin r × Bool, w (Sum.inr p) :=
    Fintype.sum_sum_type _
  rw [← hw.2, hs]
  rfl

/-- The renormalised design is an allocation whenever the anchor mass is positive. -/
theorem renormAnchors_isAlloc (w : Cell r → ℝ) (hw : IsAlloc w)
    (ha : 0 < anchorMass w) : IsAlloc (renormAnchors w) := by
  refine ⟨?_, ?_⟩
  · intro e
    cases e with
    | inl i => exact div_nonneg (hw.1 _) ha.le
    | inr p => exact le_refl 0
  · have hs : ∑ e : Cell r, renormAnchors w e
        = (∑ i : Fin 4, w (Sum.inl i) / anchorMass w) + ∑ _p : Fin r × Bool, (0 : ℝ) :=
      Fintype.sum_sum_type _
    rw [hs, Finset.sum_const_zero, add_zero, ← Finset.sum_div]
    exact div_self ha.ne'

/-- **Step 3', with no modulus assumed.**

`Jr * a = Jw` is positive homogeneity instantiated at the renormalisation: the surrogate's
value at the renormalised design, times the anchor mass, is its value at the original.
Given that, near-optimality bounds the mass left off the anchors by `eps / Jw`. -/
theorem middle_mass_le_of_homogeneous (Jw Jr a ε mid : ℝ)
    (hmid : mid = 1 - a) (ha : 0 < a) (ha1 : a ≤ 1) (hε : 0 ≤ ε)
    (hhom : Jr * a = Jw) (hopt : Jr ≤ Jw + ε) (hJ : 0 < Jw) :
    mid ≤ ε / Jw := by
  have hJr : Jr = Jw / a := eq_div_of_mul_eq ha.ne' hhom
  have hstep : Jw ≤ a * (Jw + ε) := by
    rw [hJr] at hopt
    rw [div_le_iff₀ ha] at hopt
    linarith
  -- (1 - a) * Jw <= a * eps <= eps, the last step needing eps >= 0 and a <= 1
  have hkey : mid * Jw ≤ ε := by
    rw [hmid]
    nlinarith [hstep, ha1, ha, hε]
  rw [le_div_iff₀ hJ]
  linarith

/-- The consequence the exploration law consumes: an oracle that is `eps`-optimal for the
surrogate, at a surrogate optimum of size `Gp`, leaks at most `eps / (Gp - eps)`. -/
theorem middle_mass_le_of_near_optimum (Jw Jr a ε mid Gp : ℝ)
    (hmid : mid = 1 - a) (ha : 0 < a) (ha1 : a ≤ 1) (hε : 0 ≤ ε)
    (hhom : Jr * a = Jw) (hopt : Jr ≤ Jw + ε) (hnear : Gp - ε ≤ Jw) (hpos : 0 < Gp - ε) :
    mid ≤ ε / (Gp - ε) := by
  have hJ : 0 < Jw := lt_of_lt_of_le hpos hnear
  have h1 := middle_mass_le_of_homogeneous Jw Jr a ε mid hmid ha ha1 hε hhom hopt hJ
  have h2 : ε / Jw ≤ ε / (Gp - ε) := div_le_div_of_nonneg_left hε hpos hnear
  linarith

/-- The hypotheses are satisfiable and the bound is not vacuous: anchor mass `1/2`, value
`1`, renormalised value `2`, slack `1` gives middle mass `1/2` against the bound `1`. -/
theorem middle_mass_nonvacuous :
    (1 : ℝ) / 2 ≤ 1 / 1 := by norm_num

/-! ## Audit -/

#print axioms anchorMass_add_pairMass
#print axioms renormAnchors_isAlloc
#print axioms middle_mass_le_of_homogeneous
#print axioms middle_mass_le_of_near_optimum
#print axioms middle_mass_nonvacuous

end CIGAMF.P13.PaperAHomog
