import «LeanD6ScalarWidthRegionV1»

/-! # R2, the `mu < 1/2` region: the scalar-dominance certificate, sharpened.

`LeanD6WidthCostInformationV1.joint_mixture_scalar_bound` proves that the
adjacent-swap mixture of any joint query, per unit cost, is at most the B-scalar
value `mu^2/(2q)` under TWO hypotheses:

    hmu     : 1/2 <= mu
    hcharge : width <= cost * variance     (i.e. `z >= 1` in the power model)

`WIDTH_SCALAR_REGION_PROOF.md` accordingly records the `mu < 1/2` region as
uncharacterised. But reading that proof, `mu >= 1/2` and `hcharge` are used ONLY
to produce the single inequality

    (1 - mu)^2 * width <= mu^2 * (cost * variance).                        (*)

So (*) is the real hypothesis, and the two-part condition is a corner of it.
Assuming (*) directly gives a strictly more general theorem with a shorter proof,
and the `mu < 1/2` region is then not a gap at all: it is the part of (*) where
the charge has to be larger.

WHAT THIS GIVES.

* `joint_mixture_scalar_bound_sharp` — the generalised bound. No sign condition
  on `mu - 1/2` and no comparison of `width` with `cost * variance`.
* `sharp_of_ratio` — (*) holds as soon as
  `cost * variance >= width * ((1-mu)/mu)^2`, for any `mu` in `(0,1]`.
  For `mu >= 1/2` the ratio is at most `1` and this is weaker than `hcharge`;
  for `mu < 1/2` the ratio exceeds `1` and the charge must simply be bigger.
* `joint_mixture_scalar_bound` (the old statement) is re-derived as a corollary,
  so nothing previously proved is weakened.

CONSEQUENCE FOR THE NUMERICAL GRID. In the power model `cost * variance =
width^z`, (*) reads `(1-mu)^2 * width^(1-z) <= mu^2`. With `z > 1` the binding
width is the smallest admissible one, `2`, so the certificate holds exactly when

    z >= 1 + 2 * log((1-mu)/mu) / log 2.

At `mu = 1/4` that threshold is `1 + 2 log 3 / log 2 = 4.1699...`. The 48-cell
sweep in `width_cost_game.json` runs only to `z = 2.5`, which is why no
scalar-optimal cell with `mu < 1/2` appears in it. The region is not absent; the
grid stopped below it.

WHAT THIS DOES NOT ESTABLISH.

- (*) is a SUFFICIENT condition for the mixture certificate, and the mixture is
  an UPPER bound on a design's value. Together with `uniform_B_lower` (the
  B-scalar design attains `mu^2/(2q)` against every wrong label, free of the
  nuisance) this identifies the optimum — but that final assembly is prose in
  `WIDTH_SCALAR_REGION_PROOF.md`, not a Lean theorem, and is not added here.
- Nothing here proves the converse: that the scalar design is STRICTLY
  suboptimal when (*) fails. The numerical grid shows it loses at the cells
  tested, which is evidence, not a theorem.
- The `z` threshold above is stated in the docstring only; `Real.rpow` is not
  used anywhere in the statements, which are all multiplicative.
-/

namespace CIGAMF.P13.D6ScalarWidthSharp
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6AllocationMargin
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6QueryWidthInformation
open CIGAMF.P13.D6WidthCostInformation CIGAMF.P13.D6ScalarWidthRegion
noncomputable section
variable {n : ℕ}

/-- The charge condition that actually drives the certificate. Valid for every
`mu` in `(0,1]`, in particular below `1/2`. -/
theorem sharp_of_ratio (mu width charge : ℝ) (hmu : 0 < mu) (hw : 0 ≤ width)
    (h : width*((1-mu)/mu)^2 ≤ charge) :
    (1-mu)^2*width ≤ mu^2*charge := by
  have hm2 : 0 < mu^2 := by positivity
  have hexp : width*((1-mu)/mu)^2 = ((1-mu)^2*width)/mu^2 := by
    field_simp
  rw [hexp, div_le_iff₀ hm2] at h
  nlinarith [h]

/-- The sharpened certificate: the adjacent-swap mixture of any legal joint
query, per unit cost, is at most the B-scalar value. The only hypothesis tying
the query's width to its charge is the product inequality. -/
theorem joint_mixture_scalar_bound_sharp (A G : Finset (I n)) (j : I n) (h : Bool)
    (q mu cost variance width : ℝ) (hq : 0<q) (hc : 0<cost) (hv : 0<variance)
    (hj : j ∉ A) (hA : (A.card:ℝ)=q+1) (hB : ((others A j).card:ℝ)=q)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (hwidth : (G.card:ℝ) ≤ width)
    (hsharp : (1-mu)^2*width ≤ mu^2*(cost*variance)) :
    (∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) G j h mu mu)/
      (q*(q+1)*cost*variance) ≤ mu^2/(2*q) := by
  have hb := actual_average_width_bound A G j h q mu width (cost*variance) hq
    (mul_pos hc hv) hj hA hB hjG hG hwidth
  have hden : (cost*variance)*q*(q+1)=q*(q+1)*cost*variance := by ring
  rw [hden] at hb
  apply hb.trans
  apply (div_le_div_iff₀ (by positivity : 0<2*(cost*variance)*q) (by positivity : 0<2*q)).mpr
  nlinarith [mul_nonneg (show (0:ℝ) ≤ 2*q by positivity) (sub_nonneg.mpr hsharp)]

/-- The published `mu >= 1/2`, `width <= cost*variance` statement is the corner
`(1-mu)^2 <= mu^2` of the sharp condition. Nothing is lost. -/
theorem joint_mixture_scalar_bound_of_half (A G : Finset (I n)) (j : I n) (h : Bool)
    (q mu cost variance width : ℝ) (hq : 0<q) (hc : 0<cost) (hv : 0<variance)
    (hmu : 1/2 ≤ mu) (hj : j ∉ A) (hA : (A.card:ℝ)=q+1)
    (hB : ((others A j).card:ℝ)=q) (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card)
    (hwidth : (G.card:ℝ) ≤ width) (hcharge : width ≤ cost*variance) :
    (∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) G j h mu mu)/
      (q*(q+1)*cost*variance) ≤ mu^2/(2*q) := by
  refine joint_mixture_scalar_bound_sharp A G j h q mu cost variance width hq hc hv
    hj hA hB hjG hG hwidth ?_
  have hw0 : (0:ℝ) ≤ width := le_trans (by positivity) hwidth
  have hsq : (1-mu)^2 ≤ mu^2 := by nlinarith
  have hcv : 0 ≤ cost*variance := (mul_pos hc hv).le
  nlinarith [mul_le_mul_of_nonneg_left hcharge (sq_nonneg (1-mu)),
    mul_le_mul_of_nonneg_right hsq hcv]

/-- Below `1/2` the certificate still applies; it only asks for a larger charge.
Stated in the form the power model produces. -/
theorem scalar_certificate_below_half (A G : Finset (I n)) (j : I n) (h : Bool)
    (q mu cost variance width : ℝ) (hq : 0<q) (hc : 0<cost) (hv : 0<variance)
    (hmu : 0 < mu) (hj : j ∉ A) (hA : (A.card:ℝ)=q+1)
    (hB : ((others A j).card:ℝ)=q) (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card)
    (hwidth : (G.card:ℝ) ≤ width) (hw0 : 0 ≤ width)
    (hratio : width*((1-mu)/mu)^2 ≤ cost*variance) :
    (∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) G j h mu mu)/
      (q*(q+1)*cost*variance) ≤ mu^2/(2*q) :=
  joint_mixture_scalar_bound_sharp A G j h q mu cost variance width hq hc hv
    hj hA hB hjG hG hwidth (sharp_of_ratio mu width (cost*variance) hmu hw0 hratio)

/-- The B-scalar design attains the same value against every wrong label and
every nuisance, so under the sharp condition the certificate is two-sided for
that design. Restated here so the pair sits in one place. -/
theorem scalar_attains (A C : Finset (I n)) (j : I n) (q mu nu : ℝ)
    (hq : 0<q) (hjA : j ∉ A) (hjC : j ∉ C) (hne : C ≠ A) (hcard : C.card=A.card) :
    mu^2/(2*q) ≤ ∑ b ∈ others A j,
      (actualMean A j mu (.inl b)-actualMean C j nu (.inl b))^2/(2*q) :=
  uniform_B_lower A C j q mu nu hq hjA hjC hne hcard

#print axioms sharp_of_ratio
#print axioms joint_mixture_scalar_bound_sharp
#print axioms joint_mixture_scalar_bound_of_half
#print axioms scalar_certificate_below_half
#print axioms scalar_attains

end
end CIGAMF.P13.D6ScalarWidthSharp
