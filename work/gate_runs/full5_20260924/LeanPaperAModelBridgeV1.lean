import Mathlib
import «LeanProductMixedDifferenceV4»

/-!
# Paper A, package A-model: the coefficient vector is DERIVED, not supplied.

## WHY THIS MODULE EXISTS

`LeanPaperAAlternativesV1` proves that the alternative set of a compression decision is
exactly a finite union of regions, but it takes the coefficient vectors `a_T` as an input
table.  A theorem whose hypotheses are a table of numbers is a theorem about that table.
This module closes that gap: it starts from the corpus definitions -- `productResponse` for
the responses and `oscOn` for the loss -- and DERIVES the coefficient vector, so nothing
downstream is free to choose it.

## THE MODEL

Parametrise the world linearly in `d` known features,

    F_theta (x) = sum_l theta_l * phi_l (x).

The reference `q` is fixed.  `productResponse` is an expectation against `q`, hence linear
in its integrand, so the responses inherit the parametrisation:

    Q_{theta,i}(u) = sum_l theta_l * Q_{phi_l, i}(u).

Retaining a set `T` of coordinates leaves the residual

    R_{theta,T}(x) = F_theta (x) - sum_{i in T} Q_{theta,i}(x_i),

and the two displays above make it a linear form in `theta` with the coefficient vector

    a_T(x)_l = phi_l (x) - sum_{i in T} Q_{phi_l, i}(x_i).                    (*)

That is `coefVector` below, and `residual_eq_inner` is the identity.  The loss on a
deployment support `K` is then half the oscillation of a linear form, which is exactly the
shape `LeanPaperAAlternativesV1` assumes -- but now with `a_T` computed from `F`, `q` and
`T` rather than handed over.

## WHAT IS AND IS NOT PROVED HERE

Proved: linearity of the responses, the identity (*), the loss identity, and the
`selectedRadius` bridge described below.  NOT proved here: that the residual equals any
expression with responses dropped.  It does not in general, and substituting one for the
other is precisely the error this module exists to make impossible.

## THE `selectedRadius` BRIDGE, WITH INTERACTION KEPT

`selectedRadius f S = supportOsc S^c f / 2` is an oscillation of a sum over the DISCARDED
components, so it only agrees with the compression loss when the family's components sum to
`F`.  A general `F` has an interaction part that no single-coordinate response captures.
Rather than assume it away, we carry it: index the extended family by `Option (Fin (n+1))`,
put

    f_none = F - sum_i Q_i          (the interaction remainder),
    f_(some i) = Q_i (. i),

so the family sums to `F` exactly.  Retaining `T` means selecting `some '' T` and never
`none`, and then the discarded components sum to `F - sum_{i in T} Q_i`, the true residual.
`selectedRadius_eq_compressionLoss` is that statement.  Dropping `none` from the family
would silently delete the interaction and make the bridge false for every `F` that has one.
-/

namespace CIGAMF.P13.PaperAModelBridge

open scoped BigOperators NNReal ENNReal
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductMixedDifference

variable {U : Type*} [Fintype U] [Nonempty U] [DecidableEq U]

/-! ## Linearity of the reference expectation and of the responses -/

/-- `productExpectation` is an expectation, hence commutes with a finite linear
combination of integrands.  Everything about linearity in `theta` comes from this. -/
theorem productExpectation_sum_smul {n d : ℕ}
    (q : Fin (n + 1) → U → ℝ) (θ : Fin d → ℝ)
    (φ : Fin d → (Fin (n + 1) → U) → ℝ) :
    productExpectation q (fun c => ∑ l, θ l * φ l c)
      = ∑ l, θ l * productExpectation q (φ l) := by
  classical
  unfold productExpectation
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun c _ => by ring))

/-- The product responses of a linearly parametrised world are the same linear
combination of the responses of the features. -/
theorem productResponse_sum_smul {n d : ℕ}
    (q : Fin (n + 1) → U → ℝ) (θ : Fin d → ℝ)
    (φ : Fin d → (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u : U) :
    productResponse q (fun x => ∑ l, θ l * φ l x) i u
      = ∑ l, θ l * productResponse q (φ l) i u := by
  classical
  unfold productResponse
  exact productExpectation_sum_smul q θ (fun l c => φ l (Function.update c i u))

/-! ## The coefficient vector, and the residual as a linear form -/

/-- The world assembled from features and a parameter. -/
noncomputable def worldOf {n d : ℕ}
    (φ : Fin d → (Fin (n + 1) → U) → ℝ) (θ : Fin d → ℝ) :
    (Fin (n + 1) → U) → ℝ :=
  fun x => ∑ l, θ l * φ l x

/-- What is left of the world at `x` after the retained coordinates are explained by their
product responses. -/
noncomputable def residualOf {n d : ℕ}
    (q : Fin (n + 1) → U → ℝ) (φ : Fin d → (Fin (n + 1) → U) → ℝ)
    (θ : Fin d → ℝ) (T : Finset (Fin (n + 1))) (x : Fin (n + 1) → U) : ℝ :=
  worldOf φ θ x - ∑ i ∈ T, productResponse q (worldOf φ θ) i (x i)

/-- The coefficient vector of display (*): computed from the features, the reference and
the retained set.  It does not mention `theta`, which is the whole point. -/
noncomputable def coefVector {n d : ℕ}
    (q : Fin (n + 1) → U → ℝ) (φ : Fin d → (Fin (n + 1) → U) → ℝ)
    (T : Finset (Fin (n + 1))) (x : Fin (n + 1) → U) (l : Fin d) : ℝ :=
  φ l x - ∑ i ∈ T, productResponse q (φ l) i (x i)

/-- **The bridge.**  The residual is the linear form in `theta` with coefficients
`coefVector`.  Both sides are built from corpus definitions; nothing is assumed. -/
theorem residual_eq_inner {n d : ℕ}
    (q : Fin (n + 1) → U → ℝ) (φ : Fin d → (Fin (n + 1) → U) → ℝ)
    (θ : Fin d → ℝ) (T : Finset (Fin (n + 1))) (x : Fin (n + 1) → U) :
    residualOf q φ θ T x = ∑ l, θ l * coefVector q φ T x l := by
  classical
  unfold residualOf coefVector worldOf
  have hresp : ∀ i : Fin (n + 1),
      productResponse q (fun y => ∑ l, θ l * φ l y) i (x i)
        = ∑ l, θ l * productResponse q (φ l) i (x i) := by
    intro i
    exact productResponse_sum_smul q θ φ i (x i)
  calc
    (∑ l, θ l * φ l x) - ∑ i ∈ T, productResponse q (fun y => ∑ l, θ l * φ l y) i (x i)
        = (∑ l, θ l * φ l x)
            - ∑ i ∈ T, ∑ l, θ l * productResponse q (φ l) i (x i) := by
          refine congrArg (fun z => (∑ l, θ l * φ l x) - z) ?_
          exact Finset.sum_congr rfl (fun i _ => hresp i)
    _ = (∑ l, θ l * φ l x)
            - ∑ l, θ l * ∑ i ∈ T, productResponse q (φ l) i (x i) := by
          refine congrArg (fun z => (∑ l, θ l * φ l x) - z) ?_
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
    _ = ∑ l, θ l * (φ l x - ∑ i ∈ T, productResponse q (φ l) i (x i)) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun l _ => by ring)

/-! ## The loss on a deployment support -/

/-- The compression loss of retaining `T`, on the deployment support `K`: half the
oscillation of the residual, in the corpus's own `oscOn`. -/
noncomputable def lossOn {n d : ℕ} [DecidableEq (Fin (n + 1) → U)]
    (K : Finset (Fin (n + 1) → U)) (hK : K.Nonempty)
    (q : Fin (n + 1) → U → ℝ) (φ : Fin d → (Fin (n + 1) → U) → ℝ)
    (θ : Fin d → ℝ) (T : Finset (Fin (n + 1))) : ℝ :=
  oscOn K hK (residualOf q φ θ T) / 2

/-- **The loss is half the range of a linear form.**  This is the hypothesis that
`LeanPaperAAlternativesV1` works under, now discharged rather than assumed. -/
theorem loss_eq_half_range {n d : ℕ} [DecidableEq (Fin (n + 1) → U)]
    (K : Finset (Fin (n + 1) → U)) (hK : K.Nonempty)
    (q : Fin (n + 1) → U → ℝ) (φ : Fin d → (Fin (n + 1) → U) → ℝ)
    (θ : Fin d → ℝ) (T : Finset (Fin (n + 1))) :
    lossOn K hK q φ θ T
      = (maxOn K hK (fun x => ∑ l, θ l * coefVector q φ T x l)
          - minOn K hK (fun x => ∑ l, θ l * coefVector q φ T x l)) / 2 := by
  classical
  unfold lossOn oscOn
  have hfun : residualOf q φ θ T = fun x => ∑ l, θ l * coefVector q φ T x l := by
    funext x
    exact residual_eq_inner q φ θ T x
  rw [hfun]

/-! ## The `selectedRadius` bridge, with the interaction part carried

The extended family is indexed by `Option (Fin (n+1))`.  `none` is the interaction
remainder and is never retained; `some i` is the `i`-th response. -/

/-- The extended component family.  Its components sum to `F` exactly, which is what makes
`supportOsc` of the discarded part equal the true residual. -/
noncomputable def extendedFamily {n : ℕ} [DecidableEq (Fin (n + 1) → U)]
    (q : Fin (n + 1) → U → ℝ) (F : (Fin (n + 1) → U) → ℝ) :
    Option (Fin (n + 1)) → (Fin (n + 1) → U) → ℝ
  | none => fun x => F x - ∑ i, productResponse q F i (x i)
  | some i => fun x => productResponse q F i (x i)

/-- The components of `extendedFamily` sum to `F`: no interaction is lost. -/
theorem extendedFamily_sum {n : ℕ} [DecidableEq (Fin (n + 1) → U)]
    (q : Fin (n + 1) → U → ℝ) (F : (Fin (n + 1) → U) → ℝ)
    (x : Fin (n + 1) → U) :
    ∑ j : Option (Fin (n + 1)), extendedFamily q F j x = F x := by
  classical
  rw [Fintype.sum_option]
  simp only [extendedFamily]
  ring

/-- Retaining `T` in the extended family: the images of `T` under `some`.  `none` is
excluded by construction, so the interaction remainder is never retained. -/
noncomputable def retainedIn {n : ℕ} (T : Finset (Fin (n + 1))) :
    Finset (Option (Fin (n + 1))) :=
  T.image some

/-- The complement of `retainedIn T` is `none` together with the discarded coordinates. -/
theorem compl_retainedIn {n : ℕ} [DecidableEq (Fin (n + 1))]
    (T : Finset (Fin (n + 1))) :
    (retainedIn T)ᶜ = insert none ((Tᶜ).image some) := by
  classical
  ext j
  cases j with
  | none =>
      simp [retainedIn]
  | some i =>
      simp [retainedIn, Finset.mem_compl]

/-- **The bridge.**  The sum of the discarded components of the extended family is exactly
the residual after retaining `T`, so `selectedRadius` on the extended family is the
compression loss -- with the interaction term included, not dropped. -/
theorem sumComponent_compl_eq_residual {n : ℕ} [DecidableEq (Fin (n + 1) → U)]
    [DecidableEq (Fin (n + 1))]
    (q : Fin (n + 1) → U → ℝ) (F : (Fin (n + 1) → U) → ℝ)
    (T : Finset (Fin (n + 1))) (x : Fin (n + 1) → U) :
    sumComponent (retainedIn T)ᶜ (extendedFamily q F) x
      = F x - ∑ i ∈ T, productResponse q F i (x i) := by
  classical
  unfold sumComponent
  rw [compl_retainedIn T]
  rw [Finset.sum_insert (by simp)]
  have hmap : ∑ j ∈ (Tᶜ).image some, extendedFamily q F j x
      = ∑ i ∈ Tᶜ, productResponse q F i (x i) := by
    rw [Finset.sum_image (by intro a _ b _ h; exact Option.some_injective _ h)]
    rfl
  rw [hmap]
  have hsplit : ∑ i ∈ Tᶜ, productResponse q F i (x i)
      = (∑ i, productResponse q F i (x i)) - ∑ i ∈ T, productResponse q F i (x i) := by
    have := Finset.sum_add_sum_compl T (fun i => productResponse q F i (x i))
    linarith
  simp only [extendedFamily]
  rw [hsplit]
  ring

/-- `selectedRadius` of the extended family at the retained set is the compression loss.
Stated with the ambient `osc` of `LeanSupportGeometryV4`. -/
theorem selectedRadius_eq_compressionLoss {n : ℕ} [DecidableEq (Fin (n + 1) → U)]
    [DecidableEq (Fin (n + 1))]
    (q : Fin (n + 1) → U → ℝ) (F : (Fin (n + 1) → U) → ℝ)
    (T : Finset (Fin (n + 1))) :
    selectedRadius (extendedFamily q F) (retainedIn T)
      = osc (fun x => F x - ∑ i ∈ T, productResponse q F i (x i)) / 2 := by
  classical
  unfold selectedRadius supportOsc
  congr 1
  congr 1
  funext x
  exact sumComponent_compl_eq_residual q F T x

/-! ## The centered class, where the response IS the table

`rangeA_shift_invariant` observes that adding a constant to a table does not move its range,
so the LOSS is insensitive to the constant that `productResponse` introduces.  That settles
the loss and settles nothing else.  The information a query carries is a Gaussian KL, which
depends on the DIFFERENCE of two worlds' response means; and when the two worlds have
different constants, the difference of the responses is not the difference of the tables:

    Delta R_A(a) = Delta Q_A(a) + Delta (mean of Q_B),

and the trailing term moves the KL.  So a separation argument that compares energies across
worlds cannot rely on the range argument alone.

The fix is to work in the CENTERED class, where each table sums to zero.  There the constant
`productResponse` adds is zero, the response IS the table, and the two identities -- loss and
KL -- hold simultaneously.  The witnesses used in `LeanPaperASeparationV1` move two cells by
equal and opposite amounts, so they preserve each table's total and stay in the class; that
is why the fourth action is in the construction. -/

/-- `productExpectation` of a constant is that constant, on a normalised reference. -/
theorem productExpectation_const {n : ℕ} (q : Fin (n + 1) → U → ℝ) (a : ℝ)
    (hq : ∑ c, jointWeight q c = 1) :
    productExpectation q (fun _ => a) = a := by
  classical
  unfold productExpectation
  rw [← Finset.sum_mul, hq, one_mul]

/-- and it is additive. -/
theorem productExpectation_add {n : ℕ} (q : Fin (n + 1) → U → ℝ)
    (f g : (Fin (n + 1) → U) → ℝ) :
    productExpectation q (fun c => f c + g c)
      = productExpectation q f + productExpectation q g := by
  classical
  unfold productExpectation
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => by ring)

/-- **On the centered class the response is the table itself.**

For an additive world whose every component averages to zero under the reference, the
product response at each coordinate reproduces that coordinate's table exactly -- no
additive constant.  This is what makes the loss identity and the KL identity hold of the
SAME object. -/
theorem centered_additive_response {n : ℕ} (q : Fin (n + 1) → U → ℝ)
    (Q : Fin (n + 1) → U → ℝ)
    (hq : ∑ c, jointWeight q c = 1)
    (hcentered : ∀ j : Fin (n + 1),
      productExpectation q (fun c => Q j (c j)) = 0)
    (i : Fin (n + 1)) (u : U) :
    productResponse q (fun x => ∑ j, Q j (x j)) i u = Q i u := by
  classical
  unfold productResponse
  have hsplit : ∀ c : Fin (n + 1) → U,
      (∑ j, Q j (Function.update c i u j))
        = Q i u + ∑ j ∈ Finset.univ.erase i, Q j (c j) := by
    intro c
    rw [← Finset.add_sum_erase _ (fun j => Q j (Function.update c i u j))
        (Finset.mem_univ i)]
    simp only [Function.update_self]
    refine congrArg (fun z => Q i u + z) ?_
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [show (fun c : Fin (n + 1) → U => ∑ j, Q j (Function.update c i u j))
      = (fun c => Q i u + ∑ j ∈ Finset.univ.erase i, Q j (c j)) from funext hsplit]
  rw [productExpectation_add q (fun _ => Q i u)
        (fun c => ∑ j ∈ Finset.univ.erase i, Q j (c j)),
      productExpectation_const q (Q i u) hq]
  have hzero : productExpectation q
      (fun c => ∑ j ∈ Finset.univ.erase i, Q j (c j)) = 0 := by
    unfold productExpectation
    have hswap : ∑ c, jointWeight q c * ∑ j ∈ Finset.univ.erase i, Q j (c j)
        = ∑ j ∈ Finset.univ.erase i, ∑ c, jointWeight q c * Q j (c j) := by
      have hin : ∀ c : Fin (n + 1) → U,
          jointWeight q c * ∑ j ∈ Finset.univ.erase i, Q j (c j)
            = ∑ j ∈ Finset.univ.erase i, jointWeight q c * Q j (c j) := by
        intro c
        rw [Finset.mul_sum]
      simp_rw [hin]
      rw [Finset.sum_comm]
    rw [hswap]
    refine Finset.sum_eq_zero ?_
    intro j _
    exact hcentered j
  rw [hzero, add_zero]

/-- The squared response gap over twice the variance.  Naming it is not the same as
proving it is a Kullback-Leibler divergence, so the identity that makes it one is stated
and derived below rather than assumed by nomenclature. -/
noncomputable def sqGapFunctional (var θ lam : ℕ → ℝ) (e : ℕ) : ℝ :=
  (θ e - lam e) ^ 2 / (2 * var e)

/-- **The log-density ratio of two equal-variance Gaussians is AFFINE in the observation**,
with the coefficients written out.  This was previously a hypothesis of the identity below;
it is a computation, so it is done here instead. -/
theorem gaussian_log_ratio_affine (θ lam σ : ℝ) (hσ : 0 < σ) (y : ℝ) :
    Real.log (Real.exp (-((y - θ) ^ 2 / (2 * σ ^ 2)))
      / Real.exp (-((y - lam) ^ 2 / (2 * σ ^ 2))))
      = ((θ - lam) / σ ^ 2) * y + (lam ^ 2 - θ ^ 2) / (2 * σ ^ 2) := by
  have hσ2 : (σ : ℝ) ^ 2 ≠ 0 := by positivity
  rw [← Real.exp_sub, Real.log_exp]
  field_simp
  ring

/-- **What the identity actually needs of an observation law: its action on AFFINE
functions.**

This is deliberately weaker than linearity, and the reason is not aesthetic.  An earlier
version of this file asked for

    forall f g a b,  P (a f + b g) = a P f + b P g,

unconditionally.  That hypothesis is FALSE for the Bochner integral -- `integral_add`
requires both summands to be integrable, and for `f` integrable and `g` not, the left side
is `0` while the right side is `∫ f` -- so the theorem below could not be instantiated at
the Gaussian measure at all, which was the whole point of stating it.  `AffineMean` can be,
and `affineMean_gaussianReal` does it. -/
def AffineMean (P : (ℝ → ℝ) → ℝ) (θ : ℝ) : Prop :=
  ∀ a b : ℝ, P (fun y => a * y + b) = a * θ + b

/-- **The Gaussian information identity.**

    D_KL( N(theta, sigma^2) || N(lambda, sigma^2) )  =  (theta - lambda)^2 / (2 sigma^2).

`gaussian_log_ratio_affine` makes the integrand affine, so the divergence needs only the
FIRST moment of the observation law and nothing about its shape.  The statement is therefore
made for any functional with `AffineMean P theta`, and the Gaussian expectation is one --
proved, not assumed, in `affineMean_gaussianReal`. -/
theorem gaussian_kl_eq_sq_gap (θ lam σ : ℝ) (hσ : 0 < σ)
    (P : (ℝ → ℝ) → ℝ) (hP : AffineMean P θ) :
    P (fun y => Real.log (Real.exp (-((y - θ) ^ 2 / (2 * σ ^ 2)))
        / Real.exp (-((y - lam) ^ 2 / (2 * σ ^ 2)))))
      = (θ - lam) ^ 2 / (2 * σ ^ 2) := by
  have hσ2 : (σ : ℝ) ^ 2 ≠ 0 := by positivity
  have hrw : (fun y : ℝ => Real.log (Real.exp (-((y - θ) ^ 2 / (2 * σ ^ 2)))
        / Real.exp (-((y - lam) ^ 2 / (2 * σ ^ 2)))))
      = (fun y : ℝ => ((θ - lam) / σ ^ 2) * y + (lam ^ 2 - θ ^ 2) / (2 * σ ^ 2)) := by
    funext y
    exact gaussian_log_ratio_affine θ lam σ hσ y
  rw [hrw, hP]
  field_simp
  ring

/-- **The Gaussian expectation has the affine action**, with the mean supplied by Mathlib's
`integral_id_gaussianReal` and integrability of the identity by `memLp_id_gaussianReal`.
This is the step that was missing: without it the identity above was a statement about an
abstract functional that nothing was known to satisfy. -/
theorem affineMean_gaussianReal (θ : ℝ) (v : ℝ≥0) :
    AffineMean (fun f => ∫ y, f y ∂(ProbabilityTheory.gaussianReal θ v)) θ := by
  intro a b
  show ∫ y, (a * y + b) ∂(ProbabilityTheory.gaussianReal θ v) = a * θ + b
  have hint : MeasureTheory.Integrable (fun y : ℝ => y)
      (ProbabilityTheory.gaussianReal θ v) := by
    have h := ProbabilityTheory.memLp_id_gaussianReal (μ := θ) (v := v) 1
    simpa [Function.id_def, MeasureTheory.memLp_one_iff_integrable] using h
  rw [MeasureTheory.integral_add (hint.const_mul a) (MeasureTheory.integrable_const b),
      MeasureTheory.integral_const_mul, ProbabilityTheory.integral_id_gaussianReal,
      MeasureTheory.integral_const]
  simp

/-- **The identity, at the Gaussian measure itself.**  No abstract functional, no hypothesis
about it: the observation law is `gaussianReal`, and the integral of the log-density ratio
is the squared gap over twice the variance.

Only the MEAN of the integrating measure enters, which is why `v` is arbitrary here; the
Kullback-Leibler reading is the case `v = sigma^2`, recorded separately below. -/
theorem gaussian_kl_eq_sq_gap_gaussianReal (θ lam σ : ℝ) (hσ : 0 < σ) (v : ℝ≥0) :
    ∫ y, Real.log (Real.exp (-((y - θ) ^ 2 / (2 * σ ^ 2)))
        / Real.exp (-((y - lam) ^ 2 / (2 * σ ^ 2))))
      ∂(ProbabilityTheory.gaussianReal θ v)
      = (θ - lam) ^ 2 / (2 * σ ^ 2) :=
  gaussian_kl_eq_sq_gap θ lam σ hσ _ (affineMean_gaussianReal θ v)

/-- **The Kullback-Leibler divergence of two equal-variance Gaussians.**  The integrating
measure is `N(theta, sigma^2)` and the integrand is the log-ratio of the `N(theta, sigma^2)`
and `N(lambda, sigma^2)` densities, so this is the divergence itself and not a stand-in for
it.  This is the statement `LeanPaperASeparationV1` needs in order to call an energy an
information. -/
theorem gaussian_kl_at_matching_variance (θ lam σ : ℝ) (hσ : 0 < σ) :
    ∫ y, Real.log (Real.exp (-((y - θ) ^ 2 / (2 * σ ^ 2)))
        / Real.exp (-((y - lam) ^ 2 / (2 * σ ^ 2))))
      ∂(ProbabilityTheory.gaussianReal θ (Real.toNNReal (σ ^ 2)))
      = (θ - lam) ^ 2 / (2 * σ ^ 2) :=
  gaussian_kl_eq_sq_gap_gaussianReal θ lam σ hσ _

/-- The variance of that measure really is `sigma^2`, so the name of the corollary above
matches the object it is about. -/
theorem matching_variance_coe (σ : ℝ) : ((Real.toNNReal (σ ^ 2) : ℝ≥0) : ℝ) = σ ^ 2 :=
  Real.coe_toNNReal _ (sq_nonneg σ)

/-- **The energy is the weighted information.**  With `gaussian_kl_eq_sq_gap` identifying
the per-cell divergence, a design's energy is the information its queries carry -- which is
what lets `LeanPaperASeparationV1` optimise energies and speak about information. -/
theorem energy_eq_weighted_sqGap (E : ℕ) (w var θ lam : ℕ → ℝ) :
    (∑ e ∈ Finset.range E, w e * (lam e - θ e) ^ 2 / var e) / 2
      = ∑ e ∈ Finset.range E, w e * sqGapFunctional var θ lam e := by
  classical
  unfold sqGapFunctional
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [show (lam e - θ e) ^ 2 = (θ e - lam e) ^ 2 by ring]
  ring

/-! ## Audit -/

#print axioms gaussian_log_ratio_affine
#print axioms affineMean_gaussianReal
#print axioms gaussian_kl_eq_sq_gap_gaussianReal
#print axioms gaussian_kl_at_matching_variance
#print axioms matching_variance_coe
#print axioms productExpectation_sum_smul
#print axioms productResponse_sum_smul
#print axioms residual_eq_inner
#print axioms loss_eq_half_range
#print axioms extendedFamily_sum
#print axioms compl_retainedIn
#print axioms sumComponent_compl_eq_residual
#print axioms selectedRadius_eq_compressionLoss
#print axioms productExpectation_const
#print axioms productExpectation_add
#print axioms centered_additive_response
#print axioms gaussian_kl_eq_sq_gap
#print axioms energy_eq_weighted_sqGap

end CIGAMF.P13.PaperAModelBridge
