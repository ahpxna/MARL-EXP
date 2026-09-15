import «LeanBinaryKLTwoPointV1»
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Binary Pinsker: `2*(p-q)^2 ≤ binaryKL p q`

Mathlib carries no Pinsker inequality, on this pin or on master (checked by
tree listing, not recalled). This is the sharp replacement for
`two_point_error_weak`.

Route, every Mathlib name read from the pin:

* `g = fun x => binaryKL x q - 2*(x-q)^2` on the OPEN set `D = Ioo 0 1`, so
  `interior D = D`;
* `g' x = log (x/q) - log ((1-x)/(1-q)) - 4*(x-q)`, which vanishes at `x = q`;
* `g'' x = 1/x + 1/(1-x) - 4 = (1-2*x)^2/(x*(1-x)) ≥ 0`
  (`BinaryKLTwoPoint.pinsker_curvature_nonneg`);
* `convexOn_of_hasDerivWithinAt2_nonneg` takes `f'` and `f''` as DATA, so no
  symbolic `deriv` is computed;
* `ConvexOn.isMinOn_of_rightDeriv_eq_zero` turns the stationary point into a
  global minimum;
* `g q = 0` closes it.

`binaryKL` is defined by `log` of a quotient, so it is total but agrees with the
four-term expansion only on `Ioo 0 1`. Every derivative is therefore transported
with `HasDerivAt.congr_of_eventuallyEq` across that open set rather than proved
for a globally equal function.
-/
namespace CIGAMF.BinaryPinsker
open Real Set Filter
open CIGAMF.BinaryKLTwoPoint

/-- On `Ioo 0 1` the divergence is four elementary terms. -/
theorem binaryKL_expand {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    binaryKL p q=p*Real.log p-p*Real.log q+((1-p)*Real.log (1-p)-(1-p)*Real.log (1-q)) := by
  unfold binaryKL
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq),Real.log_div (by linarith) (by linarith)]
  ring

/-- `x ↦ 1 - x`, via the dedicated `const_sub` lemma rather than `.sub` of two
derivatives, which produces the Pi-subtraction `(fun _ => 1) - id` in a
different module instance. -/
theorem hasDerivAt_one_sub (p : ℝ) : HasDerivAt (fun x : ℝ => 1-x) (-1) p := by
  simpa using (hasDerivAt_id p).const_sub (1:ℝ)

/-- `x ↦ log x`. -/
theorem hasDerivAt_log_self {p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log x) (1/p) p := by
  simpa [one_div] using (hasDerivAt_id p).log hp

/-- `x ↦ log (1-x)`, via `HasDerivAt.log`, which already folds the composition. -/
theorem hasDerivAt_log_one_sub {p : ℝ} (hp : (1:ℝ)-p ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log (1-x)) (-1/(1-p)) p := by
  simpa using (hasDerivAt_one_sub p).log (by simpa using hp)

/-- `x ↦ x*log x`. -/
theorem hasDerivAt_mul_log {p : ℝ} (hp : p ≠ 0) :
    HasDerivAt (fun x : ℝ => x*Real.log x) (Real.log p+1) p := by
  have h := (hasDerivAt_id p).mul (hasDerivAt_log_self hp)
  have he : ((id : ℝ → ℝ)*fun x : ℝ => Real.log x)=(fun x : ℝ => x*Real.log x) := by
    funext x; rfl
  rw [he] at h
  refine h.congr_deriv ?_
  rw [id_eq,one_mul,mul_one_div,div_self hp]

/-- `x ↦ (1-x)*log (1-x)`. -/
theorem hasDerivAt_one_sub_mul_log {p : ℝ} (hp : (1:ℝ)-p ≠ 0) :
    HasDerivAt (fun x : ℝ => (1-x)*Real.log (1-x)) (-(Real.log (1-p)+1)) p := by
  have h := (hasDerivAt_one_sub p).mul (hasDerivAt_log_one_sub hp)
  have he : ((fun x : ℝ => 1-x)*fun x : ℝ => Real.log (1-x))=
      (fun x : ℝ => (1-x)*Real.log (1-x)) := by funext x; rfl
  rw [he] at h
  refine h.congr_deriv ?_
  field_simp
  ring

/-- `x ↦ (x-q)^2`, via `.mul` rather than `.pow`, which produces the Pi-power. -/
theorem hasDerivAt_sq_sub (p q : ℝ) :
    HasDerivAt (fun x : ℝ => (x-q)^2) (2*(p-q)) p := by
  have hb := (hasDerivAt_id p).sub_const q
  simp only [id_eq] at hb
  have h := hb.mul hb
  have he : ((fun x : ℝ => x-q)*fun x : ℝ => x-q)=(fun x : ℝ => (x-q)^2) := by
    funext x
    show (x-q)*(x-q)=(x-q)^2
    ring
  rw [he] at h
  exact h.congr_deriv (by ring)

/-- First derivative of the gap, transported across `Ioo 0 1`. -/
theorem hasDerivAt_gap {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun x : ℝ => binaryKL x q-2*(x-q)^2)
      (Real.log (p/q)-Real.log ((1-p)/(1-q))-4*(p-q)) p := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have h1p : (1:ℝ)-p ≠ 0 := by intro h; linarith
  have h1 := hasDerivAt_mul_log hp0
  have h2 := (hasDerivAt_id p).mul_const (Real.log q)
  simp only [id_eq,one_mul] at h2
  have h3 := hasDerivAt_one_sub_mul_log h1p
  have h4 := (hasDerivAt_one_sub p).mul_const (Real.log (1-q))
  have h5 := (hasDerivAt_sq_sub p q).const_mul (2:ℝ)
  have hsum := ((h1.sub h2).add (h3.sub h4)).sub h5
  have heq : (fun x : ℝ => binaryKL x q-2*(x-q)^2) =ᶠ[nhds p]
      (fun x : ℝ => x*Real.log x-x*Real.log q+((1-x)*Real.log (1-x)-
        (1-x)*Real.log (1-q))-2*(x-q)^2) :=
    eventuallyEq_of_mem (Ioo_mem_nhds hp hp1)
      (fun x hx => by rw [binaryKL_expand hx.1 hx.2 hq hq1])
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  rw [Real.log_div hp0 (ne_of_gt hq),
    Real.log_div h1p (by intro h; linarith : (1:ℝ)-q ≠ 0)]
  ring

/-- Second derivative of the gap.  `log (x/q) = log x - log q` is FALSE at
`x = 0` (the left side is `0`), so the split is transported across `Ioo 0 1`
with `EventuallyEq` rather than rewritten globally. -/
theorem hasDerivAt_gap' {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun x : ℝ => Real.log (x/q)-Real.log ((1-x)/(1-q))-4*(x-q))
      (1/p+1/(1-p)-4) p := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have h1p : (1:ℝ)-p ≠ 0 := by intro h; linarith
  have hq0 : q ≠ 0 := ne_of_gt hq
  have h1q : (1:ℝ)-q ≠ 0 := by intro h; linarith
  have d1 := (hasDerivAt_log_self hp0).sub_const (Real.log q)
  have d2 := (hasDerivAt_log_one_sub h1p).sub_const (Real.log (1-q))
  have d3 := (hasDerivAt_id p).sub_const q
  simp only [id_eq] at d3
  have d4 := d3.const_mul (4:ℝ)
  have hsum := (d1.sub d2).sub d4
  have heq : (fun x : ℝ => Real.log (x/q)-Real.log ((1-x)/(1-q))-4*(x-q)) =ᶠ[nhds p]
      (fun x : ℝ => (Real.log x-Real.log q)-(Real.log (1-x)-Real.log (1-q))-4*(x-q)) :=
    eventuallyEq_of_mem (Ioo_mem_nhds hp hp1) (fun x hx => by
      rw [Real.log_div (ne_of_gt hx.1) hq0,
        Real.log_div (by intro h; linarith [hx.2] : (1:ℝ)-x ≠ 0) h1q])
  refine (hsum.congr_of_eventuallyEq heq).congr_deriv ?_
  ring

/-- **Binary Pinsker.** -/
theorem binary_pinsker {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) :
    2*(p-q)^2 ≤ binaryKL p q := by
  set D : Set ℝ := Ioo 0 1 with hD
  have hopen : interior D = D := IsOpen.interior_eq isOpen_Ioo
  set g : ℝ → ℝ := fun x => binaryKL x q-2*(x-q)^2 with hg
  set g' : ℝ → ℝ := fun x => Real.log (x/q)-Real.log ((1-x)/(1-q))-4*(x-q) with hg'
  set g'' : ℝ → ℝ := fun x => 1/x+1/(1-x)-4 with hg''
  have hderiv : ∀ x ∈ interior D,HasDerivWithinAt g (g' x) (interior D) x := by
    intro x hx
    rw [hopen] at hx ⊢
    exact (hasDerivAt_gap hx.1 hx.2 hq hq1).hasDerivWithinAt
  have hderiv2 : ∀ x ∈ interior D,HasDerivWithinAt g' (g'' x) (interior D) x := by
    intro x hx
    rw [hopen] at hx ⊢
    exact (hasDerivAt_gap' hx.1 hx.2 hq hq1).hasDerivWithinAt
  have hnn : ∀ x ∈ interior D,0 ≤ g'' x := by
    intro x hx
    rw [hopen] at hx
    exact pinsker_curvature_nonneg hx.1 hx.2
  have hcont : ContinuousOn g D := by
    intro x hx
    exact ((hasDerivAt_gap hx.1 hx.2 hq hq1).continuousAt).continuousWithinAt
  have hconv : ConvexOn ℝ D g :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo 0 1) hcont hderiv hderiv2 hnn
  have hqD : q ∈ interior D := by rw [hopen]; exact ⟨hq,hq1⟩
  have hzero : derivWithin g (Ioi q) q=0 := by
    have hgq : HasDerivAt g (g' q) q := hasDerivAt_gap hq hq1 hq hq1
    have hg'q : g' q=0 := by
      simp only [hg']
      rw [div_self (ne_of_gt hq),div_self (by linarith : (1:ℝ)-q ≠ 0),Real.log_one]
      ring
    rw [hg'q] at hgq
    exact hgq.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi q)
  have hmin := hconv.isMinOn_of_rightDeriv_eq_zero hqD hzero
  have hpD : p ∈ D := ⟨hp,hp1⟩
  have h := hmin hpD
  simp only [hg,Set.mem_setOf_eq] at h
  have hgq0 : binaryKL q q-2*(q-q)^2=0 := by
    unfold binaryKL
    rw [div_self (ne_of_gt hq),div_self (by linarith : (1:ℝ)-q ≠ 0),Real.log_one]
    ring
  linarith [h,hgq0.le,hgq0.ge]

#print axioms binaryKL_expand
#print axioms hasDerivAt_gap
#print axioms hasDerivAt_gap'
#print axioms binary_pinsker

end CIGAMF.BinaryPinsker
