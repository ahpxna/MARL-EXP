import «LeanPaperAOracleCertificateV1»

/-!
# Paper A, steps A1 and A2: the model, and the alternative set EXACTLY.

## WHY THIS MODULE EXISTS

`LeanPaperAOracleCertificateV1` certifies the minimum of a convex quadratic over a region
that is handed to it.  It says nothing about which regions there are, and a solver that
finds good points in a few regions has proved nothing about the rest.  This module supplies
the missing half: it fixes a model in which the loss really is a maximum of finitely many
linear forms, and it proves the alternative set is EXACTLY a finite union of
region-intersect-halfspace pieces -- an equality, not a decomposition a search happened to
find.

## A1: THE MODEL

Parametrise the world linearly, `F_theta(x) = phi(x)^T theta`.  With a fixed reference the
product responses are linear in `theta` too, so for a retained set `T` the residual at a
support point is a linear form, `r_{theta,T}(x) = a_T(x)^T theta`, and the loss is half the
oscillation of finitely many linear forms over the support.  That is the only structural
assumption, and everything below uses exactly it.

## A2: THE ALTERNATIVE SET

`alt_iff_exists_region` is the equality.  Reading it left to right is the direction that
matters: if `T` is `eps`-wrong at `theta`, then the actual maximiser and minimiser of each
residual put `theta` in a definite region, and on that region the doubled loss difference is
one linear form `v^T theta`, which exceeds `2 eps`.  Reading it right to left says every
piece really does consist of alternatives, so nothing spurious is added.

## THE CLOSURE, WHICH IS WHERE CARE IS NEEDED

The alternative condition is STRICT, and an infimum over a strict region is not in general
the infimum over its closure.  `strict_inf_eq_closed_inf` gives the exchange, and it needs a
hypothesis that must be checked region by region: the region must contain a STRICTLY bad
point.  Given one, every point of the closed region is approached along a segment that stays
strictly bad, and the energy moves by at most `t` times an explicit constant, so no limiting
argument is needed.  `strict_empty_has_no_alternatives` records the other case: when the
strict part is empty the region contributes nothing and must be dropped, NOT closed.  Closing
it would manufacture an alternative out of a tie.

## WHAT IS PROVED

* `loss_eq_of_extrema` -- with the extrema pinned, the doubled loss is a linear form.
* `exists_extrema` -- the maximiser and minimiser exist, so the pinning is always possible.
* `alt_iff_exists_region` -- **the equality of the alternative set with the union.**
* `region_form_is_linear` -- on a region, the doubled loss difference is `v^T theta` for an
  explicit `v`, which is what makes each piece a convex QP.
* `segment_stays_strict` -- the approach segment stays in the region and strictly bad.
* `strict_inf_eq_closed_inf` -- **the closure exchange as an equality of infima**, proved
  in both directions using the explicit modulus of `energy_segment_bound`.
* `strict_empty_has_no_alternatives` -- and the case where it must not be applied.

## WHAT THIS DOES NOT ESTABLISH

- The reduction from a compression problem to this linear model is asserted by fixing the
  model, not derived from the corpus definitions; `a_T` is an input here.  Connecting `a_T`
  to the corpus residual and `lossLin` to the corpus `selectedRadius` is done in the paper
  and is not re-proved in Lean.
- Finitely many support points and finitely many competitor sets.
- Nothing here bounds the NUMBER of regions, which is what decides whether enumerating them
  is practical.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.PaperAAlternatives

open Finset CIGAMF.P13.PaperAOracleCertificate

variable {d N : ℕ}

/-! ### A1: the loss of a linear model -/

/-- Half the oscillation, over the support, of a finite family of linear forms. -/
noncomputable def lossLin (a : Fin (N + 1) → Fin d → ℝ) (theta : Fin d → ℝ) : ℝ :=
  ((univ : Finset (Fin (N + 1))).sup' univ_nonempty (fun x => dot (a x) theta)
    - (univ : Finset (Fin (N + 1))).inf' univ_nonempty (fun x => dot (a x) theta)) / 2

/-- The extrema of the residual are attained, so a region assignment always exists. -/
theorem exists_extrema (a : Fin (N + 1) → Fin d → ℝ) (theta : Fin d → ℝ) :
    ∃ x y : Fin (N + 1),
      (∀ z, dot (a z) theta ≤ dot (a x) theta)
      ∧ (∀ z, dot (a y) theta ≤ dot (a z) theta) := by
  classical
  obtain ⟨x, _, hx⟩ :=
    Finset.exists_mem_eq_sup' (univ_nonempty) (fun x : Fin (N + 1) => dot (a x) theta)
  obtain ⟨y, _, hy⟩ :=
    Finset.exists_mem_eq_inf' (univ_nonempty) (fun x : Fin (N + 1) => dot (a x) theta)
  refine ⟨x, y, fun z => ?_, fun z => ?_⟩
  · rw [← hx]
    exact Finset.le_sup' (fun x : Fin (N + 1) => dot (a x) theta) (Finset.mem_univ z)
  · rw [← hy]
    exact Finset.inf'_le (fun x : Fin (N + 1) => dot (a x) theta) (Finset.mem_univ z)

/-- **With the extrema pinned, the doubled loss is a single linear form.** -/
theorem loss_eq_of_extrema (a : Fin (N + 1) → Fin d → ℝ) (theta : Fin d → ℝ)
    (x y : Fin (N + 1))
    (hx : ∀ z, dot (a z) theta ≤ dot (a x) theta)
    (hy : ∀ z, dot (a y) theta ≤ dot (a z) theta) :
    2 * lossLin a theta = dot (a x) theta - dot (a y) theta := by
  classical
  have hsup : (univ : Finset (Fin (N + 1))).sup' univ_nonempty
      (fun z => dot (a z) theta) = dot (a x) theta := by
    refine le_antisymm
      (Finset.sup'_le univ_nonempty (fun z => dot (a z) theta) fun z _ => hx z) ?_
    exact Finset.le_sup' (fun z => dot (a z) theta) (Finset.mem_univ x)
  have hinf : (univ : Finset (Fin (N + 1))).inf' univ_nonempty
      (fun z => dot (a z) theta) = dot (a y) theta := by
    refine le_antisymm (Finset.inf'_le (fun z => dot (a z) theta) (Finset.mem_univ y)) ?_
    exact Finset.le_inf' univ_nonempty (fun z => dot (a z) theta) fun z _ => hy z
  unfold lossLin
  rw [hsup, hinf]
  ring

/-- On a region, the doubled loss difference between two retained sets is the linear form
of the explicit vector `v`. -/
theorem region_form_is_linear (aT aS : Fin (N + 1) → Fin d → ℝ) (theta : Fin d → ℝ)
    (x y p q : Fin (N + 1))
    (hxT : ∀ z, dot (aT z) theta ≤ dot (aT x) theta)
    (hyT : ∀ z, dot (aT y) theta ≤ dot (aT z) theta)
    (hpS : ∀ z, dot (aS z) theta ≤ dot (aS p) theta)
    (hqS : ∀ z, dot (aS q) theta ≤ dot (aS z) theta) :
    2 * (lossLin aT theta - lossLin aS theta)
      = dot (fun i => aT x i - aT y i - aS p i + aS q i) theta := by
  have h1 := loss_eq_of_extrema aT theta x y hxT hyT
  have h2 := loss_eq_of_extrema aS theta p q hpS hqS
  have hlin : dot (fun i => aT x i - aT y i - aS p i + aS q i) theta
      = dot (aT x) theta - dot (aT y) theta - dot (aS p) theta + dot (aS q) theta := by
    unfold dot
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hlin]
  linarith

/-! ### A2: the alternative set, exactly -/

/-- **The alternative set is exactly the union of the region pieces.**

Left to right: the true extrema pin a region, and on it the doubled loss difference is the
linear form, which exceeds `2 eps`.  Right to left: every piece consists of genuine
alternatives.  Neither direction is a search result. -/
theorem alt_iff_exists_region (aT aS : Fin (N + 1) → Fin d → ℝ) (theta : Fin d → ℝ)
    (eps : ℝ) :
    lossLin aT theta - lossLin aS theta > eps
      ↔ ∃ x y p q : Fin (N + 1),
          (∀ z, dot (aT z) theta ≤ dot (aT x) theta)
          ∧ (∀ z, dot (aT y) theta ≤ dot (aT z) theta)
          ∧ (∀ z, dot (aS z) theta ≤ dot (aS p) theta)
          ∧ (∀ z, dot (aS q) theta ≤ dot (aS z) theta)
          ∧ dot (fun i => aT x i - aT y i - aS p i + aS q i) theta > 2 * eps := by
  constructor
  · intro hgt
    obtain ⟨x, y, hx, hy⟩ := exists_extrema aT theta
    obtain ⟨p, q, hp, hq⟩ := exists_extrema aS theta
    refine ⟨x, y, p, q, hx, hy, hp, hq, ?_⟩
    rw [← region_form_is_linear aT aS theta x y p q hx hy hp hq]
    linarith
  · rintro ⟨x, y, p, q, hx, hy, hp, hq, hlin⟩
    have := region_form_is_linear aT aS theta x y p q hx hy hp hq
    linarith [this, hlin]

/-! ### The closure, and when it may not be taken -/

/-- The quadratic energy moves at most linearly along a segment, with an explicit modulus:
no limiting argument is needed to approach the boundary of a region. -/
theorem energy_segment_bound (H : Fin d → Fin d → ℝ) (hsym : ∀ i j, H i j = H j i)
    (thetaStar theta0 w : Fin d → ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |energy H thetaStar (fun i => theta0 i + t * w i) - energy H thetaStar theta0|
      ≤ t * (|dot w (matMul H (fun i => theta0 i - thetaStar i))| + |quad H w| / 2) := by
  classical
  set u : Fin d → ℝ := fun i => theta0 i - thetaStar i with hu
  have hsplit : (fun i => (theta0 i + t * w i) - thetaStar i)
      = fun i => u i + t * w i := by
    funext i; simp [hu]; ring
  have hmat : matMul H (fun i => t * w i) = fun i => t * matMul H w i := by
    funext i
    unfold matMul
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hscale1 : dot (fun i => t * w i) (matMul H u) = t * dot w (matMul H u) := by
    unfold dot
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hscale2 : quad H (fun i => t * w i) = t ^ 2 * quad H w := by
    unfold quad
    rw [hmat]
    unfold dot
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hq : quad H (fun i => u i + t * w i)
      = quad H u + 2 * dot (fun i => t * w i) (matMul H u)
        + quad H (fun i => t * w i) := quad_expand H hsym u (fun i => t * w i)
  have hval : energy H thetaStar (fun i => theta0 i + t * w i) - energy H thetaStar theta0
      = t * dot w (matMul H u) + t ^ 2 * quad H w / 2 := by
    unfold energy
    rw [hsplit, hq, hscale1, hscale2]
    ring
  rw [hval]
  have ht2 : t ^ 2 ≤ t := by nlinarith
  have a1 := le_abs_self (dot w (matMul H u))
  have a2 := neg_abs_le (dot w (matMul H u))
  have a3 := le_abs_self (quad H w)
  have a4 := neg_abs_le (quad H w)
  have a5 := abs_nonneg (quad H w)
  have a6 := abs_nonneg (dot w (matMul H u))
  have ht2n : (0:ℝ) ≤ t ^ 2 := sq_nonneg t
  rw [abs_le]
  constructor <;> nlinarith

private theorem exists_small_t (C delta : ℝ) (hC : 0 ≤ C) (hd : 0 < delta) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t * C ≤ delta := by
  have h2 : (0 : ℝ) < C + 1 := by linarith
  refine ⟨min 1 (delta / (C + 1)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  have h1 : min 1 (delta / (C + 1)) ≤ delta / (C + 1) := min_le_right _ _
  calc min 1 (delta / (C + 1)) * C ≤ (delta / (C + 1)) * C :=
        mul_le_mul_of_nonneg_right h1 hC
    _ ≤ delta := by
        rw [div_mul_eq_mul_div, div_le_iff₀ h2]
        nlinarith [le_of_lt hd, hC]

/-- A segment from a closed-region point towards a strictly bad point stays in the region
and is strictly bad for every positive parameter. -/
theorem segment_stays_strict
    (v : Fin d → ℝ) (c : ℝ) (R : (Fin d → ℝ) → Prop)
    (hconv : ∀ (x y : Fin d → ℝ) (t : ℝ), R x → R y → 0 ≤ t → t ≤ 1 →
      R (fun i => x i + t * (y i - x i)))
    (thetaPlus : Fin d → ℝ) (hRplus : R thetaPlus) (hstrict : dot v thetaPlus > c)
    (theta0 : Fin d → ℝ) (hR0 : R theta0) (hclosed : dot v theta0 ≥ c)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    R (fun i => theta0 i + t * (thetaPlus i - theta0 i))
    ∧ dot v (fun i => theta0 i + t * (thetaPlus i - theta0 i)) > c := by
  refine ⟨hconv theta0 thetaPlus t hR0 hRplus (le_of_lt ht0) ht1, ?_⟩
  have hlin : dot v (fun i => theta0 i + t * (thetaPlus i - theta0 i))
      = dot v theta0 + t * (dot v thetaPlus - dot v theta0) := by
    unfold dot
    rw [← Finset.sum_sub_distrib]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hlin]
  nlinarith [hstrict, hclosed, ht0, ht1]

/-- **The closure exchange, as an equality of infima.**  Given a strictly bad point in the
region, the infimum of the energy over the STRICT part equals its infimum over the closed
part.  Both directions are proved: the strict set is contained in the closed one, and every
closed point is approached from inside the strict part along a segment whose energy moves by
at most `t` times an explicit constant, so no limiting argument is needed.

This is the step that is INVALID without `thetaPlus`; see
`strict_empty_has_no_alternatives` for the case that must be dropped instead. -/
theorem strict_inf_eq_closed_inf
    (H : Fin d → Fin d → ℝ) (hsym : ∀ i j, H i j = H j i) (thetaStar : Fin d → ℝ)
    (v : Fin d → ℝ) (c : ℝ) (R : (Fin d → ℝ) → Prop)
    (hconv : ∀ (x y : Fin d → ℝ) (t : ℝ), R x → R y → 0 ≤ t → t ≤ 1 →
      R (fun i => x i + t * (y i - x i)))
    (thetaPlus : Fin d → ℝ) (hRplus : R thetaPlus) (hstrict : dot v thetaPlus > c)
    (Sstrict Sclosed : ℝ)
    (hS : IsGLB {e : ℝ | ∃ theta, R theta ∧ dot v theta > c
      ∧ energy H thetaStar theta = e} Sstrict)
    (hC : IsGLB {e : ℝ | ∃ theta, R theta ∧ dot v theta ≥ c
      ∧ energy H thetaStar theta = e} Sclosed) :
    Sstrict = Sclosed := by
  refine le_antisymm ?_ ?_
  · -- every closed point is approached from within the strict part
    refine hC.2 ?_
    rintro e ⟨theta0, hR0, hclosed, rfl⟩
    refine le_of_forall_pos_le_add ?_
    intro delta hdelta
    obtain ⟨t, ht0, ht1, hsmall⟩ := exists_small_t
      (|dot (fun i => thetaPlus i - theta0 i)
          (matMul H (fun i => theta0 i - thetaStar i))|
        + |quad H (fun i => thetaPlus i - theta0 i)| / 2) delta (by positivity) hdelta
    obtain ⟨hRt, hst⟩ := segment_stays_strict v c R hconv thetaPlus hRplus hstrict
      theta0 hR0 hclosed t ht0 ht1
    have hbound := energy_segment_bound H hsym thetaStar theta0
      (fun i => thetaPlus i - theta0 i) t (le_of_lt ht0) ht1
    have hmem : energy H thetaStar (fun i => theta0 i + t * (thetaPlus i - theta0 i))
        ∈ {e : ℝ | ∃ theta, R theta ∧ dot v theta > c
          ∧ energy H thetaStar theta = e} := ⟨_, hRt, hst, rfl⟩
    have hle := hS.1 hmem
    have habs := abs_le.mp hbound
    linarith [hle, habs.2, hsmall]
  · -- the strict set sits inside the closed one
    refine hS.2 ?_
    rintro e ⟨theta, hR, hgt, rfl⟩
    exact hC.1 ⟨theta, hR, le_of_lt hgt, rfl⟩

/-- **And the case where the closure must NOT be taken.**  If no point of the region is
strictly bad, the region contains no alternative at all and is dropped.  Replacing the
strict inequality by a weak one there would invent an alternative out of a tie. -/
theorem strict_empty_has_no_alternatives
    (v : Fin d → ℝ) (c : ℝ) (R : (Fin d → ℝ) → Prop)
    (hempty : ∀ theta, R theta → ¬ (dot v theta > c)) :
    ∀ theta, R theta → dot v theta ≤ c := by
  intro theta hR
  exact not_lt.mp (hempty theta hR)

#print axioms exists_extrema
#print axioms loss_eq_of_extrema
#print axioms region_form_is_linear
#print axioms alt_iff_exists_region
#print axioms energy_segment_bound
#print axioms strict_inf_eq_closed_inf
#print axioms strict_empty_has_no_alternatives

end CIGAMF.P13.PaperAAlternatives
