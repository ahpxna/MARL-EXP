import Mathlib
import «LeanSupportGeometryV4»

/-!
# Paper A, package A-model: the alternative set is the union over EVERY competitor.

## WHY THIS MODULE EXISTS

`LeanPaperAAlternativesV1` characterises the alternative set of a retained set `T` against
ONE competitor.  An oracle that only looks at one competitor is not an oracle: an answer is
alternative as soon as SOME other answer beats it, and missing a competitor makes the
alternative set too small and the information rate too large.  This module states and proves
the characterisation with the union taken over all competitors and all ways of pinning the
four extrema, so the alternative set is exactly what the decision rule says it is.

## THE SHAPE

For each answer `T` the loss is half the range of a linear form,

    2 L_lambda (T) = max_{x in K} <a_T(x), lambda> - min_{x in K} <a_T(x), lambda>,

with `a_T` the coefficient vector DERIVED in `LeanPaperAModelBridgeV1`.  Pinning a maximiser
`p` and a minimiser `m` for `T`, and `p'`, `m'` for a competitor `S`, the difference of the
two losses becomes a single linear form,

    2 [L_lambda (T) - L_lambda (S)] = <v(T,S,p,m,p',m'), lambda>,                 (*)

with

    v_l = a_T(p)_l - a_T(m)_l - a_S(p')_l + a_S(m')_l.

The region on which that pinning is valid is cut out by the linear inequalities
"`p` maximises", "`m` minimises", and so on -- each a finite family of inequalities in
`lambda`.  So the alternative set is a finite union of (region, half-space) pieces.

## WHAT IS PROVED

`alt_iff_exists_region_any` is an IFF, over all competitors: the left-to-right direction
needs that the true extrema pin some region, the right-to-left that any validly pinned
region witnesses a genuine loss gap.  Both are proved.  `altSet_eq_biUnion` restates it as a
set equality, and `alt_region_finite` records that the index set is finite, which is what
makes an exhaustive solver possible at all.

Nothing here assumes a particular competitor is the binding one; which competitor binds is
an output of the characterisation, not an input to it.
-/

namespace CIGAMF.P13.PaperAAlternativeUnion

open scoped BigOperators
open CIGAMF.V4.SupportGeometry

variable {d : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans]

/-- The linear form a coefficient vector defines on parameter space. -/
noncomputable def linForm (a : X → Fin d → ℝ) (lam : Fin d → ℝ) (x : X) : ℝ :=
  ∑ l, a x l * lam l

/-- `p` maximises `f` on `K`.  This is the region condition, and in `lambda` it is a finite
family of linear inequalities -- which is what makes the region polyhedral. -/
def AttainsMax (K : Finset X) (f : X → ℝ) (p : X) : Prop :=
  p ∈ K ∧ ∀ y ∈ K, f y ≤ f p

/-- `m` minimises `f` on `K`. -/
def AttainsMin (K : Finset X) (f : X → ℝ) (m : X) : Prop :=
  m ∈ K ∧ ∀ y ∈ K, f m ≤ f y

theorem attainsMax_eq_maxOn (K : Finset X) (hK : K.Nonempty) (f : X → ℝ) {p : X}
    (hp : AttainsMax K f p) : f p = CIGAMF.V4.SupportGeometry.maxOn K hK f := by
  classical
  unfold CIGAMF.V4.SupportGeometry.maxOn
  refine le_antisymm ?_ ?_
  · exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p, hp.1, rfl⟩)
  · refine (Finset.max'_le_iff _ _).2 ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact hp.2 z hz

theorem attainsMin_eq_minOn (K : Finset X) (hK : K.Nonempty) (f : X → ℝ) {m : X}
    (hm : AttainsMin K f m) : f m = CIGAMF.V4.SupportGeometry.minOn K hK f := by
  classical
  unfold CIGAMF.V4.SupportGeometry.minOn
  refine le_antisymm ?_ ?_
  · refine (Finset.le_min' _ _ _ ?_)
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
    exact hm.2 z hz
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨m, hm.1, rfl⟩)

/-- Every finite nonempty support has a maximiser and a minimiser of any real function.
This is what lets the left-to-right direction pin a region. -/
theorem exists_attains (K : Finset X) (hK : K.Nonempty) (f : X → ℝ) :
    (∃ p, AttainsMax K f p) ∧ (∃ m, AttainsMin K f m) := by
  classical
  constructor
  · obtain ⟨p, hpK, hp⟩ := K.exists_max_image f hK
    exact ⟨p, hpK, hp⟩
  · obtain ⟨m, hmK, hm⟩ := K.exists_min_image f hK
    exact ⟨m, hmK, hm⟩

/-- The loss of an answer: half the range of its linear form on the deployment support. -/
noncomputable def loss (K : Finset X) (hK : K.Nonempty)
    (a : Ans → X → Fin d → ℝ) (T : Ans) (lam : Fin d → ℝ) : ℝ :=
  CIGAMF.V4.SupportGeometry.oscOn K hK (linForm (a T) lam) / 2

/-- The contrast vector of display (*): a single vector whose linear form is twice the loss
difference, once the four extrema are pinned. -/
noncomputable def contrastVec (a : Ans → X → Fin d → ℝ) (T S : Ans) (p m p' m' : X)
    (l : Fin d) : ℝ :=
  a T p l - a T m l - a S p' l + a S m' l

/-- **(*)**: on a region, the loss difference is a single linear form. -/
theorem two_loss_sub_eq_contrast (K : Finset X) (hK : K.Nonempty)
    (a : Ans → X → Fin d → ℝ) (T S : Ans) (lam : Fin d → ℝ) {p m p' m' : X}
    (hp : AttainsMax K (linForm (a T) lam) p)
    (hm : AttainsMin K (linForm (a T) lam) m)
    (hp' : AttainsMax K (linForm (a S) lam) p')
    (hm' : AttainsMin K (linForm (a S) lam) m') :
    2 * (loss K hK a T lam - loss K hK a S lam)
      = ∑ l, contrastVec a T S p m p' m' l * lam l := by
  classical
  unfold loss CIGAMF.V4.SupportGeometry.oscOn contrastVec
  rw [← attainsMax_eq_maxOn K hK _ hp, ← attainsMin_eq_minOn K hK _ hm,
      ← attainsMax_eq_maxOn K hK _ hp', ← attainsMin_eq_minOn K hK _ hm']
  unfold linForm
  have hexp : ∑ l, (a T p l - a T m l - a S p' l + a S m' l) * lam l
      = (∑ l, a T p l * lam l) - (∑ l, a T m l * lam l)
        - (∑ l, a S p' l * lam l) + (∑ l, a S m' l * lam l) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hexp]
  ring

/-- The alternative set at tolerance `eps`: some competitor beats `T` by more than `eps`. -/
def AltSet (K : Finset X) (hK : K.Nonempty) (a : Ans → X → Fin d → ℝ)
    (T : Ans) (eps : ℝ) : Set (Fin d → ℝ) :=
  {lam | ∃ S : Ans, loss K hK a T lam > loss K hK a S lam + eps}

/-- **The oracle, over every competitor.**  A parameter is alternative exactly when some
competitor and some valid pinning of the four extrema make the contrast exceed `2 eps`.
The union is over all of `Ans`, not a selected competitor. -/
theorem alt_iff_exists_region_any (K : Finset X) (hK : K.Nonempty)
    (a : Ans → X → Fin d → ℝ) (T : Ans) (eps : ℝ) (lam : Fin d → ℝ) :
    lam ∈ AltSet K hK a T eps ↔
      ∃ (S : Ans) (p m p' m' : X),
        AttainsMax K (linForm (a T) lam) p ∧
        AttainsMin K (linForm (a T) lam) m ∧
        AttainsMax K (linForm (a S) lam) p' ∧
        AttainsMin K (linForm (a S) lam) m' ∧
        2 * eps < ∑ l, contrastVec a T S p m p' m' l * lam l := by
  classical
  constructor
  · rintro ⟨S, hS⟩
    obtain ⟨⟨p, hp⟩, ⟨m, hm⟩⟩ := exists_attains K hK (linForm (a T) lam)
    obtain ⟨⟨p', hp'⟩, ⟨m', hm'⟩⟩ := exists_attains K hK (linForm (a S) lam)
    refine ⟨S, p, m, p', m', hp, hm, hp', hm', ?_⟩
    rw [← two_loss_sub_eq_contrast K hK a T S lam hp hm hp' hm']
    linarith
  · rintro ⟨S, p, m, p', m', hp, hm, hp', hm', hgt⟩
    refine ⟨S, ?_⟩
    have := two_loss_sub_eq_contrast K hK a T S lam hp hm hp' hm'
    rw [← this] at hgt
    linarith

/-- The same statement as a set equality: the alternative set IS the union of its pieces,
indexed by a competitor and a pinning. -/
theorem altSet_eq_biUnion (K : Finset X) (hK : K.Nonempty)
    (a : Ans → X → Fin d → ℝ) (T : Ans) (eps : ℝ) :
    AltSet K hK a T eps
      = ⋃ (S : Ans) (p : X) (m : X) (p' : X) (m' : X),
          {lam : Fin d → ℝ |
            AttainsMax K (linForm (a T) lam) p ∧
            AttainsMin K (linForm (a T) lam) m ∧
            AttainsMax K (linForm (a S) lam) p' ∧
            AttainsMin K (linForm (a S) lam) m' ∧
            2 * eps < ∑ l, contrastVec a T S p m p' m' l * lam l} := by
  classical
  ext lam
  rw [alt_iff_exists_region_any K hK a T eps lam]
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]

/-- The index set of the union is finite, which is what makes exhaustive certification
possible.  With `|Ans|` answers and `|X|` support points there are `|Ans| * |X|^4` pieces. -/
theorem alt_region_finite : Fintype.card (Ans × X × X × X × X)
    = Fintype.card Ans * (Fintype.card X * (Fintype.card X *
        (Fintype.card X * Fintype.card X))) := by
  simp [Fintype.card_prod]

/-- On a fixed region the alternative condition is a LINEAR inequality in `lambda`: the
contrast vector does not depend on `lambda`, only on the pinning.  This is why each piece is
a polyhedron and the regional minimum is a convex quadratic program. -/
theorem region_condition_is_linear (a : Ans → X → Fin d → ℝ) (T S : Ans) (p m p' m' : X)
    (lam mu : Fin d → ℝ) (s t : ℝ) :
    ∑ l, contrastVec a T S p m p' m' l * (s * lam l + t * mu l)
      = s * (∑ l, contrastVec a T S p m p' m' l * lam l)
        + t * (∑ l, contrastVec a T S p m p' m' l * mu l) := by
  classical
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun l _ => by ring)

/-- If no competitor beats `T` anywhere, the alternative set is empty: an answer with no
alternative is globally safe, and the information rate question does not arise for it.
This is the case that must be given its own branch in any algorithm. -/
theorem altSet_empty_of_no_competitor (K : Finset X) (hK : K.Nonempty)
    (a : Ans → X → Fin d → ℝ) (T : Ans) (eps : ℝ)
    (hsafe : ∀ (S : Ans) (lam : Fin d → ℝ),
      loss K hK a T lam ≤ loss K hK a S lam + eps) :
    AltSet K hK a T eps = ∅ := by
  classical
  ext lam
  simp only [AltSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
  intro S
  exact hsafe S lam

/-! ## Audit -/

#print axioms attainsMax_eq_maxOn
#print axioms attainsMin_eq_minOn
#print axioms exists_attains
#print axioms two_loss_sub_eq_contrast
#print axioms alt_iff_exists_region_any
#print axioms altSet_eq_biUnion
#print axioms region_condition_is_linear
#print axioms altSet_empty_of_no_competitor

end CIGAMF.P13.PaperAAlternativeUnion
