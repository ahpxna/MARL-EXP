import «LeanSupportGeometryV4»

/-!
# Paper B: the overlapping-safe-answer construction, on the corpus's own `selectedRadius`

`LeanPaperBSafeOrderV1` proves the safe-order law and instantiates its GEOMETRY at safe sets
of the form "everything but one answer" --- but it NAMES those safe sets.  Here they are
**computed** from the corpus's actual compression loss, `selectedRadius`, which is half the
oscillation of the DISCARDED components over the deployment support.

With `m` answers, world `w` has support `{0, tip_w}` where `(tip_w)_i = -(m-2)` at `i = w`
and `1` elsewhere, and the components are the coordinates.  The tip's coordinates sum to
`-(m-2) + (m-1) = 1`, so retaining the single answer `j` leaves a discarded sum equal to `0`
at the origin and `1 - (tip_w)_j` at the tip --- that is `m-1` when `j = w` and `0`
otherwise.  Hence

    selectedRadius_w({j})  =  (m-1)/2   if j = w,      0   otherwise,

so at any tolerance below `(m-1)/2` the safe answers at `w` are exactly the ones other than
`w`: pairwise intersecting, with empty total intersection.  The geometry the law consumes is
now derived from the loss rather than posited.

WHAT REMAINS, AND IT IS THE SUBSTANCE.  This is the LOSS half.  The resolving-order table
--- that a parity-masked query at order `j` separates world `j` from the rest, and that no
admissible query does so sooner --- is a statement about densities and is **not** proved
here.  Without it the law's `sep` is still an input and `s_safe = 1`, `s_id = m-1` do not
follow from this file.
-/

namespace CIGAMF.P13.PaperBTip

open Finset CIGAMF.V4.SupportGeometry

/-! ## Oscillation over a two-point support -/

theorem maxVal_bool (g : Bool → ℝ) : maxVal g = max (g false) (g true) := by
  classical
  refine le_antisymm ?_ (max_le (le_maxVal g false) (le_maxVal g true))
  refine Finset.max'_le _ _ _ (fun y hy => ?_)
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
  cases b
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem minVal_bool (g : Bool → ℝ) : minVal g = min (g false) (g true) := by
  classical
  refine le_antisymm (le_min (minVal_le g false) (minVal_le g true)) ?_
  refine Finset.le_min' _ _ _ (fun y hy => ?_)
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hy
  cases b
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- **Oscillation over two points, one of which is zero, is the absolute value of the
other.** -/
theorem osc_bool_of_zero (g : Bool → ℝ) (h0 : g false = 0) : osc g = |g true| := by
  unfold osc
  rw [maxVal_bool, minVal_bool, h0]
  rcases le_total (0 : ℝ) (g true) with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonneg h]
    ring
  · rw [max_eq_left h, min_eq_right h, abs_of_nonpos h]
    ring

/-! ## The construction -/

variable {m : ℕ}

/-- The tip of world `w`. -/
noncomputable def tip (m : ℕ) (w : Fin m) : Fin m → ℝ :=
  fun i => if i = w then -((m : ℝ) - 2) else 1

/-- The support: the origin and the tip. -/
noncomputable def supp (m : ℕ) (w : Fin m) : Bool → Fin m → ℝ :=
  fun b => if b then tip m w else fun _ => 0

/-- The components are the coordinates. -/
noncomputable def comp (m : ℕ) (w : Fin m) : Fin m → Bool → ℝ :=
  fun i b => supp m w b i

/-- **The tip's coordinates sum to one.** -/
theorem sum_tip (m : ℕ) (w : Fin m) : ∑ i, tip m w i = 1 := by
  classical
  have h : ∀ i : Fin m, tip m w i = 1 + (if i = w then -((m : ℝ) - 2) - 1 else 0) := by
    intro i
    unfold tip
    by_cases hi : i = w
    · rw [if_pos hi, if_pos hi]; ring
    · rw [if_neg hi, if_neg hi]; ring
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Finset.sum_ite_eq' Finset.univ w (fun _ => -((m : ℝ) - 2) - 1),
      if_pos (Finset.mem_univ w)]
  ring

/-- The discarded sum when the single answer `j` is retained. -/
theorem sumComponent_compl (m : ℕ) (w j : Fin m) :
    sumComponent ({j} : Finset (Fin m))ᶜ (comp m w) true = 1 - tip m w j := by
  classical
  have hval : ∀ i : Fin m, comp m w i true = tip m w i := fun _ => rfl
  have hsplit : ∑ i ∈ ({j} : Finset (Fin m))ᶜ, tip m w i
      = (∑ i, tip m w i) - tip m w j := by
    rw [← Finset.sum_compl_add_sum ({j} : Finset (Fin m)) (tip m w), Finset.sum_singleton]
    ring
  unfold sumComponent
  rw [Finset.sum_congr rfl (fun i _ => hval i), hsplit, sum_tip m w]

theorem sumComponent_compl_zero (m : ℕ) (w j : Fin m) :
    sumComponent ({j} : Finset (Fin m))ᶜ (comp m w) false = 0 := by
  classical
  have hval : ∀ i : Fin m, comp m w i false = 0 := fun _ => rfl
  unfold sumComponent
  rw [Finset.sum_congr rfl (fun i _ => hval i), Finset.sum_const_zero]

/-- **The compression loss of retaining one answer, computed.** -/
theorem selectedRadius_eq (m : ℕ) (w j : Fin m) :
    selectedRadius (comp m w) {j} = |1 - tip m w j| / 2 := by
  unfold selectedRadius supportOsc
  rw [osc_bool_of_zero _ (sumComponent_compl_zero m w j), sumComponent_compl m w j]

/-- **Retaining the world's own index is the expensive one.** -/
theorem selectedRadius_self (m : ℕ) (hm : 2 ≤ m) (w : Fin m) :
    selectedRadius (comp m w) {w} = ((m : ℝ) - 1) / 2 := by
  rw [selectedRadius_eq m w w]
  have ht : tip m w w = -((m : ℝ) - 2) := by unfold tip; rw [if_pos rfl]
  rw [ht]
  have hm' : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - -((m : ℝ) - 2))]
  ring

/-- **Retaining any other answer costs nothing.** -/
theorem selectedRadius_other (m : ℕ) (w j : Fin m) (hj : j ≠ w) :
    selectedRadius (comp m w) {j} = 0 := by
  rw [selectedRadius_eq m w j]
  have ht : tip m w j = 1 := by unfold tip; rw [if_neg hj]
  rw [ht]
  norm_num

/-- **The safe sets are exactly "everything but the world's own index"**, at any tolerance
below `(m-1)/2`: pairwise intersecting when `m >= 3`, with empty total intersection.  This
is the geometry `LeanPaperBSafeOrderV1`'s law consumes, now derived from the loss. -/
theorem safe_iff_ne (m : ℕ) (hm : 2 ≤ m) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : ε < ((m : ℝ) - 1) / 2) (w j : Fin m) :
    selectedRadius (comp m w) {j} ≤ ε ↔ j ≠ w := by
  constructor
  · intro h hjw
    subst hjw
    rw [selectedRadius_self m hm j] at h
    linarith
  · intro hj
    rw [selectedRadius_other m w j hj]
    exact hε0

/-! ## Audit -/

#print axioms maxVal_bool
#print axioms osc_bool_of_zero
#print axioms sum_tip
#print axioms selectedRadius_eq
#print axioms selectedRadius_self
#print axioms selectedRadius_other
#print axioms safe_iff_ne

end CIGAMF.P13.PaperBTip
