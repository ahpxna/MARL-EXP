import «LeanSupportPhysicalQueryContractV1»

/-! Multiple actual support tips. Safe singleton decisions are exactly the
missing tips; physical membership exposes one tip at a time. -/
namespace CIGAMF.P13.SupportMultiTipGeometry
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportUnboundedObstruction
open CIGAMF.P13.SupportPhysicalQueryContract (tip_ne_zero tip_injective)
noncomputable section
variable {m : ℕ}

def support (W : Finset (Fin m)) : Finset (Fin m → ℝ) := insert 0 (W.image tip)

abbrev Points (W : Finset (Fin m)) := Option {w // w ∈ W}

def point (W : Finset (Fin m)) : Points W → (Fin m → ℝ)
  | none => 0
  | some w => tip w.val

def components (W : Finset (Fin m)) (j : Fin m) (x : Points W) : ℝ := point W x j

lemma point_image (W : Finset (Fin m)) :
    (univ.image (point W)) = support W := by
  ext x
  simp only [mem_image,mem_univ,true_and,support,mem_insert]
  constructor
  · rintro ⟨a,rfl⟩
    cases a with
    | none => exact Or.inl rfl
    | some w => exact Or.inr ⟨w.val,w.property,rfl⟩
  · rintro (rfl | ⟨w,hw,rfl⟩)
    · exact ⟨none,rfl⟩
    · exact ⟨some ⟨w,hw⟩,rfl⟩

theorem physical_membership_iff (hm : 2 ≤ m) (W : Finset (Fin m)) (a : Fin m) :
    tip a ∈ support W ↔ a ∈ W := by
  simp only [support,mem_insert,mem_image]
  constructor
  · rintro (h | ⟨w,hw,he⟩)
    · exact False.elim (tip_ne_zero a h)
    · exact tip_injective hm he ▸ hw
  · intro h; exact Or.inr ⟨a,h,rfl⟩

lemma residual_none (W : Finset (Fin m)) (j : Fin m) :
    sumComponent ({j}ᶜ) (components W) none = 0 := by
  simp [sumComponent,components,point]

lemma residual_some (W : Finset (Fin m)) (j : Fin m) (w : {w // w ∈ W}) :
    sumComponent ({j}ᶜ) (components W) (some w) =
      if j=w.val then (m:ℝ)-1 else 0 := by
  have he : ({j}ᶜ : Finset (Fin m)) = univ.erase j := by ext i; simp [eq_comm]
  simp only [sumComponent,components,point]
  rw [he,sum_erase_eq_sub (mem_univ j),total_tip]
  unfold tip
  ring

theorem radius_formula (hm : 2 ≤ m) (W : Finset (Fin m)) (j : Fin m) :
    selectedRadius (components W) {j} = if j ∈ W then ((m:ℝ)-1)/2 else 0 := by
  let f := sumComponent ({j}ᶜ) (components W)
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hn : minVal f = 0 := by
    apply le_antisymm
    · simpa [f,residual_none] using minVal_le f none
    · apply le_minVal
      intro x
      cases x with
      | none => simp [f,residual_none]
      | some w => simp only [f,residual_some]; split_ifs <;> linarith
  have hx : maxVal f = if j ∈ W then (m:ℝ)-1 else 0 := by
    apply le_antisymm
    · apply maxVal_le
      intro x
      cases x with
      | none => simp only [f,residual_none]; split_ifs <;> linarith
      | some w =>
        simp only [f,residual_some]
        by_cases h : j=w.val
        · subst j; simp [w.property]
        · simp only [h,↓reduceIte]; split_ifs <;> linarith
    · by_cases h : j ∈ W
      · simpa [f,residual_some,h] using le_maxVal f (some ⟨j,h⟩)
      · simpa [f,residual_none,h] using le_maxVal f none
  change (maxVal f-minVal f)/2 = _
  rw [hx,hn]
  split_ifs <;> ring

theorem zero_radius_iff (hm : 2 ≤ m) (W : Finset (Fin m)) (j : Fin m) :
    selectedRadius (components W) {j}=0 ↔ j ∉ W := by
  rw [radius_formula hm]
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  by_cases h : j ∈ W <;> simp [h] <;> linarith

/-- In the dense family with exactly one missing tip, every world has one
safe choice, and two different worlds already have incompatible decisions. -/
theorem dense_unique_safe (hm : 2 ≤ m) (w j : Fin m) :
    selectedRadius (components (univ.erase w)) {j}=0 ↔ j=w := by
  rw [zero_radius_iff hm]
  simp

#print axioms point_image
#print axioms physical_membership_iff
#print axioms radius_formula
#print axioms zero_radius_iff
#print axioms dense_unique_safe
end
end CIGAMF.P13.SupportMultiTipGeometry
