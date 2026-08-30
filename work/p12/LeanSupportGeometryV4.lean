import Mathlib

/-!
# CIG-AMF active support geometry (v4)

`Ω` is represented by a finite nonempty type.  Its inhabitants are feasible
joint actions; no empirical/observed-row interpretation is assumed.
-/

namespace CIGAMF.V4.SupportGeometry

open scoped BigOperators

section FiniteExtrema

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

noncomputable def maxVal (f : Ω → ℝ) : ℝ :=
  (Finset.univ.image f).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

noncomputable def minVal (f : Ω → ℝ) : ℝ :=
  (Finset.univ.image f).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)

noncomputable def osc (f : Ω → ℝ) : ℝ := maxVal f - minVal f

theorem le_maxVal (f : Ω → ℝ) (a : Ω) : f a ≤ maxVal f := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

theorem minVal_le (f : Ω → ℝ) (a : Ω) : minVal f ≤ f a := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)

theorem maxVal_le (f : Ω → ℝ) {x : ℝ} (h : ∀ a, f a ≤ x) : maxVal f ≤ x := by
  classical
  apply (Finset.max'_le_iff _ _).2
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨a, -, rfl⟩
  exact h a

theorem le_minVal (f : Ω → ℝ) {x : ℝ} (h : ∀ a, x ≤ f a) : x ≤ minVal f := by
  classical
  apply (Finset.le_min'_iff _ _).2
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨a, -, rfl⟩
  exact h a

theorem exists_eq_maxVal (f : Ω → ℝ) : ∃ a, f a = maxVal f := by
  classical
  have hm := Finset.max'_mem (Finset.univ.image f)
    (Finset.image_nonempty.mpr Finset.univ_nonempty)
  rcases Finset.mem_image.mp hm with ⟨a, -, ha⟩
  exact ⟨a, ha⟩

theorem exists_eq_minVal (f : Ω → ℝ) : ∃ a, f a = minVal f := by
  classical
  have hm := Finset.min'_mem (Finset.univ.image f)
    (Finset.image_nonempty.mpr Finset.univ_nonempty)
  rcases Finset.mem_image.mp hm with ⟨a, -, ha⟩
  exact ⟨a, ha⟩

theorem osc_nonneg (f : Ω → ℝ) : 0 ≤ osc f := by
  rcases exists_eq_maxVal f with ⟨a, ha⟩
  have h := minVal_le f a
  rw [ha] at h
  exact sub_nonneg.mpr h

theorem maxVal_const_sub (c : ℝ) (f : Ω → ℝ) :
    maxVal (fun a => c - f a) = c - minVal f := by
  apply le_antisymm
  · apply maxVal_le
    intro a
    linarith [minVal_le f a]
  · rcases exists_eq_minVal f with ⟨a, ha⟩
    simpa [ha] using le_maxVal (fun a => c - f a) a

theorem minVal_const_sub (c : ℝ) (f : Ω → ℝ) :
    minVal (fun a => c - f a) = c - maxVal f := by
  apply le_antisymm
  · rcases exists_eq_maxVal f with ⟨a, ha⟩
    simpa [ha] using minVal_le (fun a => c - f a) a
  · apply le_minVal
    intro a
    linarith [le_maxVal f a]

theorem osc_neg (f : Ω → ℝ) : osc (fun a => -f a) = osc f := by
  rw [show (fun a => -f a) = (fun a => 0 - f a) by funext a; ring]
  simp only [osc, maxVal_const_sub, minVal_const_sub]
  ring

theorem osc_add_le (f g : Ω → ℝ) :
    osc (fun a => f a + g a) ≤ osc f + osc g := by
  have hmax : maxVal (fun a => f a + g a) ≤ maxVal f + maxVal g := by
    apply maxVal_le
    intro a
    exact add_le_add (le_maxVal f a) (le_maxVal g a)
  have hmin : minVal f + minVal g ≤ minVal (fun a => f a + g a) := by
    apply le_minVal
    intro a
    exact add_le_add (minVal_le f a) (minVal_le g a)
  simp only [osc]
  linarith

theorem osc_add_deviation (f g : Ω → ℝ) :
    |osc (fun a => f a + g a) - osc f| ≤ osc g := by
  apply abs_le.mpr
  constructor
  · have h := osc_add_le (fun a => f a + g a) (fun a => -g a)
    have heq : (fun a => f a + g a + -g a) = f := by funext a; ring
    rw [heq, osc_neg] at h
    linarith
  · linarith [osc_add_le f g]

theorem osc_add_const (f : Ω → ℝ) (c : ℝ) :
    osc (fun a => f a + c) = osc f := by
  have h := osc_add_deviation f (fun _ => c)
  have hz : osc (fun _ : Ω => c) = 0 := by
    let a0 : Ω := Classical.choice (inferInstance : Nonempty Ω)
    have hmax : maxVal (fun _ : Ω => c) = c := by
      apply le_antisymm
      · exact maxVal_le _ (fun _ => le_rfl)
      · exact le_maxVal (fun _ : Ω => c) a0
    have hmin : minVal (fun _ : Ω => c) = c := by
      apply le_antisymm
      · exact minVal_le (fun _ : Ω => c) a0
      · exact le_minVal _ (fun _ => le_rfl)
    simp [osc, hmax, hmin]
  rw [hz] at h
  have hz0 : |osc (fun a => f a + c) - osc f| = 0 :=
    le_antisymm h (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp hz0)

theorem osc_of_sum_gauge_bounded
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Finset ι) (fhat f : ι → Ω → ℝ) (delta : ι → ℝ)
    (hdelta : ∀ j ∈ T, 0 ≤ delta j)
    (hgauge : ∀ j ∈ T, ∃ c : ℝ, ∀ a, |fhat j a - f j a - c| ≤ delta j) :
    |osc (fun a => T.sum (fun j => fhat j a)) -
        osc (fun a => T.sum (fun j => f j a))| ≤ 2 * T.sum delta := by
  let shifts : ι → ℝ := fun j =>
    if hj : j ∈ T then Classical.choose (hgauge j hj) else 0
  have hshifts : ∀ j, j ∈ T → ∀ a, |fhat j a - f j a - shifts j| ≤ delta j := by
    intro j hj a
    simp [shifts, hj]
    exact Classical.choose_spec (hgauge j hj) a
  let totalShift : ℝ := T.sum shifts
  let centeredErr : Ω → ℝ := fun a =>
    T.sum (fun j => (fhat j a - f j a - shifts j))
  have hcenter : ∀ a, |centeredErr a| ≤ T.sum delta := by
    intro a
    calc
      |centeredErr a| ≤ T.sum (fun j => |fhat j a - f j a - shifts j|) :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ T.sum delta := by
        apply Finset.sum_le_sum
        intro j hj
        exact hshifts j hj a
  have hosc : osc centeredErr ≤ 2 * T.sum delta := by
    have hmax : maxVal centeredErr ≤ T.sum delta :=
      maxVal_le _ (fun a => (abs_le.mp (hcenter a)).2)
    have hmin : -(T.sum delta) ≤ minVal centeredErr :=
      le_minVal _ (fun a => (abs_le.mp (hcenter a)).1)
    simp only [osc]
    linarith
  have hdecomp : (fun a => T.sum (fun j => fhat j a)) =
      (fun a => T.sum (fun j => f j a) + centeredErr a + totalShift) := by
    funext a
    simp only [centeredErr, totalShift, Finset.sum_sub_distrib]
    ring
  rw [hdecomp]
  have hdev := osc_add_deviation (fun a => T.sum (fun j => f j a))
    (fun a => centeredErr a + totalShift)
  have hoscShift : osc (fun a => centeredErr a + totalShift) = osc centeredErr :=
    osc_add_const centeredErr totalShift
  rw [hoscShift] at hdev
  have hbound :
      |osc (fun a => T.sum (fun j => f j a) + (centeredErr a + totalShift)) -
          osc (fun a => T.sum (fun j => f j a))| ≤ 2 * T.sum delta :=
    le_trans hdev hosc
  simpa [add_assoc] using hbound

theorem G2_fixed_subset_radius_stability_from_components
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Finset ι) (fhat f : ι → Ω → ℝ) (delta : ι → ℝ)
    (hdelta : ∀ j ∈ T, 0 ≤ delta j)
    (hgauge : ∀ j ∈ T, ∃ c : ℝ, ∀ a, |fhat j a - f j a - c| ≤ delta j) :
    |osc (fun a => T.sum (fun j => fhat j a)) / 2 -
        osc (fun a => T.sum (fun j => f j a)) / 2| ≤ T.sum delta := by
  have h := osc_of_sum_gauge_bounded T fhat f delta hdelta hgauge
  rw [show osc (fun a => T.sum (fun j => fhat j a)) / 2 -
      osc (fun a => T.sum (fun j => f j a)) / 2 =
      (osc (fun a => T.sum (fun j => fhat j a)) -
        osc (fun a => T.sum (fun j => f j a))) / 2 by ring]
  rw [abs_div]
  norm_num
  have hsum_nonneg : 0 ≤ T.sum delta :=
    Finset.sum_nonneg (fun j hj => hdelta j hj)
  calc
    |osc (fun a => T.sum (fun j => fhat j a)) -
        osc (fun a => T.sum (fun j => f j a))| / 2
        ≤ (2 * T.sum delta) / 2 := by exact div_le_div_of_nonneg_right h (by norm_num)
    _ = T.sum delta := by ring

theorem G2_fixed_subset_radius_stability
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Finset ι) (fhat f : ι → Ω → ℝ) (delta : ι → ℝ)
    (hdelta : ∀ j ∈ T, 0 ≤ delta j)
    (hgauge : ∀ j ∈ T, ∃ c : ℝ, ∀ a, |fhat j a - f j a - c| ≤ delta j) :
    |osc (fun a => T.sum (fun j => fhat j a)) / 2 -
        osc (fun a => T.sum (fun j => f j a)) / 2| ≤ T.sum delta :=
  G2_fixed_subset_radius_stability_from_components T fhat f delta hdelta hgauge

/- `IsCompressionRadius f r` is the exact infimum contract without hiding an
attainment assumption in a real-valued `sInf`: `r` is achievable and no
achievable uniform scalar error can be smaller. -/
def IsCompressionRadius (f : Ω → ℝ) (r : ℝ) : Prop :=
  (∃ c : ℝ, ∀ a, |f a - c| ≤ r) ∧
  (∀ c s : ℝ, (∀ a, |f a - c| ≤ s) → r ≤ s)

theorem BH1_exact_radius (f : Ω → ℝ) :
    IsCompressionRadius f (osc f / 2) := by
  constructor
  · refine ⟨(maxVal f + minVal f) / 2, ?_⟩
    intro a
    apply abs_le.mpr
    simp only [osc]
    constructor <;> linarith [minVal_le f a, le_maxVal f a]
  · intro c s hs
    rcases exists_eq_maxVal f with ⟨amax, hmax⟩
    rcases exists_eq_minVal f with ⟨amin, hmin⟩
    have h₁ := (abs_le.mp (hs amax)).2
    have h₂ := (abs_le.mp (hs amin)).1
    rw [hmax] at h₁
    rw [hmin] at h₂
    simp only [osc]
    linarith

end FiniteExtrema

section NestedSupports

variable {A : Type*} [DecidableEq A]

noncomputable def maxOn (support : Finset A) (hne : support.Nonempty)
    (f : A → ℝ) : ℝ :=
  (support.image f).max' (Finset.image_nonempty.mpr hne)

noncomputable def minOn (support : Finset A) (hne : support.Nonempty)
    (f : A → ℝ) : ℝ :=
  (support.image f).min' (Finset.image_nonempty.mpr hne)

noncomputable def oscOn (support : Finset A) (hne : support.Nonempty)
    (f : A → ℝ) : ℝ := maxOn support hne f - minOn support hne f

noncomputable def radiusOn (support : Finset A) (hne : support.Nonempty)
    (f : A → ℝ) : ℝ := oscOn support hne f / 2

theorem maxOn_mono (inner outer : Finset A)
    (hi : inner.Nonempty) (ho : outer.Nonempty) (hsub : inner ⊆ outer)
    (f : A → ℝ) : maxOn inner hi f ≤ maxOn outer ho f := by
  classical
  apply (Finset.max'_le_iff _ _).2
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨a, hsub ha, rfl⟩)

theorem minOn_antitone (inner outer : Finset A)
    (hi : inner.Nonempty) (ho : outer.Nonempty) (hsub : inner ⊆ outer)
    (f : A → ℝ) : minOn outer ho f ≤ minOn inner hi f := by
  classical
  apply (Finset.le_min'_iff _ _).2
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨a, hsub ha, rfl⟩)

theorem oscOn_mono (inner outer : Finset A)
    (hi : inner.Nonempty) (ho : outer.Nonempty) (hsub : inner ⊆ outer)
    (f : A → ℝ) : oscOn inner hi f ≤ oscOn outer ho f := by
  have hmax := maxOn_mono inner outer hi ho hsub f
  have hmin := minOn_antitone inner outer hi ho hsub f
  simp only [oscOn]
  linarith

theorem H1_radius_monotonicity (inner truth outer : Finset A)
    (hi : inner.Nonempty) (ht : truth.Nonempty) (ho : outer.Nonempty)
    (hit : inner ⊆ truth) (hto : truth ⊆ outer) (f : A → ℝ) :
    radiusOn inner hi f ≤ radiusOn truth ht f ∧
      radiusOn truth ht f ≤ radiusOn outer ho f := by
  constructor
  · unfold radiusOn
    linarith [oscOn_mono inner truth hi ht hit f]
  · unfold radiusOn
    linarith [oscOn_mono truth outer ht ho hto f]

theorem H4_projected_span_bracket (inner truth outer : Finset A)
    (hi : inner.Nonempty) (ht : truth.Nonempty) (ho : outer.Nonempty)
    (hit : inner ⊆ truth) (hto : truth ⊆ outer) (f : A → ℝ) :
    oscOn inner hi f ≤ oscOn truth ht f ∧
      oscOn truth ht f ≤ oscOn outer ho f := by
  exact ⟨oscOn_mono inner truth hi ht hit f,
    oscOn_mono truth outer ht ho hto f⟩

end NestedSupports

section Components

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]

noncomputable def sumComponent (T : Finset ι) (f : ι → Ω → ℝ) (a : Ω) : ℝ :=
  T.sum (fun j => f j a)

noncomputable def componentMax (f : ι → Ω → ℝ) (j : ι) : ℝ := maxVal (f j)
noncomputable def componentMin (f : ι → Ω → ℝ) (j : ι) : ℝ := minVal (f j)
noncomputable def componentSpan (f : ι → Ω → ℝ) (j : ι) : ℝ :=
  componentMax f j - componentMin f j
noncomputable def modularSpan (T : Finset ι) (f : ι → Ω → ℝ) : ℝ :=
  T.sum (fun j => componentSpan f j)
noncomputable def supportOsc (T : Finset ι) (f : ι → Ω → ℝ) : ℝ :=
  osc (sumComponent T f)
noncomputable def deficit (T : Finset ι) (f : ι → Ω → ℝ) : ℝ :=
  modularSpan T f - supportOsc T f
noncomputable def ePlus (T : Finset ι) (f : ι → Ω → ℝ) : ℝ :=
  minVal (fun a => T.sum (fun j => componentMax f j - f j a))
noncomputable def eMinus (T : Finset ι) (f : ι → Ω → ℝ) : ℝ :=
  minVal (fun a => T.sum (fun j => f j a - componentMin f j))

theorem sumComponent_le_modularMax (T : Finset ι) (f : ι → Ω → ℝ) (a : Ω) :
    sumComponent T f a ≤ T.sum (fun j => componentMax f j) := by
  unfold sumComponent componentMax
  exact Finset.sum_le_sum fun j _ => le_maxVal (f j) a

theorem modularMin_le_sumComponent (T : Finset ι) (f : ι → Ω → ℝ) (a : Ω) :
    T.sum (fun j => componentMin f j) ≤ sumComponent T f a := by
  unfold sumComponent componentMin
  exact Finset.sum_le_sum fun j _ => minVal_le (f j) a

theorem BH2_supportOsc_le_modularSpan (T : Finset ι) (f : ι → Ω → ℝ) :
    supportOsc T f ≤ modularSpan T f := by
  have hmax : maxVal (sumComponent T f) ≤ T.sum (fun j => componentMax f j) :=
    maxVal_le _ (sumComponent_le_modularMax T f)
  have hmin : T.sum (fun j => componentMin f j) ≤ minVal (sumComponent T f) :=
    le_minVal _ (modularMin_le_sumComponent T f)
  simp only [supportOsc, modularSpan, componentSpan, osc]
  rw [Finset.sum_sub_distrib]
  linarith

theorem ePlus_eq (T : Finset ι) (f : ι → Ω → ℝ) :
    ePlus T f = T.sum (fun j => componentMax f j) - maxVal (sumComponent T f) := by
  have hfun : (fun a => T.sum (fun j => componentMax f j - f j a)) =
      (fun a => T.sum (fun j => componentMax f j) - sumComponent T f a) := by
    funext a
    simp only [sumComponent, Finset.sum_sub_distrib]
  rw [ePlus, hfun, minVal_const_sub]

theorem eMinus_eq (T : Finset ι) (f : ι → Ω → ℝ) :
    eMinus T f = minVal (sumComponent T f) - T.sum (fun j => componentMin f j) := by
  have hfun : (fun a => T.sum (fun j => f j a - componentMin f j)) =
      (fun a => sumComponent T f a - T.sum (fun j => componentMin f j)) := by
    funext a
    simp only [sumComponent, Finset.sum_sub_distrib]
  rw [eMinus, hfun]
  apply le_antisymm
  · rcases exists_eq_minVal (sumComponent T f) with ⟨a, ha⟩
    simpa [ha] using minVal_le
      (fun a => sumComponent T f a - T.sum (fun j => componentMin f j)) a
  · apply le_minVal
    intro a
    linarith [minVal_le (sumComponent T f) a]

theorem BH3_exact_support_deficit_identity (T : Finset ι) (f : ι → Ω → ℝ) :
    deficit T f = ePlus T f + eMinus T f ∧ 0 ≤ deficit T f := by
  rw [ePlus_eq, eMinus_eq]
  constructor
  · simp only [deficit, modularSpan, supportOsc, componentSpan, osc]
    rw [Finset.sum_sub_distrib]
    ring
  · exact sub_nonneg.mpr (BH2_supportOsc_le_modularSpan T f)

theorem BH4_coextremizable_exactness
    (T : Finset ι) (f : ι → Ω → ℝ)
    (amax amin : Ω)
    (hmax : ∀ j ∈ T, f j amax = componentMax f j)
    (hmin : ∀ j ∈ T, f j amin = componentMin f j) :
    supportOsc T f = modularSpan T f := by
  apply le_antisymm (BH2_supportOsc_le_modularSpan T f)
  have h₁ : sumComponent T f amax = T.sum (fun j => componentMax f j) := by
    unfold sumComponent
    apply Finset.sum_congr rfl
    intro j hj
    exact hmax j hj
  have h₂ : sumComponent T f amin = T.sum (fun j => componentMin f j) := by
    unfold sumComponent
    apply Finset.sum_congr rfl
    intro j hj
    exact hmin j hj
  have hm := le_maxVal (sumComponent T f) amax
  have hn := minVal_le (sumComponent T f) amin
  rw [h₁] at hm
  rw [h₂] at hn
  simp only [supportOsc, modularSpan, componentSpan, osc]
  rw [Finset.sum_sub_distrib]
  linarith

end Components

section CardinalityTopC

variable {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
variable [Fintype ι] [DecidableEq ι]

def IsTopKByScore (C : ι → ℝ) (selected : Finset ι) (k : ℕ) : Prop :=
  selected.card = k ∧
    ∀ candidate : Finset ι, candidate.card = k → candidate.sum C ≤ selected.sum C

def cardinalityFamily (q : ℕ) : Finset (Finset ι) :=
  Finset.univ.filter (fun S => S.card = q)

noncomputable def finiteMaxOn
    (family : Finset (Finset ι)) (value : Finset ι → ℝ) : ℝ :=
  if h : family.Nonempty then
    (family.image value).max' (Finset.image_nonempty.mpr h)
  else 0

theorem finiteMaxOn_dominates
    (family : Finset (Finset ι)) (value : Finset ι → ℝ)
    (S : Finset ι) (hS : S ∈ family) :
    value S ≤ finiteMaxOn family value := by
  have hne : family.Nonempty := ⟨S, hS⟩
  simp only [finiteMaxOn, dif_pos hne]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨S, hS, rfl⟩)

noncomputable def zetaDefFinite (f : ι → Ω → ℝ) (k : ℕ) : ℝ :=
  finiteMaxOn (cardinalityFamily (ι := ι) (Fintype.card ι - k))
    (fun T => deficit T f)

theorem zetaDefFinite_dominates
    (f : ι → Ω → ℝ) (k : ℕ) (T : Finset ι)
    (hcard : T.card = Fintype.card ι - k) :
    deficit T f ≤ zetaDefFinite f k := by
  unfold zetaDefFinite
  exact finiteMaxOn_dominates
    (cardinalityFamily (ι := ι) (Fintype.card ι - k))
    (fun T => deficit T f) T (by simp [cardinalityFamily, hcard])

noncomputable def deltaKFinite (delta : ι → ℝ) (k : ℕ) : ℝ :=
  finiteMaxOn (cardinalityFamily (ι := ι) k) (fun S => Sᶜ.sum delta)

theorem deltaKFinite_dominates
    (delta : ι → ℝ) (k : ℕ) (S : Finset ι) (hcard : S.card = k) :
    Sᶜ.sum delta ≤ deltaKFinite delta k := by
  unfold deltaKFinite
  exact finiteMaxOn_dominates (cardinalityFamily (ι := ι) k)
    (fun S => Sᶜ.sum delta) S (by simp [cardinalityFamily, hcard])

theorem exists_topKByScore
    (C : ι → ℝ) (k : ℕ)
    (hne : (cardinalityFamily (ι := ι) k).Nonempty) :
    ∃ S : Finset ι, IsTopKByScore C S k := by
  rcases Finset.exists_max_image (cardinalityFamily (ι := ι) k)
    (fun S => S.sum C) hne with
    ⟨S, hS, hmax⟩
  refine ⟨S, ?_, ?_⟩
  · simpa [cardinalityFamily] using hS
  · intro candidate hcard
    exact hmax candidate (by simpa [cardinalityFamily, hcard])

noncomputable def canonicalTopK (C : ι → ℝ) (k : ℕ) : Finset ι :=
  if h : (cardinalityFamily (ι := ι) k).Nonempty then
    Classical.choose (exists_topKByScore C k h)
  else ∅

theorem canonicalTopK_spec
    (C : ι → ℝ) (k : ℕ)
    (hne : (cardinalityFamily (ι := ι) k).Nonempty) :
    IsTopKByScore C (canonicalTopK C k) k := by
  simp only [canonicalTopK, dif_pos hne]
  exact Classical.choose_spec (exists_topKByScore C k hne)

theorem canonicalTopK_upperOptimal
    (U : ι → ℝ) (k : ℕ)
    (hne : (cardinalityFamily (ι := ι) k).Nonempty)
    (candidate : Finset ι) (hcard : candidate.card = k) :
    candidate.sum U ≤ (canonicalTopK U k).sum U := by
  exact (canonicalTopK_spec U k hne).2 candidate hcard

noncomputable def omittedModularScore (C : ι → ℝ) (selected : Finset ι) : ℝ :=
  selectedᶜ.sum C

noncomputable def selectedRadius (f : ι → Ω → ℝ) (selected : Finset ι) : ℝ :=
  supportOsc selectedᶜ f / 2

theorem topK_implies_omitted_modular_min
    (C : ι → ℝ) (selected candidate : Finset ι) (k : ℕ)
    (hTop : IsTopKByScore C selected k) (hCandidate : candidate.card = k) :
    omittedModularScore C selected ≤ omittedModularScore C candidate := by
  have hs := selected.sum_add_sum_compl C
  have hc := candidate.sum_add_sum_compl C
  have hscore := hTop.2 candidate hCandidate
  unfold omittedModularScore
  linarith

theorem omitted_modular_difference_eq_retained_score_loss
    (C : ι → ℝ) (trueTop selected : Finset ι) :
    omittedModularScore C selected - omittedModularScore C trueTop =
      trueTop.sum C - selected.sum C := by
  have hs := selected.sum_add_sum_compl C
  have ht := trueTop.sum_add_sum_compl C
  unfold omittedModularScore
  linarith

theorem BH5_cardinality_topC_support_deficit
    (f : ι → Ω → ℝ) (trueTop optimum : Finset ι) (k : ℕ) (zetaDef : ℝ)
    (hTop : IsTopKByScore (componentSpan f) trueTop k)
    (hOptCard : optimum.card = k)
    (hZeta : deficit optimumᶜ f ≤ zetaDef) :
    selectedRadius f trueTop - selectedRadius f optimum ≤ zetaDef / 2 := by
  have hM := topK_implies_omitted_modular_min (componentSpan f)
    trueTop optimum k hTop hOptCard
  have hd0 := (BH3_exact_support_deficit_identity trueTopᶜ f).2
  have hTopRadius : supportOsc trueTopᶜ f =
      modularSpan trueTopᶜ f - deficit trueTopᶜ f := by
    unfold deficit
    ring
  have hOptRadius : supportOsc optimumᶜ f =
      modularSpan optimumᶜ f - deficit optimumᶜ f := by
    unfold deficit
    ring
  change supportOsc trueTopᶜ f / 2 - supportOsc optimumᶜ f / 2 ≤ zetaDef / 2
  change modularSpan trueTopᶜ f ≤ modularSpan optimumᶜ f at hM
  rw [hTopRadius, hOptRadius]
  linarith

theorem BH5_selected_score_to_geometry
    (f : ι → Ω → ℝ) (trueTop selected optimum : Finset ι)
    (k : ℕ) (zetaDef : ℝ)
    (hTop : IsTopKByScore (componentSpan f) trueTop k)
    (hSelectedCard : selected.card = k) (hOptCard : optimum.card = k)
    (hZeta : deficit optimumᶜ f ≤ zetaDef) :
    selectedRadius f selected - selectedRadius f optimum ≤
      (trueTop.sum (componentSpan f) - selected.sum (componentSpan f)) / 2 +
        zetaDef / 2 := by
  have hMTopOpt := topK_implies_omitted_modular_min (componentSpan f)
    trueTop optimum k hTop hOptCard
  have hMSelected :
      omittedModularScore (componentSpan f) selected -
        omittedModularScore (componentSpan f) trueTop =
      trueTop.sum (componentSpan f) - selected.sum (componentSpan f) :=
    omitted_modular_difference_eq_retained_score_loss _ _ _
  have hdSelected := (BH3_exact_support_deficit_identity selectedᶜ f).2
  have hdOpt := hZeta
  have hSelRadius : supportOsc selectedᶜ f =
      modularSpan selectedᶜ f - deficit selectedᶜ f := by
    unfold deficit
    ring
  have hOptRadius : supportOsc optimumᶜ f =
      modularSpan optimumᶜ f - deficit optimumᶜ f := by
    unfold deficit
    ring
  change supportOsc selectedᶜ f / 2 - supportOsc optimumᶜ f / 2 ≤
    (trueTop.sum (componentSpan f) - selected.sum (componentSpan f)) / 2 +
      zetaDef / 2
  change modularSpan trueTopᶜ f ≤ modularSpan optimumᶜ f at hMTopOpt
  change modularSpan selectedᶜ f - modularSpan trueTopᶜ f =
    trueTop.sum (componentSpan f) - selected.sum (componentSpan f) at hMSelected
  rw [hSelRadius, hOptRadius]
  linarith

end CardinalityTopC

section LPRelaxation

variable {ι : Type*}

def IntegerFeasible (base : (ι → ℝ) → Prop) (x : ι → ℝ) : Prop :=
  base x ∧ ∀ j, x j = 0 ∨ x j = 1

def RelaxedFeasible (base : (ι → ℝ) → Prop) (x : ι → ℝ) : Prop :=
  base x ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1

theorem integer_feasible_subset_relaxed
    (base : (ι → ℝ) → Prop) (x : ι → ℝ)
    (hx : IntegerFeasible base x) : RelaxedFeasible base x := by
  refine ⟨hx.1, ?_⟩
  intro j
  rcases hx.2 j with h0 | h1
  · rw [h0]
    norm_num
  · rw [h1]
    norm_num

theorem BH7_relaxation_is_lower_bound
    {X : Type*} (integer relaxed : X → Prop) (objective : X → ℝ)
    (integerOpt relaxedOpt : X)
    (hsubset : ∀ x, integer x → relaxed x)
    (hint : integer integerOpt)
    (hrelaxedMin : ∀ x, relaxed x → objective relaxedOpt ≤ objective x) :
    objective relaxedOpt ≤ objective integerOpt := by
  exact hrelaxedMin integerOpt (hsubset integerOpt hint)

end LPRelaxation

section InstantiatedSupportBrackets

variable {A X : Type*} [DecidableEq A]

theorem H2_support_regret_bracket_instantiated
    (inner truth outer : Finset A)
    (hi : inner.Nonempty) (ht : truth.Nonempty) (ho : outer.Nonempty)
    (hit : inner ⊆ truth) (hto : truth ⊆ outer)
    (residual : X → A → ℝ) (selected innerOpt trueOpt : X)
    (hinnerOpt : ∀ x, radiusOn inner hi (residual innerOpt) ≤
      radiusOn inner hi (residual x)) :
    radiusOn truth ht (residual selected) - radiusOn truth ht (residual trueOpt) ≤
      radiusOn outer ho (residual selected) - radiusOn inner hi (residual innerOpt) := by
  have hupper := (H1_radius_monotonicity inner truth outer hi ht ho hit hto
    (residual selected)).2
  have hmid := (H1_radius_monotonicity inner truth outer hi ht ho hit hto
    (residual trueOpt)).1
  have hopt := hinnerOpt trueOpt
  linarith

theorem H3_inner_lp_regret_bracket_instantiated
    (inner truth outer : Finset A)
    (hi : inner.Nonempty) (ht : truth.Nonempty) (ho : outer.Nonempty)
    (hit : inner ⊆ truth) (hto : truth ⊆ outer)
    (residual : X → A → ℝ) (selected innerOpt trueOpt : X) (lb : ℝ)
    (hinnerOpt : ∀ x, radiusOn inner hi (residual innerOpt) ≤
      radiusOn inner hi (residual x))
    (hLB : lb ≤ radiusOn inner hi (residual innerOpt)) :
    radiusOn truth ht (residual selected) - radiusOn truth ht (residual trueOpt) ≤
      radiusOn outer ho (residual selected) - lb := by
  have h := H2_support_regret_bracket_instantiated inner truth outer hi ht ho hit hto
    residual selected innerOpt trueOpt hinnerOpt
  linarith

end InstantiatedSupportBrackets

section Certificates

variable {X : Type*}

theorem BH5_one_sided_zeta_half
    (M d : X → ℝ) (top opt : X) (zeta : ℝ)
    (hTop : M top ≤ M opt)
    (hd0 : ∀ x, 0 ≤ d x) (hdz : ∀ x, d x ≤ zeta) :
    (M top - d top) / 2 - (M opt - d opt) / 2 ≤ zeta / 2 := by
  linarith [hd0 top, hdz opt]

theorem BH6_global_subset_independent_certificate
    (M d : X → ℝ) (top opt : X) (E : ℝ)
    (hTop : M top ≤ M opt)
    (hd0 : ∀ x, 0 ≤ d x) (hdE : ∀ x, d x ≤ E) :
    (M top - d top) / 2 - (M opt - d opt) / 2 ≤ E / 2 := by
  exact BH5_one_sided_zeta_half M d top opt E hTop hd0 hdE

theorem BH7_lp_lower_bound_implication
    (candidate optimum lb : ℝ) (hLB : lb ≤ optimum) :
    candidate - optimum ≤ candidate - lb := by linarith

theorem G2_fixed_subset_radius_stability_historical_assumed
    (rHat r delta : ℝ) (h : |rHat - r| ≤ delta) :
    |rHat - r| ≤ delta := h

theorem G3_optimization_transfer
    {X : Type*} (r rHat : X → ℝ) (selected optimum : X) (Delta : ℝ)
    (hclose : ∀ x, |rHat x - r x| ≤ Delta)
    (hselected : rHat selected ≤ rHat optimum) :
    r selected - r optimum ≤ 2 * Delta := by
  have hs₁ := (abs_le.mp (hclose selected)).1
  have hs₂ := (abs_le.mp (hclose optimum)).2
  linarith

theorem H2_support_regret_bracket
    (rTrueSelected rTrueStar rPlusSelected rMinusStar : ℝ)
    (hupper : rTrueSelected ≤ rPlusSelected)
    (hlower : rMinusStar ≤ rTrueStar) :
    rTrueSelected - rTrueStar ≤ rPlusSelected - rMinusStar := by linarith

theorem H3_inner_lp_regret_bracket
    (rTrueSelected rTrueStar rPlusSelected lbMinus rMinusStar : ℝ)
    (hupper : rTrueSelected ≤ rPlusSelected)
    (hmono : rMinusStar ≤ rTrueStar)
    (hLB : lbMinus ≤ rMinusStar) :
    rTrueSelected - rTrueStar ≤ rPlusSelected - lbMinus := by linarith

theorem H4_midpoint_span_error
    (cMinus c cPlus : ℝ) (hlo : cMinus ≤ c) (hhi : c ≤ cPlus) :
    |c - (cPlus + cMinus) / 2| ≤ (cPlus - cMinus) / 2 := by
  apply abs_le.mpr
  constructor <;> linarith

theorem CERT_deterministic_from_two_branches
    (lossSelected lossStar eHalf lpGap Delta eta : ℝ)
    (hE : lossSelected - lossStar ≤ eHalf + 2 * Delta + 2 * eta)
    (hLP : lossSelected - lossStar ≤ lpGap + 2 * Delta + 2 * eta) :
    lossSelected - lossStar ≤ min eHalf lpGap + 2 * Delta + 2 * eta := by
  have hE' : lossSelected - lossStar - (2 * Delta + 2 * eta) ≤ eHalf := by linarith
  have hLP' : lossSelected - lossStar - (2 * Delta + 2 * eta) ≤ lpGap := by linarith
  have hmin : lossSelected - lossStar - (2 * Delta + 2 * eta) ≤ min eHalf lpGap :=
    le_min hE' hLP'
  linarith

theorem CERT_instantiated_end_to_end
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι]
    (fhat f : ι → Ω → ℝ) (delta : ι → ℝ)
    (L : Finset ι → ℝ)
    (selected estimatedOpt trueOpt : Finset ι)
    (k : ℕ) (Ehat lbHat Delta eta : ℝ)
    (hDeltaNonneg : ∀ j, 0 ≤ delta j)
    (hGauge : ∀ j, ∃ c : ℝ, ∀ a, |fhat j a - f j a - c| ≤ delta j)
    (hDeltaK : ∀ S : Finset ι, S.card = k → Sᶜ.sum delta ≤ Delta)
    (hSelectedTop : IsTopKByScore (componentSpan fhat) selected k)
    (hEstimatedOptCard : estimatedOpt.card = k)
    (hTrueOptCard : trueOpt.card = k)
    (hEstimatedOpt : ∀ S : Finset ι, S.card = k →
      selectedRadius fhat estimatedOpt ≤ selectedRadius fhat S)
    (hTrueOpt : ∀ S : Finset ι, S.card = k →
      selectedRadius f trueOpt ≤ selectedRadius f S)
    (hEhat : deficit estimatedOptᶜ fhat ≤ Ehat)
    (hLB : lbHat ≤ selectedRadius fhat estimatedOpt)
    (hDownstream : ∀ S : Finset ι, S.card = k →
      |L S - selectedRadius f S| ≤ eta) :
    L selected - L trueOpt ≤
      min (Ehat / 2) (selectedRadius fhat selected - lbHat) +
        2 * Delta + 2 * eta := by
  have hclose : ∀ S : Finset ι, S.card = k →
      |selectedRadius fhat S - selectedRadius f S| ≤ Delta := by
    intro S hcard
    have hfixed := G2_fixed_subset_radius_stability Sᶜ fhat f delta
      (fun j hj => hDeltaNonneg j)
      (fun j hj => hGauge j)
    exact le_trans hfixed (hDeltaK S hcard)
  have hEstimatedOrder := hEstimatedOpt trueOpt hTrueOptCard
  have hSelectedClose := hclose selected hSelectedTop.1
  have hTrueClose := hclose trueOpt hTrueOptCard
  have hRadiusTransfer :
      selectedRadius f selected - selectedRadius f trueOpt ≤
        selectedRadius fhat selected - selectedRadius fhat estimatedOpt +
          2 * Delta := by
    have hs := (abs_le.mp hSelectedClose).1
    have ht := (abs_le.mp hTrueClose).2
    linarith
  have hLossSelected := (abs_le.mp (hDownstream selected hSelectedTop.1)).2
  have hLossOpt := (abs_le.mp (hDownstream trueOpt hTrueOptCard)).1
  have hLossTransfer : L selected - L trueOpt ≤
      selectedRadius fhat selected - selectedRadius fhat estimatedOpt +
        2 * Delta + 2 * eta := by
    linarith
  have hEBranchGeometry := BH5_cardinality_topC_support_deficit fhat selected
    estimatedOpt k Ehat hSelectedTop hEstimatedOptCard hEhat
  have hEBranch : L selected - L trueOpt ≤ Ehat / 2 + 2 * Delta + 2 * eta := by
    linarith
  have hLPGap : selectedRadius fhat selected - selectedRadius fhat estimatedOpt ≤
      selectedRadius fhat selected - lbHat := by
    linarith
  have hLPBranch : L selected - L trueOpt ≤
      (selectedRadius fhat selected - lbHat) + 2 * Delta + 2 * eta := by
    linarith
  exact CERT_deterministic_from_two_branches (L selected) (L trueOpt)
    (Ehat / 2) (selectedRadius fhat selected - lbHat) Delta eta hEBranch hLPBranch

theorem CERT_with_finite_Delta
    {Ω ι : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype ι] [DecidableEq ι]
    (fhat f : ι → Ω → ℝ) (delta : ι → ℝ)
    (L : Finset ι → ℝ)
    (selected estimatedOpt trueOpt : Finset ι)
    (k : ℕ) (Ehat lbHat eta : ℝ)
    (hDeltaNonneg : ∀ j, 0 ≤ delta j)
    (hGauge : ∀ j, ∃ c : ℝ, ∀ a, |fhat j a - f j a - c| ≤ delta j)
    (hSelectedTop : IsTopKByScore (componentSpan fhat) selected k)
    (hEstimatedOptCard : estimatedOpt.card = k)
    (hTrueOptCard : trueOpt.card = k)
    (hEstimatedOpt : ∀ S : Finset ι, S.card = k →
      selectedRadius fhat estimatedOpt ≤ selectedRadius fhat S)
    (hTrueOpt : ∀ S : Finset ι, S.card = k →
      selectedRadius f trueOpt ≤ selectedRadius f S)
    (hEhat : deficit estimatedOptᶜ fhat ≤ Ehat)
    (hLB : lbHat ≤ selectedRadius fhat estimatedOpt)
    (hDownstream : ∀ S : Finset ι, S.card = k →
      |L S - selectedRadius f S| ≤ eta) :
    L selected - L trueOpt ≤
      min (Ehat / 2) (selectedRadius fhat selected - lbHat) +
        2 * deltaKFinite delta k + 2 * eta := by
  apply CERT_instantiated_end_to_end fhat f delta L selected estimatedOpt trueOpt
    k Ehat lbHat (deltaKFinite delta k) eta hDeltaNonneg hGauge
  · intro S hcard
    exact deltaKFinite_dominates delta k S hcard
  · exact hSelectedTop
  · exact hEstimatedOptCard
  · exact hTrueOptCard
  · exact hEstimatedOpt
  · exact hTrueOpt
  · exact hEhat
  · exact hLB
  · exact hDownstream

end Certificates

end CIGAMF.V4.SupportGeometry
