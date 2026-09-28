import «LeanSupportThreeWorldWitnessV1»

/-! Arbitrarily high-order fibre obstruction in actual two-point support geometry.
All worlds share coordinate projections as primitives and differ only in the tip
of their support. Nevertheless one membership query suffices for a safe decision:
obstruction order alone is not acquisition complexity. -/
namespace CIGAMF.P13.SupportUnboundedObstruction
open scoped BigOperators
open Finset
open CIGAMF.V4.SupportGeometry CIGAMF.V6.FunctionalRanking
noncomputable section
variable {m : ℕ}

def tip (w j : Fin m) : ℝ := 1 - if j=w then (m:ℝ)-1 else 0

def supportPoint (w : Fin m) (a : Fin 2) : Fin m → ℝ :=
  fun j => if a=0 then 0 else tip w j

def worldF (w j : Fin m) (a : Fin 2) : ℝ := supportPoint w a j

theorem total_tip (w : Fin m) : (∑ j, tip w j) = 1 := by
  simp [tip,sum_sub_distrib]

theorem radius_formula (hm : 2 ≤ m) (w j : Fin m) :
    selectedRadius (worldF w) {j} = if j=w then ((m:ℝ)-1)/2 else 0 := by
  have hzero : sumComponent ({j}ᶜ) (worldF w) 0 = 0 := by
    simp [sumComponent,worldF,supportPoint]
  have he : ({j}ᶜ : Finset (Fin m)) = univ.erase j := by ext i; simp [eq_comm]
  have hone : sumComponent ({j}ᶜ) (worldF w) 1 = if j=w then (m:ℝ)-1 else 0 := by
    simp only [sumComponent,worldF,supportPoint,show (1:Fin 2) ≠ 0 by decide,↓reduceIte]
    rw [he,sum_erase_eq_sub (mem_univ j),total_tip]
    unfold tip
    ring
  have hpos : (0:ℝ) ≤ if j=w then (m:ℝ)-1 else 0 := by
    have h : (2:ℝ) ≤ m := by exact_mod_cast hm
    split_ifs <;> linarith
  unfold selectedRadius supportOsc osc
  rw [maxVal_fin2,minVal_fin2,hzero,hone,max_eq_right hpos,min_eq_left hpos]
  split_ifs <;> ring

def normalizedRadius (w j : Fin m) : ℝ :=
  selectedRadius (worldF w) {j} / (((2:ℝ)*m-3)/2)

theorem normalized_bad_gt_half (hm : 2 ≤ m) (w : Fin m) :
    1/2 < normalizedRadius w w := by
  rw [normalizedRadius,radius_formula hm]
  simp only [↓reduceIte]
  have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
  apply (lt_div_iff₀ (by linarith : (0:ℝ) < (2*(m:ℝ)-3)/2)).mpr
  linarith

theorem normalized_good (hm : 2 ≤ m) (w j : Fin m) (h : j ≠ w) :
    normalizedRadius w j = 0 := by simp [normalizedRadius,radius_formula hm,h]

/-- Every proper subfamily has a common exact decision. -/
theorem every_proper_subfamily_safe (hm : 2 ≤ m) (W : Finset (Fin m)) (hW : W ≠ univ) :
    ∃ j : Fin m, ∀ w ∈ W, selectedRadius (worldF w) {j} = 0 := by
  have hex : ∃ j : Fin m, j ∉ W := by
    by_contra h
    push_neg at h
    apply hW
    ext j; simp [h j]
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,?_⟩
  intro w hw
  have h : j ≠ w := by intro h; subst j; exact hj hw
  simp [radius_formula hm,h]

/-- Failure persists for every epsilon <= 1/2 after radius normalization. -/
theorem full_fibre_not_half_safe (hm : 2 ≤ m) :
    ¬ ∃ j : Fin m, ∀ w : Fin m, normalizedRadius w j ≤ 1/2 := by
  rintro ⟨j,hj⟩
  exact (not_le.mpr (normalized_bad_gt_half hm j)) (hj j)

/-- Query whether the tip of world a is in the actual support. Under this
finite world family this is equivalent to w=a, and no hidden label is returned. -/
def answer (a w : Fin m) : Bool := decide (w=a)

def choose (a b : Fin m) (observed : Bool) : Fin m := if observed then b else a

theorem one_query_sound (hm : 2 ≤ m) (a b : Fin m) (hab : a ≠ b) (w : Fin m) :
    selectedRadius (worldF w) {choose a b (answer a w)} = 0 := by
  by_cases h : w=a
  · subst w
    simp [choose,answer,radius_formula hm,Ne.symm hab]
  · simp [choose,answer,h,radius_formula hm,Ne.symm h]

#print axioms radius_formula
#print axioms normalized_bad_gt_half
#print axioms every_proper_subfamily_safe
#print axioms full_fibre_not_half_safe
#print axioms one_query_sound
end
end CIGAMF.P13.SupportUnboundedObstruction
