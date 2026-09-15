import «LeanD6FiniteGridAllocationV1»
import «LeanQuadraticIntervalMinimumV1»

/-! The finite solver score needs no optimization oracle over a continuum.
For each alternative label, a quadratic is minimized exactly on [0,1]; a finite
comparison then selects the worst label. This is an exact-real algorithm. -/
namespace CIGAMF.P13.D6FiniteNuisanceEvaluation
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationRiskBridge CIGAMF.P13.D6AllocationTrackingStability
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6MovingNuisanceRegret
open CIGAMF.P13.FiniteGridSolver
noncomputable section
variable {n : ℕ}

def labels (A : Finset (I n)) (j : I n) : Finset (Finset (I n)) :=
  univ.filter (fun B => B ≠ A ∧ B.card=A.card ∧ j ∉ B)

lemma labels_mem (A B : Finset (I n)) (j : I n) :
    B ∈ labels A j ↔ B ≠ A ∧ B.card=A.card ∧ j ∉ B := by simp [labels]

lemma labels_nonempty (A : Finset (I n)) (j : I n)
    (halt : ∃ B nu,Admissible A B j nu) : (labels A j).Nonempty := by
  obtain ⟨B,nu,h⟩ := halt
  exact ⟨B,(labels_mem A B j).mpr ⟨h.1,h.2.1,h.2.2.1⟩⟩

def curvature (B : Finset (I n)) (j : I n) (E : Finset (Measurement n))
    (w : Measurement n → ℝ) : ℝ := ∑ e ∈ E,w e*(meanSlope B j e)^2

def crossTerm (A B : Finset (I n)) (j : I n) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : ℝ :=
  ∑ e ∈ E,w e*(actualMean A j mu e-meanOffset B j e)*meanSlope B j e

def constantTerm (A B : Finset (I n)) (j : I n) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : ℝ :=
  ∑ e ∈ E,w e*(actualMean A j mu e-meanOffset B j e)^2

def nuisance (A B : Finset (I n)) (j : I n) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : ℝ :=
  QuadraticIntervalMinimum.minimizer (crossTerm A B j mu E w) (curvature B j E w)

def labelValue (A B : Finset (I n)) (j : I n) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : ℝ :=
  QuadraticIntervalMinimum.value (constantTerm A B j mu E w)
    (crossTerm A B j mu E w) (curvature B j E w) (nuisance A B j mu E w)

lemma information_quadratic (A B : Finset (I n)) (j : I n) (hjB : j ∉ B)
    (q mu nu : ℝ) (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) :
    (∑ e ∈ E,w e*information A B j mu nu e)=
      QuadraticIntervalMinimum.value (constantTerm A B j mu E w)
        (crossTerm A B j mu E w) (curvature B j E w) nu := by
  unfold QuadraticIntervalMinimum.value constantTerm crossTerm curvature
  simp_rw [information_eq_mean]
  simp only [mul_sum,sum_mul,← sum_sub_distrib,← sum_add_distrib,Finset.sum_div]
  apply sum_congr rfl
  intro e he
  rw [actual_mean_affine B j hjB q nu e (hl e he)]
  ring

lemma labelValue_lower (A B : Finset (I n)) (j : I n) (hjB : j ∉ B)
    (q mu nu : ℝ) (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e)
    (hnu0 : 0 ≤ nu) (hnu1 : nu ≤ 1) :
    labelValue A B j mu E w ≤ ∑ e ∈ E,w e*information A B j mu nu e := by
  rw [information_quadratic A B j hjB q mu nu E w hl]
  exact QuadraticIntervalMinimum.minimum _ _ _
    (sum_nonneg (fun e he => mul_nonneg (hw e he) (sq_nonneg _))) nu hnu0 hnu1

def worstLabel (A : Finset (I n)) (j : I n)
    (halt : ∃ B nu,Admissible A B j nu) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : labels A j :=
  letI := (labels_nonempty A j halt).to_subtype
  argmax (fun B : labels A j => -labelValue A B.val j mu E w)

def finiteValue (A : Finset (I n)) (j : I n)
    (halt : ∃ B nu,Admissible A B j nu) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : ℝ :=
  labelValue A (worstLabel A j halt mu E w).val j mu E w

/-- The exact sInf equals a finite evaluation using arithmetic and comparisons. -/
theorem allocationValue_eq_finite (A : Finset (I n)) (j : I n)
    (halt : ∃ B nu,Admissible A B j nu) (q mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) :
    allocationValue A j mu E w=finiteValue A j halt mu E w := by
  letI := (labels_nonempty A j halt).to_subtype
  let B := worstLabel A j halt mu E w
  have hB := (labels_mem A B.val j).mp B.property
  have hnu := QuadraticIntervalMinimum.minimizer_mem (crossTerm A B.val j mu E w) (curvature B.val j E w)
  apply le_antisymm
  · have h := allocationValue_le_actual A B.val j mu (nuisance A B.val j mu E w) E w hw
      ⟨hB.1,hB.2.1,hB.2.2,hnu.1,hnu.2⟩
    rw [information_quadratic A B.val j hB.2.2 q mu _ E w hl] at h
    exact h
  · apply le_csInf (value_nonempty A j halt mu E w)
    rintro z ⟨B',nu,hB',rfl⟩
    have hmem : B' ∈ labels A j := (labels_mem A B' j).mpr ⟨hB'.1,hB'.2.1,hB'.2.2.1⟩
    have hmax := argmax_spec (fun B : labels A j => -labelValue A B.val j mu E w) ⟨B',hmem⟩
    have hlo := labelValue_lower A B' j hB'.2.2.1 q mu nu E w hl hw hB'.2.2.2.1 hB'.2.2.2.2
    change -labelValue A B' j mu E w ≤ -finiteValue A j halt mu E w at hmax
    linarith

#print axioms information_quadratic
#print axioms labelValue_lower
#print axioms allocationValue_eq_finite
end
end CIGAMF.P13.D6FiniteNuisanceEvaluation
