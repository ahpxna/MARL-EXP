import Mathlib
import «LeanSupportGeometryV4»

/-! Deterministic functional transfer and gauge-invariant extrema stability. -/

namespace CIGAMF.V4.FunctionalBoundary

open scoped BigOperators
open SupportGeometry

variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

noncomputable def capacity (Q : A → ℝ) : ℝ := osc Q
noncomputable def direction (w Q : A → ℝ) : ℝ := Finset.univ.sum (fun a => w a * Q a)

theorem A1_capacity_transfer
    (Qhat Q : A → ℝ) (eps : ℝ)
    (hSup : ∀ a, |Qhat a - Q a| ≤ eps) :
    |capacity Qhat - capacity Q| ≤ 2 * eps := by
  let err : A → ℝ := fun a => Qhat a - Q a
  have herr : osc err ≤ 2 * eps := by
    have hmax : maxVal err ≤ eps := by
      apply maxVal_le
      intro a
      exact (abs_le.mp (hSup a)).2
    have hmin : -eps ≤ minVal err := by
      apply le_minVal
      intro a
      exact (abs_le.mp (hSup a)).1
    simp only [osc]
    linarith
  have hfun : (fun a => Q a + err a) = Qhat := by
    funext a
    simp [err]
  have hosc := osc_add_deviation Q err
  rw [hfun] at hosc
  simpa [capacity] using hosc.trans herr

theorem A1_direction_transfer
    (w Qhat Q : A → ℝ) (eps : ℝ)
    (hSup : ∀ a, |Qhat a - Q a| ≤ eps) (heps : 0 ≤ eps) :
    |direction w Qhat - direction w Q| ≤
      (Finset.univ.sum fun a => |w a|) * eps := by
  have heq : direction w Qhat - direction w Q =
      Finset.univ.sum (fun a => w a * (Qhat a - Q a)) := by
    simp only [direction, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [heq]
  calc
    |Finset.univ.sum (fun a => w a * (Qhat a - Q a))| ≤
        Finset.univ.sum (fun a => |w a * (Qhat a - Q a)|) :=
      Finset.abs_sum_le_sum_abs _ _
    _ = Finset.univ.sum (fun a => |w a| * |Qhat a - Q a|) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul]
    _ ≤ Finset.univ.sum (fun a => |w a| * eps) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hSup a) (abs_nonneg _)
    _ = (Finset.univ.sum fun a => |w a|) * eps := by
      rw [Finset.sum_mul]

noncomputable def gaugeError (Qhat Q : A → ℝ) : ℝ := osc (fun a => Qhat a - Q a) / 2

theorem GQ_exact_gauge_identity (Qhat Q : A → ℝ) :
    IsCompressionRadius (fun a => Qhat a - Q a) (gaugeError Qhat Q) := by
  exact BH1_exact_radius (fun a => Qhat a - Q a)

noncomputable def lambdaC (delta g : ℝ) : Option ℝ :=
  if g = 0 then none else some (delta / g)

theorem lambdaC_undefined_at_zero (delta : ℝ) : lambdaC delta 0 = none := by
  simp [lambdaC]

def PreservesExtrema (Qhat Q : A → ℝ) (aPlus aMinus : A) : Prop :=
  (∀ a ≠ aPlus, Qhat a < Qhat aPlus) ∧
  (∀ a ≠ aMinus, Qhat aMinus < Qhat a)

theorem A2_gauge_extrema_stability
    (Qhat Q : A → ℝ) (aPlus aMinus : A) (g delta : ℝ)
    (hGapPos : 0 < g)
    (hMaxGap : ∀ a ≠ aPlus, g ≤ Q aPlus - Q a)
    (hMinGap : ∀ a ≠ aMinus, g ≤ Q a - Q aMinus)
    (hGauge : ∃ c : ℝ, ∀ a, |(Qhat a - Q a) - c| ≤ delta)
    (hPhase : delta < g / 2) :
    PreservesExtrema Qhat Q aPlus aMinus := by
  rcases hGauge with ⟨c, hc⟩
  constructor
  · intro a ha
    have hEa := (abs_le.mp (hc a)).2
    have hEp := (abs_le.mp (hc aPlus)).1
    have hg := hMaxGap a ha
    linarith
  · intro a ha
    have hEa := (abs_le.mp (hc a)).1
    have hEm := (abs_le.mp (hc aMinus)).2
    have hg := hMinGap a ha
    linarith

theorem A3_stable_extrema_linearization
    (Qhat Q : A → ℝ) (aPlus aMinus : A)
    (hQmax : maxVal Q = Q aPlus) (hQmin : minVal Q = Q aMinus)
    (hHmax : maxVal Qhat = Qhat aPlus) (hHmin : minVal Qhat = Qhat aMinus) :
    capacity Qhat - capacity Q =
      (Qhat aPlus - Q aPlus) - (Qhat aMinus - Q aMinus) := by
  simp only [capacity, osc, hQmax, hQmin, hHmax, hHmin]
  ring

theorem A4_simultaneous_interval_implies_capacity_interval
    (lower Q upper : A → ℝ)
    (hband : ∀ a, lower a ≤ Q a ∧ Q a ≤ upper a) :
    maxVal lower - minVal upper ≤ capacity Q ∧
      capacity Q ≤ maxVal upper - minVal lower := by
  rcases exists_eq_maxVal lower with ⟨al, hal⟩
  rcases exists_eq_minVal upper with ⟨au, hau⟩
  have hmaxLower : maxVal lower ≤ maxVal Q := by
    rw [← hal]
    exact le_trans (hband al).1 (le_maxVal Q al)
  have hminUpper : minVal Q ≤ minVal upper := by
    rw [← hau]
    exact le_trans (minVal_le Q au) (hband au).2
  have hmaxUpper : maxVal Q ≤ maxVal upper := by
    apply maxVal_le
    intro a
    exact le_trans (hband a).2 (le_maxVal upper a)
  have hminLower : minVal lower ≤ minVal Q := by
    apply le_minVal
    intro a
    exact le_trans (minVal_le lower a) (hband a).1
  simp only [capacity, osc]
  constructor <;> linarith

theorem A4_exact_null_range_pathology
    (Qhat Q : A → ℝ) (c : ℝ)
    (hNull : ∀ a, Q a = c) (a b : A) (hDifferent : Qhat a ≠ Qhat b) :
    capacity Q = 0 ∧ 0 < capacity Qhat := by
  constructor
  · have hfun : Q = fun _ => c := funext hNull
    rw [hfun]
    let a0 : A := Classical.choice (inferInstance : Nonempty A)
    have hmax : maxVal (fun _ : A => c) = c := by
      apply le_antisymm
      · exact maxVal_le _ (fun _ => le_rfl)
      · exact le_maxVal (fun _ : A => c) a0
    have hmin : minVal (fun _ : A => c) = c := by
      apply le_antisymm
      · exact minVal_le (fun _ : A => c) a0
      · exact le_minVal _ (fun _ => le_rfl)
    simp [capacity, osc, hmax, hmin]
  · rcases lt_or_gt_of_ne hDifferent with hab | hba
    · have hmax := le_maxVal Qhat b
      have hmin := minVal_le Qhat a
      simp only [capacity, osc]
      linarith
    · have hmax := le_maxVal Qhat a
      have hmin := minVal_le Qhat b
      simp only [capacity, osc]
      linarith

end CIGAMF.V4.FunctionalBoundary
