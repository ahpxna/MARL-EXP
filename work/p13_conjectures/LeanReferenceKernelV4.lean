import Mathlib
import «LeanSupportGeometryV4»
import «LeanReferenceFidelityV4»

/-! Finite joint conditional kernels, their induced responses, and a total-variation
bound.  This file keeps the probability-kernel semantics separate from the
linear-weight RF1 theorem. -/

namespace CIGAMF.V4

open scoped BigOperators
open SupportGeometry

namespace JointKernel

variable {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

def Valid (κ : A → B → ℝ) : Prop :=
  (∀ a b, 0 ≤ κ a b) ∧ (∀ a, ∑ b, κ a b = 1)

def expectation (κ : A → B → ℝ) (H : B → ℝ) (a : A) : ℝ :=
  ∑ b, κ a b * H b

def response (κ : A → B → ℝ) (F : A → B → ℝ) (a : A) : ℝ :=
  expectation κ (F a) a

theorem expectation_decomposition
    (κ : A → B → ℝ) (hκ : Valid κ)
    (b0 : ℝ) (primitive : A → ℝ) (H : B → ℝ) (a : A) :
    response κ (fun a z => b0 + primitive a + H z) a =
      b0 + primitive a + expectation κ H a := by
  unfold response expectation
  calc
    Finset.univ.sum (fun x => κ a x * (b0 + primitive a + H x)) =
        Finset.univ.sum (fun x => κ a x * b0) +
          Finset.univ.sum (fun x => κ a x * primitive a) +
          Finset.univ.sum (fun x => κ a x * H x) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = b0 + primitive a + Finset.univ.sum (fun x => κ a x * H x) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          rw [hκ.2 a]
          ring

noncomputable def tv (P Q : B → ℝ) : ℝ := (∑ b, |P b - Q b|) / 2

theorem tv_nonneg (P Q : B → ℝ) : 0 ≤ tv P Q := by
  unfold tv
  positivity

theorem expectation_diff_le_tv_osc
    (P Q : B → ℝ) (H : B → ℝ)
    (hP : ∑ b, P b = 1) (hQ : ∑ b, Q b = 1) :
    |(∑ b, P b * H b) - ∑ b, Q b * H b| ≤ tv P Q * osc H := by
  let c : ℝ := (maxVal H + minVal H) / 2
  have hcenter : ∀ b, |H b - c| ≤ osc H / 2 := by
    intro b
    apply abs_le.mpr
    simp only [c, osc]
    constructor <;> linarith [minVal_le H b, le_maxVal H b]
  have hsumdiff : ∑ b, (P b - Q b) = 0 := by
    rw [Finset.sum_sub_distrib, hP, hQ, sub_self]
  have hrewrite :
      (∑ b, P b * H b) - ∑ b, Q b * H b =
        ∑ b, (P b - Q b) * (H b - c) := by
    calc
      (∑ b, P b * H b) - ∑ b, Q b * H b =
          ∑ b, (P b * H b - Q b * H b) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ b, ((P b - Q b) * (H b - c) + (P b - Q b) * c) := by
            apply Finset.sum_congr rfl
            intro b hb
            ring
      _ = (∑ b, (P b - Q b) * (H b - c)) +
            (∑ b, (P b - Q b)) * c := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = ∑ b, (P b - Q b) * (H b - c) := by rw [hsumdiff, zero_mul, add_zero]
  rw [hrewrite]
  calc
    |∑ b, (P b - Q b) * (H b - c)| ≤
        ∑ b, |(P b - Q b) * (H b - c)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b, |P b - Q b| * |H b - c| := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [abs_mul]
    _ ≤ ∑ b, |P b - Q b| * (osc H / 2) := by
          apply Finset.sum_le_sum
          intro b hb
          exact mul_le_mul_of_nonneg_left (hcenter b) (abs_nonneg _)
    _ = (∑ b, |P b - Q b|) * (osc H / 2) := by
          rw [Finset.sum_mul]
    _ = tv P Q * osc H := by
          unfold tv
          ring

noncomputable def tau (κ : A → B → ℝ) : ℝ :=
  maxVal (fun p : A × A => tv (κ p.1) (κ p.2))

theorem tau_nonneg (κ : A → B → ℝ) : 0 ≤ tau κ := by
  let a0 : A := Classical.choice (inferInstance : Nonempty A)
  exact le_trans (tv_nonneg (κ a0) (κ a0))
    (le_maxVal (fun p : A × A => tv (κ p.1) (κ p.2)) (a0, a0))

theorem chi_le_osc_mul_tau
    (κ : A → B → ℝ) (hκ : Valid κ) (H : B → ℝ) :
    osc (fun a => expectation κ H a) ≤ osc H * tau κ := by
  let m : A → ℝ := fun a => expectation κ H a
  rcases exists_eq_maxVal m with ⟨amax, hmax⟩
  rcases exists_eq_minVal m with ⟨amin, hmin⟩
  have hrow := expectation_diff_le_tv_osc (κ amax) (κ amin) H
    (hκ.2 amax) (hκ.2 amin)
  change |m amax - m amin| ≤ tv (κ amax) (κ amin) * osc H at hrow
  have htau : tv (κ amax) (κ amin) ≤ tau κ :=
    le_maxVal (fun p : A × A => tv (κ p.1) (κ p.2)) (amax, amin)
  have hmul : tv (κ amax) (κ amin) * osc H ≤ tau κ * osc H :=
    mul_le_mul_of_nonneg_right htau (osc_nonneg H)
  have hdiff : 0 ≤ m amax - m amin := by
    rw [hmax, hmin]
    exact osc_nonneg m
  have hmain : m amax - m amin ≤ tv (κ amax) (κ amin) * osc H := by
    rw [← abs_of_nonneg hdiff]
    exact hrow
  have hoscEq : osc m = m amax - m amin := by
    unfold osc
    rw [← hmax, ← hmin]
  rw [hoscEq]
  exact le_trans hmain (by simpa [mul_comm] using hmul)

theorem chi_le_component_sum_tau
    (κ : A → B → ℝ) (hκ : Valid κ) (H : B → ℝ) (componentSum : ℝ)
    (hspan : osc H ≤ componentSum) :
    osc (fun a => expectation κ H a) ≤ componentSum * tau κ := by
  have hchi := chi_le_osc_mul_tau κ hκ H
  have hmul : osc H * tau κ ≤ componentSum * tau κ :=
    mul_le_mul_of_nonneg_right hspan (tau_nonneg κ)
  exact le_trans hchi hmul

/-! A finite joint kernel induces coordinate marginals.  RF1 itself is the
linear-weight theorem; the corollary below applies it to these induced
marginals, while `Valid` supplies non-negativity and row normalization of the
joint law. -/
noncomputable def coordinateMarginal {L U : Type*}
    [Fintype L] [Fintype U] [DecidableEq L] [DecidableEq U]
    (κ : A → (L → U) → ℝ) (a : A) (l : L) (u : U) : ℝ :=
  ∑ z, if z l = u then κ a z else 0

theorem coordinateMarginal_nonneg {L U : Type*}
    [Fintype L] [Fintype U] [Nonempty U] [DecidableEq L] [DecidableEq U]
    (κ : A → (L → U) → ℝ) (hκ : Valid κ)
    (a : A) (l : L) (u : U) : 0 ≤ coordinateMarginal κ a l u := by
  unfold coordinateMarginal
  apply Finset.sum_nonneg
  intro z hz
  split_ifs
  · exact hκ.1 a z
  · norm_num

theorem rf1_joint_kernel_bridge {L U : Type*}
    [Fintype L] [Fintype U] [Nonempty U] [DecidableEq L] [DecidableEq U]
    (κ : A → (L → U) → ℝ) (hκ : Valid κ)
    (hInv : ∀ l u a a', coordinateMarginal κ a l u = coordinateMarginal κ a' l u) :
    ReferenceFidelity.UniversalAdditiveConstancy
      (fun a l u => coordinateMarginal κ a l u) := by
  apply (ReferenceFidelity.RF1_universal_fidelity_iff_marginal_invariance
    (fun a l u => coordinateMarginal κ a l u)).2
  exact hInv

end JointKernel

end CIGAMF.V4
