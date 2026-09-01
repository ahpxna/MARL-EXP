import Mathlib
import «LeanD6CycleDual»

/-!
# Anchor-cycle spanning: dual/annihilator formulation

This module proves only the span statement requested by the handoff.  In a
finite function space, equality of the annihilator of all anchored D6 cycles
with the coordinate-additive subspace is the dual characterization of cycle
spanning.  No coefficient norm or sharp fixed-anchor atomic-cost bound is
claimed; that stronger statement has an exact counterexample.
-/

namespace CIGAMF.P13.D6AnchorCycleSpanning

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ResidualCentering
open CIGAMF.P13.D6CycleDual

variable {U : Type*} [Fintype U] [Nonempty U]

def AnchorCycleAnnihilator {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (anchor : Fin (n + 1) → U) : Prop :=
  ∀ (i : Fin (n + 1)) (x : Fin (n + 1) → U),
    cycleFunctional i x anchor F = 0

def AnchorCoordinateAdditive {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (anchor : Fin (n + 1) → U) : Prop :=
  ∀ x,
    F x = (∑ i : Fin (n + 1), F (Function.update anchor i (x i))) -
      (n : ℝ) * F anchor

/- If a world annihilates every mixed-difference cycle at one fixed anchor,
the P12 hybrid telescope reconstructs it from one-coordinate anchor sections.
This is the constructive direction of the span theorem. -/
theorem anchor_cycles_annihilator_implies_coordinate_additive {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (anchor : Fin (n + 1) → U)
    (hcycle : AnchorCycleAnnihilator F anchor) :
    AnchorCoordinateAdditive F anchor := by
  intro x
  have hsum :
      (∑ i : Fin n,
        mixedDifference F i.castSucc (hybrid x anchor i.val) anchor) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← cycleFunctional_eq_mixedDifference]
    exact hcycle i.castSucc (hybrid x anchor i.val)
  have hid := pointwise_residual_eq_sum_mixed F x anchor
  rw [hsum] at hid
  linarith

/- Conversely, the anchored coordinate-additive reconstruction has zero D6
cycle functional.  This proves equality of the two annihilator classes. -/
theorem coordinate_additive_implies_anchor_cycles_annihilator {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (anchor : Fin (n + 1) → U)
    (hadd : AnchorCoordinateAdditive F anchor) :
    AnchorCycleAnnihilator F anchor := by
  let g : Fin (n + 1) → U → ℝ := fun i u ↦
    F (Function.update anchor i u)
  have hfun : F = fun x ↦ (∑ i, g i (x i)) - (n : ℝ) * F anchor := by
    funext x
    exact hadd x
  intro i x
  rw [hfun]
  simpa [sub_eq_add_neg] using
    cycle_annihilates_coordinate_additive g (-((n : ℝ) * F anchor)) i x anchor

theorem AnchorCycleSpanning_dual {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (anchor : Fin (n + 1) → U) :
    AnchorCycleAnnihilator F anchor ↔ AnchorCoordinateAdditive F anchor := by
  constructor
  · exact anchor_cycles_annihilator_implies_coordinate_additive F anchor
  · exact coordinate_additive_implies_anchor_cycles_annihilator F anchor

end CIGAMF.P13.D6AnchorCycleSpanning
