import Mathlib

/-!
# Obstructions: when a decision can be made without identifying the world.

## WHY THIS MODULE EXISTS

The corpus has a WITNESS separating the cost of deciding from the cost of identifying.  A
witness is one pair of numbers; what is missing is the law that says, for a whole family,
which resolution is enough.  This file supplies the combinatorial half of that law.

Fix an eps and let `safe F` be the set of decisions that are eps-correct in world `F`.  A
set of worlds `H` is an OBSTRUCTION when no single decision is safe in all of them.  The
point of the definition is that identifying the world is sufficient but wildly wasteful:
a learner only has to separate worlds far enough that no obstruction survives inside a
class it can no longer split.

That is the content of `classes_resolve_iff`: grouping worlds into classes, every class
has a common safe answer if and only if no obstruction lies inside a class.  Combined
with a notion of resolution that refines as the order rises, this is what makes

    r_safe = max over minimal obstructions H of  min over queries q of
             min over distinct F, G in H of  r_q(F, G)

a candidate quantity only when pairwise orders come from a common coefficient signature:
F and G agree through order r iff every query has separation order greater than r.
This module does not define those signatures, their orders, or prove this max-min formula.

## WHAT IS PROVED

* `hasCommon_mono` -- a common answer survives shrinking, so obstructions are UPWARD
  closed: any superset of an obstruction is an obstruction.
* `classes_resolve_iff` -- **the law**: every class has a common safe answer iff no
  obstruction is contained in a class.
* `resolution_refines` -- raising the order can only split classes, never merge them, so
  obstruction-freeness transfers to a finer class map. Existence of a finite resolving
  order or attainment of a minimum is NOT a conclusion of this theorem.
* `obstruction_error_floor_deterministic` -- against an obstruction, every deterministic
  rule is unsafe in some world of it.
* `obstruction_error_floor_randomized` -- **and every RANDOMIZED rule has worst-case
  unsafe probability at least `1/|H|`**, by a fibre-counting argument: each action is
  unsafe somewhere in `H`, so the total unsafe mass over `H` is at least one.  This is the
  error floor that converts "the obstruction survived" into a lower bound on risk, and it
  covers randomized decoders, not only deterministic ones.
* `no_obstruction_iff_global_answer` -- the degenerate case: if the whole world set admits
  a common safe answer then there are no obstructions at all and the decision costs
  nothing, which must be excluded before any rate statement is made.

## WHAT THIS DOES NOT ESTABLISH

- **The rate `N_safe(h) = Theta(h^(-2 r_safe))` is NOT proved here.**  This module supplies
  the combinatorics -- which classes suffice, and the error floor that makes a surviving
  obstruction costly.  Converting an order-`r` indistinguishability into a Hellinger
  distance, and that into a sample count, is the analytic half and is not formalised.
- `r_q(F,G)`, the order at which query `q` separates two worlds, is taken as given.  Its
  existence for the polynomial-query class is the subject of
  `LeanUnifiedQueryOrderV1`, which proves the vanishing but not the attainment.
- Finitely many worlds, actions and queries throughout.
- Nothing here says the minimal obstructions are easy to find; `r_safe` is a formula, not
  an algorithm.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.UnifiedObstructionOrder

open Finset

variable {World Act : Type*} [DecidableEq World] [Fintype World]
  [DecidableEq Act] [Fintype Act]

/-! `safe F` is the set of decisions that are eps-correct in world `F`. -/

variable (safe : World → Finset Act)

/-- A set of worlds admits a common safe answer. -/
def HasCommon (H : Finset World) : Prop := ∃ a : Act, ∀ F ∈ H, a ∈ safe F

/-- An obstruction: no single decision is safe throughout. -/
def IsObstruction (H : Finset World) : Prop := ¬ HasCommon safe H

/-- **A common answer survives shrinking.** -/
theorem hasCommon_mono {H H' : Finset World} (hsub : H ⊆ H')
    (h : HasCommon safe H') : HasCommon safe H := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun F hF => ha F (hsub hF)⟩

/-- **Hence obstructions are upward closed.**  This is why it is enough to look at the
classes a learner cannot split: if any obstruction hides inside a class, the class itself
is one. -/
theorem isObstruction_mono {H H' : Finset World} (hsub : H ⊆ H')
    (h : IsObstruction safe H) : IsObstruction safe H' :=
  fun hc => h (hasCommon_mono safe hsub hc)

/-- **The law.**  Given any grouping of worlds into classes, every class has a common safe
answer exactly when no obstruction is contained in a class. -/
theorem classes_resolve_iff {K : Type*} [DecidableEq K] [Fintype K]
    (cls : World → K) :
    (∀ k : K, HasCommon safe (univ.filter (fun F => cls F = k)))
      ↔ (∀ H : Finset World, IsObstruction safe H →
            ¬ ∃ k : K, H ⊆ univ.filter (fun F => cls F = k)) := by
  constructor
  · rintro hall H hH ⟨k, hk⟩
    exact hH (hasCommon_mono safe hk (hall k))
  · intro hno k
    by_contra hc
    exact hno (univ.filter (fun F => cls F = k)) hc ⟨k, Finset.Subset.refl _⟩

/-- Raising the resolution order can only split classes.  Stated for an arbitrary pair of
class maps with `fine` refining `coarse`. -/
theorem resolution_refines [Nonempty Act] {K L : Type*} [DecidableEq K] [DecidableEq L]
    [Fintype K] [Fintype L] (coarse : World → K) (fine : World → L)
    (hrefine : ∀ F G : World, fine F = fine G → coarse F = coarse G)
    (hcoarse : ∀ k : K, HasCommon safe (univ.filter (fun F => coarse F = k))) :
    ∀ l : L, HasCommon safe (univ.filter (fun F => fine F = l)) := by
  intro l
  by_cases hne : (univ.filter (fun F => fine F = l)).Nonempty
  · obtain ⟨F0, hF0⟩ := hne
    have hsub : univ.filter (fun F => fine F = l)
        ⊆ univ.filter (fun F => coarse F = coarse F0) := by
      intro G hG
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG hF0 ⊢
      exact hrefine G F0 (by rw [hG, hF0])
    exact hasCommon_mono safe hsub (hcoarse (coarse F0))
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    exact ⟨Classical.arbitrary Act, fun F hF => absurd hF (by simp)⟩

/-! ### The error floor an obstruction creates -/

/-- **Against an obstruction, every deterministic rule fails somewhere in it.** -/
theorem obstruction_error_floor_deterministic {H : Finset World}
    (hH : IsObstruction safe H) (a : Act) : ∃ F ∈ H, a ∉ safe F := by
  by_contra hc
  push_neg at hc
  exact hH ⟨a, hc⟩

/-- The unsafe mass a randomized rule puts on world `F`. -/
noncomputable def unsafeMass (p : Act → ℝ) (F : World) : ℝ :=
  ∑ a ∈ univ.filter (fun a => a ∉ safe F), p a

/-- **Every randomized rule has total unsafe mass at least one across an obstruction.**
Each action is unsafe in SOME world of `H`; assigning each action to such a world gives
disjoint fibres whose masses sum to the rule's total mass. -/
theorem obstruction_total_unsafe_mass {H : Finset World}
    (hH : IsObstruction safe H) (p : Act → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    1 ≤ ∑ F ∈ H, unsafeMass safe p F := by
  classical
  -- choose, for each action, a world of `H` in which it is unsafe
  have hchoice : ∀ a : Act, ∃ F, F ∈ H ∧ a ∉ safe F := by
    intro a
    obtain ⟨F, hF, hns⟩ := obstruction_error_floor_deterministic safe hH a
    exact ⟨F, hF, hns⟩
  choose w hwH hwns using hchoice
  -- the fibres of that assignment partition the actions
  have hfib : ∑ F ∈ H, ∑ a ∈ univ.filter (fun a => w a = F), p a = ∑ a, p a := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := w) (fun a _ => hwH a)]
  -- and each fibre's mass is below the unsafe mass of its world
  have hle : ∀ F ∈ H, ∑ a ∈ univ.filter (fun a => w a = F), p a ≤ unsafeMass safe p F := by
    intro F _
    unfold unsafeMass
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rw [← ha]
      exact hwns a
    · intro a _ _
      exact hp a
  calc (1 : ℝ) = ∑ a, p a := hsum.symm
    _ = ∑ F ∈ H, ∑ a ∈ univ.filter (fun a => w a = F), p a := hfib.symm
    _ ≤ ∑ F ∈ H, unsafeMass safe p F := Finset.sum_le_sum hle

/-- **The floor.**  Some world of the obstruction receives unsafe mass at least `1/|H|`,
for a COMMON action distribution p. Applying this to a data-dependent decoder requires
identical transcript laws, or an explicit approximation bound; that join is not here. -/
theorem obstruction_error_floor_randomized {H : Finset World}
    (hH : IsObstruction safe H) (hne : H.Nonempty) (p : Act → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    ∃ F ∈ H, 1 / (H.card : ℝ) ≤ unsafeMass safe p F := by
  classical
  by_contra hc
  push_neg at hc
  have hcard : (0 : ℝ) < (H.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hlt : ∑ F ∈ H, unsafeMass safe p F < ∑ _F ∈ H, 1 / (H.card : ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty hne
    intro F hF
    exact hc F hF
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  rw [mul_one_div, div_self (ne_of_gt hcard)] at hlt
  exact absurd (obstruction_total_unsafe_mass safe hH p hp hsum) (not_le.mpr hlt)

/-- **The degenerate case that must be excluded.**  If the whole world set has a common
safe answer then there are no obstructions at all, the safe decision costs nothing, and no
rate statement applies. -/
theorem no_obstruction_iff_global_answer :
    HasCommon safe (univ : Finset World)
      ↔ ∀ H : Finset World, ¬ IsObstruction safe H := by
  constructor
  · intro h H hH
    exact hH (hasCommon_mono safe (Finset.subset_univ H) h)
  · intro h
    by_contra hc
    exact h univ hc

#print axioms hasCommon_mono
#print axioms isObstruction_mono
#print axioms classes_resolve_iff
#print axioms resolution_refines
#print axioms obstruction_error_floor_deterministic
#print axioms obstruction_total_unsafe_mass
#print axioms obstruction_error_floor_randomized
#print axioms no_obstruction_iff_global_answer

end CIGAMF.P13.UnifiedObstructionOrder
