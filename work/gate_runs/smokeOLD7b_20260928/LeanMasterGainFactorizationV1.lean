import Mathlib

/-! # MASTER: the gain matrix FACTORS, and only the active set matters.

Two audit items:

 F-G  `G_{u,l} = (c_l^T K^{-1} M_u)^2/(2 nu_l kappa_l)` was verified numerically from
      real instruments (`P22`).  What it needs as a THEOREM is the structural fact the
      rank-two claim rests on: `G` is the entrywise SQUARE of a matrix `B` that factors
      through width `r`, and the square then factors through width `r^2` -- through the
      SYMMETRIC pairs, so `r(r+1)/2` -- with no rank machinery at all.

 M4   `value_improves_iff` is an equivalence over ALL alternatives, not a derivative law
      on the active set.  The honest replacement is a SLACK lemma: when the inactive
      alternatives are `s` above the minimum and every alternative moves by at most
      `K t`, then for `2 K t < s` the minimum is still attained inside the active set.
      That is what licenses dropping inactive alternatives -- a quantitative statement,
      not an assertion.

## WHAT IS PROVED

* `hadamard_square_factor` — `(∑_k c_{uk} d_{kl})^2 = ∑_{k,k'} (c_{uk}c_{uk'})(d_{kl}d_{k'l})`:
  the entrywise square of a width-`r` product is a width-`r^2` product, and the factor
  is symmetric in `(k,k')`, so it lives on the `r(r+1)/2` symmetric pairs.
* `hadamard_square_rank_one` — a width-one `B` gives a rank-one `G`, explicitly.
* `min_attained_on_active` — **the slack law**: with `2Kt < s` the minimum after a
  perturbation of size `Kt` is attained at an alternative that was active before.
* `inactive_dropped` — hence the minimum over ALL alternatives equals the minimum over
  the active ones.

## WHAT THIS DOES NOT ESTABLISH

- The derivative identity `dI_u = G_{u,l} - I_u` itself is verified numerically in
  `P22`, not here: it needs the derivative of a matrix inverse, which is not formalised.
- `min_attained_on_active` is about a perturbation bounded by `K t`; tying `K` to a
  particular design parametrisation is the caller's job.
-/

namespace CIGAMF.P13.MasterGainFactorization

open Finset

/-- **The factorisation.**  The entrywise square of a width-`r` product is a product of
width `r²`, whose left factor `c_{uk}c_{uk'}` is symmetric in `(k,k')` -- so it lives on
the `r(r+1)/2` symmetric pairs.  No rank machinery is used. -/
theorem hadamard_square_factor {R : Type*} [Fintype R] [DecidableEq R]
    (c : R → ℝ) (d : R → ℝ) :
    (∑ k, c k * d k) ^ 2 = ∑ k, ∑ k', (c k * c k') * (d k * d k') := by
  rw [sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => by ring

/-- The left factor is symmetric, so the sum really is over unordered pairs. -/
theorem hadamard_factor_symm {R : Type*} (c : R → ℝ) (k k' : R) :
    c k * c k' = c k' * c k := mul_comm _ _

/-- A width-one `B` gives a rank-one `G`, explicitly. -/
theorem hadamard_square_rank_one (c d : ℝ) : (c * d) ^ 2 = c ^ 2 * d ^ 2 := by ring

section ActiveSet

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **The slack law.**  `f` is the profile before the perturbation, `g` after; the
active set `A` carries the minimum `V`, the rest is `s` above it, and nothing moves by
more than `K t`.  If `2 K t < s`, the new minimum is attained inside `A`. -/
theorem min_attained_on_active (f g : U → ℝ) (A : Finset U) (V s Kt : ℝ)
    (hA : A.Nonempty) (hs : 0 < s) (hKt : 0 ≤ Kt)
    (hact : ∀ u ∈ A, f u = V) (hina : ∀ u ∉ A, V + s ≤ f u)
    (hmove : ∀ u, |g u - f u| ≤ Kt) (hsmall : 2 * Kt < s) :
    ∃ u₀ ∈ A, ∀ u : U, g u₀ ≤ g u := by
  classical
  obtain ⟨u₀, hu₀A, hu₀⟩ := A.exists_min_image g hA
  refine ⟨u₀, hu₀A, fun u => ?_⟩
  by_cases hu : u ∈ A
  · exact hu₀ u hu
  · -- u is inactive: it is far above, and u₀ is close to V
    have h1 : g u₀ ≤ V + Kt := by
      have := (abs_le.1 (hmove u₀)).2
      have hf := hact u₀ hu₀A
      linarith
    have h2 : V + s - Kt ≤ g u := by
      have := (abs_le.1 (hmove u)).1
      have hf := hina u hu
      linarith
    linarith

/-- …so the minimum over ALL alternatives equals the minimum over the active ones. -/
theorem inactive_dropped [Nonempty U] (f g : U → ℝ) (A : Finset U) (V s Kt : ℝ)
    (hA : A.Nonempty) (hs : 0 < s) (hKt : 0 ≤ Kt)
    (hact : ∀ u ∈ A, f u = V) (hina : ∀ u ∉ A, V + s ≤ f u)
    (hmove : ∀ u, |g u - f u| ≤ Kt) (hsmall : 2 * Kt < s) :
    (univ : Finset U).inf' univ_nonempty g = A.inf' hA g := by
  classical
  obtain ⟨u₀, hu₀A, hu₀⟩ := min_attained_on_active f g A V s Kt hA hs hKt hact hina
    hmove hsmall
  refine le_antisymm ?_ ?_
  · obtain ⟨u₁, hu₁A, hu₁⟩ := A.exists_min_image g hA
    have hval : A.inf' hA g = g u₁ :=
      le_antisymm (Finset.inf'_le g hu₁A) (Finset.le_inf' _ _ fun u hu => hu₁ u hu)
    rw [hval]
    exact Finset.inf'_le g (mem_univ u₁)
  · refine Finset.le_inf' _ _ fun u _ => ?_
    exact le_trans (Finset.inf'_le g hu₀A) (hu₀ u)

end ActiveSet

#print axioms hadamard_square_factor
#print axioms hadamard_factor_symm
#print axioms hadamard_square_rank_one
#print axioms min_attained_on_active
#print axioms inactive_dropped

end CIGAMF.P13.MasterGainFactorization
