import Mathlib
import «LeanD6RawRankOneMultiaffineV1»

/-!
# Raw rank-one coverage by searched monomial fibres

This is the sound coverage direction needed for the E2 raw-fibre search.
For every active raw-rank-one world, the coefficients recovered directly from
the world by `rawTheta` define a searched monomial fibre containing that world.

The reverse inclusion is deliberately not claimed here: it requires the
separate closure theorem that every scalar-multiaffine fibre point with a
zero-anchor coefficient is raw rank one.  This module therefore does not
silently turn a coverage result into an equality-of-varieties claim.
-/

namespace CIGAMF.P13.D6RawRankOneVarietyCoverage

open CIGAMF.P13.D6RawLocalContrastRankOne
open CIGAMF.P13.D6RawRankOneReconstruction
open CIGAMF.P13.D6RawRankOneMultiaffine

variable {U : Type*} [Fintype U] [Nonempty U] [DecidableEq U]

/-- The raw normal-form fibre searched at a fixed family of action coefficients.
The anchor-zero condition removes the affine gauge at each coordinate. -/
def InRawMonomialFibre {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (u0 : U)
    (t : Fin (n + 1) → U → ℝ) : Prop :=
  (∀ i, t i u0 = 0) ∧ F ∈ Submodule.span ℝ (monomialSet t)

/-- Union over all anchor-normalized raw fibres. -/
def InSomeRawMonomialFibre {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (u0 : U) : Prop :=
  ∃ t, InRawMonomialFibre F u0 t

/-- **Lemma 6 (coverage).**  Given fixed active representatives, raw local
rank one places the world in the raw monomial fibre generated directly from
its own contrasts.  No factorization witness is chosen or used. -/
theorem rawRankOne_active_covered_by_rawMonomialFibre {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (u0 : U)
    (r : Fin (n + 1) → U) (zs : Fin (n + 1) → (Fin (n + 1) → U))
    (hRank : ∀ i, RawLocalContrastRankOne F i u0)
    (hr : ∀ i, rawLocalContrast F i u0 (r i) (zs i) ≠ 0) :
    InSomeRawMonomialFibre F u0 := by
  let t : Fin (n + 1) → U → ℝ :=
    fun i u => rawTheta F i u0 (r i) (zs i) u
  refine ⟨t, ?_, ?_⟩
  · intro i
    simp [t, rawTheta_anchor]
  · simpa [t] using rawRankOne_mem_monomialSpan F u0 r zs hRank hr

end CIGAMF.P13.D6RawRankOneVarietyCoverage
