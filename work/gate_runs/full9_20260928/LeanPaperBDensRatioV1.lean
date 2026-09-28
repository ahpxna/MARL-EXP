import «LeanPaperBChangeV1»

/-!
# Paper B: `hdens` reduced to "both restrictions have densities"

`change_of_measure` asks for

    hdens : forall t, P.trim (F.le t) = (Q.trim (F.le t)).withDensity (L t),

and building it for a concrete continuous policy was recorded as the blocker for the
adaptive Gaussian transcript.  Part of that blocker is not about Gaussians at all: it is the
general step from "both laws have densities with respect to a common base" to "one is the
other with a density".  That step is here.

`withDensity_ratio` is the general fact: if `P = nu.withDensity p` and `Q = nu.withDensity q`
with `q` finite and nowhere zero, then `P = Q.withDensity (p/q)`, with no hypothesis about
what `nu` is.  `hdens_of_densities` is the same statement in the exact shape
`change_of_measure` consumes, one level `t` at a time.

So the remaining ask for the continuous case is no longer "construct `hdens`" but "exhibit
the densities of the two restricted laws with respect to a common base" -- for the Gaussian
transcript, the marginal of the path density over the unobserved coordinates.  That is a
statement about the construction, not about the conclusion, and it is what
`LeanPaperBGaussStepV1` computes at one step.
-/

namespace CIGAMF.P13.PaperBDensRatio

open MeasureTheory
open scoped ENNReal

variable {α : Type*} {mα : MeasurableSpace α}

/-- **A density over a density.**  If two measures have densities with respect to the same
base and the denominator is finite and nowhere zero, the first is the second with the ratio
as density. -/
theorem withDensity_ratio (ν : Measure α) (p q : α → ENNReal)
    (hp : Measurable p) (hq : Measurable q)
    (hq0 : ∀ x, q x ≠ 0) (hqtop : ∀ x, q x ≠ ⊤) :
    ν.withDensity p = (ν.withDensity q).withDensity (fun x => p x / q x) := by
  have hmeas : Measurable (fun x => p x / q x) := hp.div hq
  rw [← withDensity_mul _ hq hmeas]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [ENNReal.mul_div_cancel' (fun hc => absurd hc (hq0 x)) (fun hc => absurd hc (hqtop x))]

/-- **`hdens`, from densities at each level.**  This is `withDensity_ratio` in the shape
`change_of_measure` asks for: supply the two restricted laws' densities against a common
base at each `t`, and the hypothesis is discharged. -/
theorem hdens_of_densities {Ω : Type*} {m0 : MeasurableSpace Ω}
    (F : Filtration ℕ m0) (P Q : Measure Ω)
    (base : (t : ℕ) → @Measure Ω (F t))
    (p q : ℕ → Ω → ENNReal)
    (hp : ∀ t, Measurable[F t] (p t)) (hq : ∀ t, Measurable[F t] (q t))
    (hq0 : ∀ t x, q t x ≠ 0) (hqtop : ∀ t x, q t x ≠ ⊤)
    (hP : ∀ t, P.trim (F.le t) = (base t).withDensity (p t))
    (hQ : ∀ t, Q.trim (F.le t) = (base t).withDensity (q t)) :
    ∀ t, P.trim (F.le t)
      = (Q.trim (F.le t)).withDensity (fun ω => p t ω / q t ω) := by
  intro t
  rw [hP t, hQ t]
  exact withDensity_ratio (mα := F t) (base t) (p t) (q t) (hp t) (hq t) (hq0 t) (hqtop t)

/-! ## Audit -/

#print axioms withDensity_ratio
#print axioms hdens_of_densities

end CIGAMF.P13.PaperBDensRatio
