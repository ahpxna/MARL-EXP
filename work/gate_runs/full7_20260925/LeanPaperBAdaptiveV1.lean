import Mathlib

/-!
# Paper B: policy cancellation for an ADAPTIVE randomised policy

`LeanPaperBTranscriptV1` cancels the policy when each step's kernel value is a number.  A
randomised adaptive policy's kernel at step `t` is a function of the transcript, so the
cancellation has to survive that dependence --- and it does, for the same reason and with no
extra hypothesis: the learner runs the SAME rule under both worlds, so whatever the kernel
evaluates to, it evaluates to the same thing on both sides of the ratio.

The statement below therefore lets the policy factor depend on the WHOLE transcript, which
is strictly more than adaptivity requires (a real policy depends only on the strict past).
Proving it in the stronger form makes clear that nothing about predictability is being used
for the cancellation itself --- predictability is needed for the conditional law of the next
observation, which is a different step.

WHAT IS STILL NOT HERE, AND IT IS THE HARD PART.  This is an identity between transcript
WEIGHTS.  The obligation is the measure-theoretic one:

    L_t  =  d P_theta |_{F_t}  /  d P_lambda |_{F_t}

on the filtration, and then `KL = E_theta log L_N` with the tower property giving the sum of
per-step divergences.  That requires two actual probability laws on the transcript space and
a change-of-measure identity; a ratio of densities against a common reference is the right
route, but it is not carried out here.  Until it is, "every randomised adaptive policy" is
not proved.
-/

namespace CIGAMF.P13.PaperBAdaptive

open Finset

variable {n : ℕ} {H : Type*}

/-- The transcript weight with a HISTORY-DEPENDENT policy factor. -/
noncomputable def weightH (pol obs : Fin n → H → ℝ) (y : H) : ℝ :=
  ∏ t, pol t y * obs t y

theorem weightH_eq (pol obs : Fin n → H → ℝ) (y : H) :
    weightH pol obs y = (∏ t, pol t y) * ∏ t, obs t y := by
  unfold weightH
  rw [Finset.prod_mul_distrib]

/-- **The policy cancels even when it reads the transcript.**  No predictability is used:
the same rule appears on both sides. -/
theorem policy_cancels_adaptive (pol obsT obsL : Fin n → H → ℝ) (y : H)
    (hpol : ∀ t, pol t y ≠ 0) (hobs : ∀ t, obsL t y ≠ 0) :
    weightH pol obsT y / weightH pol obsL y = ∏ t, obsT t y / obsL t y := by
  have hP : (∏ t, pol t y) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun t _ => hpol t)
  have hL : (∏ t, obsL t y) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun t _ => hobs t)
  rw [weightH_eq, weightH_eq, Finset.prod_div_distrib]
  field_simp

/-- **The division-free form**, which is what a change-of-measure argument uses: the two
weights agree up to the common policy factor, with nothing divided anywhere. -/
theorem weightH_common_factor (pol obsT obsL : Fin n → H → ℝ) (y : H) :
    weightH pol obsT y * (∏ t, obsL t y) = weightH pol obsL y * ∏ t, obsT t y := by
  rw [weightH_eq, weightH_eq]
  ring

/-- **And the log telescopes**, which is the shape the chain rule consumes. -/
theorem log_weightH_ratio (pol obsT obsL : Fin n → H → ℝ) (y : H)
    (hpol : ∀ t, pol t y ≠ 0) (hT : ∀ t, 0 < obsT t y) (hL : ∀ t, 0 < obsL t y) :
    Real.log (weightH pol obsT y / weightH pol obsL y)
      = ∑ t, Real.log (obsT t y / obsL t y) := by
  rw [policy_cancels_adaptive pol obsT obsL y hpol (fun t => ne_of_gt (hL t))]
  rw [Real.log_prod]
  intro t _
  exact ne_of_gt (div_pos (hT t) (hL t))

/-- **A policy that reads only the strict past is a special case**, recorded so the general
statement is not mistaken for a weaker one. -/
theorem adaptive_generalises (pol : Fin n → ℝ) (obsT obsL : Fin n → H → ℝ) (y : H)
    (hpol : ∀ t, pol t ≠ 0) (hobs : ∀ t, obsL t y ≠ 0) :
    weightH (fun t _ => pol t) obsT y / weightH (fun t _ => pol t) obsL y
      = ∏ t, obsT t y / obsL t y :=
  policy_cancels_adaptive (fun t _ => pol t) obsT obsL y hpol hobs

/-! ## Audit -/

#print axioms weightH_eq
#print axioms policy_cancels_adaptive
#print axioms weightH_common_factor
#print axioms log_weightH_ratio
#print axioms adaptive_generalises

end CIGAMF.P13.PaperBAdaptive
