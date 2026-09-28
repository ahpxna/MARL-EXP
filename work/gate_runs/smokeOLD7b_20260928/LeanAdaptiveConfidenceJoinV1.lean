import Mathlib
import «LeanAdaptiveLoopJoinV1»

/-! # Adaptive: the confidence event, and what the loop guarantees ON it.

`LeanAdaptiveLoopJoinV1` proves the SCHEDULE half of the join: soundness from
revalidation, and total spend below `4 B*`.  `scripts/P11_adaptive_loop_join.py`
measures the rest by simulation.  What is still missing -- and is stated as missing
-- is the probabilistic half: the confidence event, the tracking step, and the tail
of the stopping time.  This file supplies the COMPOSITION of those three, so what
remains open is exactly the three ingredients and not their assembly.

## WHAT IS PROVED

* `guarantee_on_event` — if on an event `E` (i) the certificate holds by epoch `k`,
  (ii) the stopping rule fires only on a certificate, and (iii) a certificate implies
  correctness, then on `E` the loop is correct AND stops by epoch `k`.
* `cost_on_event` — and then the schedule half applies verbatim: on `E` the total
  spend is below `4 B*`.
* `error_bounded_by_event` — the only probabilistic step that is needed downstream:
  if correctness holds on `E`, then the failure set is contained in `Eᶜ`, so any
  bound `P(Eᶜ) ≤ delta` transfers to the loop.  Stated with `Set`s so it is the
  measure-free part of the argument.

## WHAT THIS DOES NOT ESTABLISH

- `P(Eᶜ) ≤ delta` for the GLR threshold used in the script is NOT proved: the
  threshold there is the standard heuristic `log((K-1)(1+log n)/delta)` and the error
  rate is measured, not certified.  That is the first of the three open ingredients.
- The tracking step -- that the plug-in allocation converges to the oracle one -- is
  not proved; it is the second.
- The tail of the stopping time, and hence `E[total]`, is not proved; it is the
  third.  `guarantee_on_event` is deliberately a statement ON the event only.
-/

namespace CIGAMF.P13.AdaptiveConfidenceJoin

open CIGAMF.P13.AdaptiveLoopJoin

theorem guarantee_on_event {E : Prop} {S C : ℕ → Prop} {Correct : Prop} (k : ℕ)
    (hcert_by : E → C k) (hstop : ∀ j, S j → C j) (hsound : ∀ j, C j → Correct)
    (hfire : ∀ j, C j → S j) (hE : E) :
    Correct ∧ S k :=
  ⟨hsound k (hcert_by hE), hfire k (hcert_by hE)⟩

theorem cost_on_event {E : Prop} (b0 Bstar : ℝ) (hb0 : 0 < b0) (hB : b0 ≤ Bstar)
    (k : ℕ) (hk : Bstar ≤ budget b0 k)
    (hmin : ∀ j, j < k → budget b0 j < Bstar) (hE : E) :
    ∑ i ∈ Finset.range (k + 1), budget b0 i < 4 * Bstar :=
  doubling_factor b0 Bstar hb0 hB k hk hmin

/-- The measure-free half of "error ≤ delta": the failure set sits inside `Eᶜ`. -/
theorem error_bounded_by_event {Ω : Type*} (E Fail : Set Ω)
    (hcorrect : ∀ w ∈ E, w ∉ Fail) : Fail ⊆ Eᶜ := by
  intro w hw
  intro hwE
  exact hcorrect w hwE hw

#print axioms guarantee_on_event
#print axioms cost_on_event
#print axioms error_bounded_by_event

end CIGAMF.P13.AdaptiveConfidenceJoin
