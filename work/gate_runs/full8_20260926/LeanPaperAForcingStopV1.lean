import «LeanPaperASacrificeStoppedV1»

/-!
# Paper A: the forcing law for policies that stop almost surely

`forcing_law` and `power_forcing_law` (`LeanPaperASacrificeV1`) are stated for finite-horizon
policies. This module extends them to every stopping policy that stops almost surely at the
truth (`CorrectA`), with no bound on the stopping time.

* `forcing_law_stopped`: if at every horizon the stopped history has
  `Mid ≤ φ(T) + B_n` pathwise, with `E B_n ≤ b`, `φ` continuous, concave and nondecreasing on
  `[0, ∞)`, and the expected real queries of the whole run are at most `T̄`, then
  `φ(T̄) ≥ 8rM·D(2δ) - b`. The truncation at a horizon where at most `δ` of the true world's runs
  are unstopped is correct at level `2δ`, its counts are at most the whole run's, and `φ` is
  nondecreasing.
* `power_forcing_law_stopped`: with `φ(t) = c t^a`, `T̄ ≥ ((8rM·D(2δ) - b)/c)^{1/a}`.
-/

namespace CIGAMF.P13.PaperAForcingStop

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperABridge CIGAMF.P13.PaperABridgeDummy CIGAMF.P13.PaperAFamilyLower
open CIGAMF.P13.PaperASacrifice CIGAMF.P13.PaperASacrificeStopped CIGAMF.P13.PaperBStoppedLaw
open CIGAMF.P13.PaperAActualDecisionBridge CIGAMF.P13.PaperAStrict
open CIGAMF.P13.PaperACentred CIGAMF.P13.PaperARPair CIGAMF.P13.PaperAGaussianKL

variable {r : ℕ}

/-- **The forcing law for unbounded stopping.** -/
theorem forcing_law_stopped [NeZero r] (M : ℝ) (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ)
    (h2δ : 2 * δ ≤ 1) (S : SPolicy (Cell r ⊕ Unit) Bool) (hS : CorrectA M hM δ S)
    (hD : 0 ≤ demand (2 * δ)) (φ : ℝ → ℝ) (hφc : Continuous φ)
    (hφ : ConcaveOn ℝ (Set.Ici 0) φ) (hmono : MonotoneOn φ (Set.Ici 0))
    (B : ∀ n, Hist (Cell r ⊕ Unit) n → ℝ)
    (hB : ∀ n, Integrable (B n)
      (hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n))
    (b : ℝ) (hb : ∀ n, ∫ ω, B n ω
      ∂hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n ≤ b)
    (hpath : ∀ n ω, midReal n ω ≤ φ (totReal n ω) + B n ω) (Tbar : ℝ)
    (hT : ∀ n, ∫ ω, totReal n ω
      ∂hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n ≤ Tbar) :
    8 * (r : ℝ) * M * demand (2 * δ) - b ≤ φ Tbar := by
  obtain ⟨n, hθ, hl⟩ := trunc_A M hM δ hδ S hS
  have h := forcing_law M hM (stoppedPol S (famChan M hM).dummy) n {x | ansT S n x = true}
    (measurableSet_ansT S n) (2 * δ) (by linarith) h2δ hθ hl hD φ hφc hφ (B n) (hB n) b (hb n)
    (hpath n)
  have hT0 : 0 ≤ ∫ ω, totReal n ω
      ∂hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n :=
    integral_nonneg fun ω => totReal_nonneg n ω
  exact h.trans (hmono (Set.mem_Ici.mpr hT0) (Set.mem_Ici.mpr (hT0.trans (hT n))) (hT n))

/-- **The power forcing law for unbounded stopping.** -/
theorem power_forcing_law_stopped [NeZero r] (M : ℝ) (hM : 0 < M) (δ : ℝ) (hδ : 0 < δ)
    (h2δ : 2 * δ ≤ 1) (S : SPolicy (Cell r ⊕ Unit) Bool) (hS : CorrectA M hM δ S)
    (hD : 0 ≤ demand (2 * δ)) (c a : ℝ) (hc : 0 < c) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (B : ∀ n, Hist (Cell r ⊕ Unit) n → ℝ)
    (hB : ∀ n, Integrable (B n)
      (hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n))
    (b : ℝ) (hb : ∀ n, ∫ ω, B n ω
      ∂hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n ≤ b)
    (hgap : b ≤ 8 * (r : ℝ) * M * demand (2 * δ))
    (hpath : ∀ n ω, midReal n ω ≤ c * totReal n ω ^ a + B n ω) (Tbar : ℝ) (hTbar : 0 ≤ Tbar)
    (hT : ∀ n, ∫ ω, totReal n ω
      ∂hist (famChan M hM) (stoppedPol S (famChan M hM).dummy) (lift (thetaC r)) n ≤ Tbar) :
    ((8 * (r : ℝ) * M * demand (2 * δ) - b) / c) ^ (1 / a) ≤ Tbar := by
  have hφc : Continuous fun t : ℝ => c * t ^ a :=
    continuous_const.mul (Real.continuous_rpow_const ha0.le)
  have hφ : ConcaveOn ℝ (Set.Ici 0) fun t : ℝ => c * t ^ a :=
    (Real.concaveOn_rpow ha0.le ha1).smul hc.le
  have hmono : MonotoneOn (fun t : ℝ => c * t ^ a) (Set.Ici 0) := by
    intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy ha0.le) hc.le
  have h := forcing_law_stopped M hM δ hδ h2δ S hS hD (fun t => c * t ^ a) hφc hφ hmono B hB b hb
    hpath Tbar hT
  have hk : 0 ≤ (8 * (r : ℝ) * M * demand (2 * δ) - b) / c := div_nonneg (by linarith) hc.le
  have h2 : (8 * (r : ℝ) * M * demand (2 * δ) - b) / c ≤ Tbar ^ a := by
    rw [div_le_iff₀ hc]; linarith
  calc ((8 * (r : ℝ) * M * demand (2 * δ) - b) / c) ^ (1 / a)
      ≤ (Tbar ^ a) ^ (1 / a) := Real.rpow_le_rpow hk h2 (by positivity)
    _ = Tbar := by
      rw [← Real.rpow_mul hTbar, mul_one_div_cancel ha0.ne', Real.rpow_one]

#print axioms forcing_law_stopped
#print axioms power_forcing_law_stopped

end CIGAMF.P13.PaperAForcingStop
