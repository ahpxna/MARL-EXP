import Mathlib
import «LeanFunctionalRankingV6»

/-! # Functional certificate lifetime under deterministic policy drift -/

namespace CIGAMF.P13.FunctionalCertificateLifetime

open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.FunctionalBoundary

variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

theorem LIFE1_gauge_triangle (Q₁ Q₂ Q₃ : A → ℝ) :
    gaugeError Q₁ Q₃ ≤ gaugeError Q₁ Q₂ + gaugeError Q₂ Q₃ := by
  have hfun : (fun a ↦ Q₁ a - Q₃ a) =
      (fun a ↦ (Q₁ a - Q₂ a) + (Q₂ a - Q₃ a)) := by
    funext a
    ring
  have h := osc_add_le (fun a ↦ Q₁ a - Q₂ a)
    (fun a ↦ Q₂ a - Q₃ a)
  unfold gaugeError
  rw [hfun]
  linarith

theorem LIFE1_drift_composition
    (Qhat Qt Qfuture : A → ℝ) (delta drift : ℝ)
    (hEst : gaugeError Qhat Qt ≤ delta)
    (hDrift : gaugeError Qfuture Qt ≤ drift) :
    gaugeError Qhat Qfuture ≤ delta + drift := by
  have hsym : gaugeError Qt Qfuture = gaugeError Qfuture Qt := by
    unfold gaugeError
    rw [show (fun a ↦ Qt a - Qfuture a) =
        (fun a ↦ -(Qfuture a - Qt a)) by funext a; ring, osc_neg]
  have htri := LIFE1_gauge_triangle Qhat Qt Qfuture
  rw [hsym] at htri
  linarith

private theorem preserves_of_gauge_le
    (Qnew Qold : A → ℝ) (aPlus aMinus : A) (g bound : ℝ)
    (hGapPos : 0 < g)
    (hMaxGap : ∀ a ≠ aPlus, g ≤ Qold aPlus - Qold a)
    (hMinGap : ∀ a ≠ aMinus, g ≤ Qold a - Qold aMinus)
    (hGauge : gaugeError Qnew Qold ≤ bound)
    (hPhase : bound < g / 2) :
    PreservesExtrema Qnew Qold aPlus aMinus := by
  rcases (GQ_exact_gauge_identity Qnew Qold).1 with ⟨c, hc⟩
  apply A2_gauge_extrema_stability Qnew Qold aPlus aMinus g bound
    hGapPos hMaxGap hMinGap
  · exact ⟨c, fun a ↦ le_trans (hc a) hGauge⟩
  · exact hPhase

/- The old extrema identities are shared by both the frozen estimate and the
future true response.  This is the precise conservative reuse semantics; it
does not incorrectly use the old gap as a gap theorem for the future world. -/
theorem LIFE2_conservative_reuse
    (Qhat Qt Qfuture : A → ℝ) (aPlus aMinus : A)
    (g delta drift : ℝ)
    (hGapPos : 0 < g)
    (hMaxGap : ∀ a ≠ aPlus, g ≤ Qt aPlus - Qt a)
    (hMinGap : ∀ a ≠ aMinus, g ≤ Qt a - Qt aMinus)
    (hEst : gaugeError Qhat Qt ≤ delta)
    (hDrift : gaugeError Qfuture Qt ≤ drift)
    (hPhase : 2 * (delta + drift) < g)
    (hDeltaNonneg : 0 ≤ delta) (hDriftNonneg : 0 ≤ drift) :
    PreservesExtrema Qhat Qt aPlus aMinus ∧
      PreservesExtrema Qfuture Qt aPlus aMinus := by
  constructor
  · apply preserves_of_gauge_le Qhat Qt aPlus aMinus g delta
      hGapPos hMaxGap hMinGap hEst
    linarith
  · apply preserves_of_gauge_le Qfuture Qt aPlus aMinus g drift
      hGapPos hMaxGap hMinGap hDrift
    linarith

theorem LIFE3_bounded_update_drift
    (Q : ℕ → A → ℝ) (t h : ℕ) (nu : ℝ)
    (hStep : ∀ s, gaugeError (Q (s + 1)) (Q s) ≤ nu) :
    gaugeError (Q (t + h)) (Q t) ≤ (h : ℝ) * nu := by
  induction h with
  | zero =>
      have hzero : (fun a ↦ Q t a - Q t a) = (fun _ : A ↦ (0 : ℝ)) := by
        funext a
        ring
      have hmax : maxVal (fun _ : A ↦ (0 : ℝ)) = 0 := by
        rcases exists_eq_maxVal (fun _ : A ↦ (0 : ℝ)) with ⟨a, ha⟩
        simpa using ha.symm
      have hmin : minVal (fun _ : A ↦ (0 : ℝ)) = 0 := by
        rcases exists_eq_minVal (fun _ : A ↦ (0 : ℝ)) with ⟨a, ha⟩
        simpa using ha.symm
      simp [gaugeError, hzero, osc, hmax, hmin]
  | succ h ih =>
      have htri := LIFE1_gauge_triangle (Q (t + h + 1)) (Q (t + h)) (Q t)
      have hs := hStep (t + h)
      rw [Nat.add_assoc] at htri
      have hs' :
          gaugeError (Q (t + (h + 1))) (Q (t + h)) ≤ nu := by
        simpa [Nat.add_assoc] using hs
      calc
        gaugeError (Q (t + (h + 1))) (Q t) ≤
            gaugeError (Q (t + (h + 1))) (Q (t + h)) +
              gaugeError (Q (t + h)) (Q t) := htri
        _ ≤ nu + (h : ℝ) * nu := add_le_add hs' ih
        _ = ((h + 1 : ℕ) : ℝ) * nu := by
          push_cast
          ring

def LifetimeSafe (delta nu g : ℝ) (h : ℕ) : Prop :=
  2 * (delta + (h : ℝ) * nu) < g

/- A definitionally transparent finite-horizon maximum contract avoids hiding
floor/strict-bound edge conventions in an opaque arithmetic formula. -/
def IsCertifiedLifetime (H Hstar : ℕ) (delta nu g : ℝ) : Prop :=
  Hstar ≤ H ∧ LifetimeSafe delta nu g Hstar ∧
    ∀ h ≤ H, LifetimeSafe delta nu g h → h ≤ Hstar

theorem LIFE4_within_certified_lifetime
    (H Hstar h : ℕ) (delta nu g : ℝ)
    (hLifetime : IsCertifiedLifetime H Hstar delta nu g)
    (hLe : h ≤ Hstar)
    (hDeltaNonneg : 0 ≤ delta) (hNuNonneg : 0 ≤ nu) :
    LifetimeSafe delta nu g h := by
  have hs := hLifetime.2.1
  unfold LifetimeSafe at hs ⊢
  have hcast : (h : ℝ) ≤ (Hstar : ℝ) := by exact_mod_cast hLe
  nlinarith

theorem LIFE5_future_topK_margin
    {I : Type*} [Fintype I] [DecidableEq I]
    (Ct Cfuture Chat e drift : I → ℝ)
    (S : Finset I) (k : ℕ)
    (hcard : S.card = k)
    (hEstimate : ∀ j, |Chat j - Ct j| ≤ e j)
    (hFuture : ∀ j, |Cfuture j - Ct j| ≤ drift j)
    (hmargin : ∀ j ∈ S, ∀ l ∉ S,
      e j + e l + drift j + drift l < Ct j - Ct l) :
    CIGAMF.V6.FunctionalRanking.StrictTopK Cfuture S k := by
  refine ⟨hcard, ?_⟩
  intro j hj l hl
  have hjf := (abs_le.mp (hFuture j)).1
  have hlf := (abs_le.mp (hFuture l)).2
  have heNonnegJ : 0 ≤ e j := le_trans (abs_nonneg _) (hEstimate j)
  have heNonnegL : 0 ≤ e l := le_trans (abs_nonneg _) (hEstimate l)
  have hm := hmargin j hj l hl
  linarith

end CIGAMF.P13.FunctionalCertificateLifetime
