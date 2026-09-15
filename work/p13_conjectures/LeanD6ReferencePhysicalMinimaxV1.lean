import «LeanD6ReferencePhysicalBoundsV1»
import «LeanD6ReferenceCertifiedPhaseValueV1»

/-! # D06: the D05 certificates stated in physical parameters only.

`full_actual_minimax_certificates` (D05) is quantified over `Region q j T`, a
structure that BUNDLES ten fields, one of which (`hp : 1/2 ≤ rho - 2 b`) is an
algebraic side condition a reader cannot check by inspecting the construction.
`LeanD6ReferencePhysicalBoundsV1` proved `hp` from the geometry, so it need not
be assumed. This file is the public interface that follows: the hypotheses are
exactly the physical ones

    2 ≤ q,  T ∈ worlds q j,  0 ≤ t ≤ 1,  1 ≤ rho ≤ 2,  strong : 1 ≤ (q-1) b,

and both certificates are stated in `gateMass` / `slopeBval` / `actualLoss` /
`legalMinimum` — no `Region` appears anywhere in the statement. Nothing new is
proved here: the content is D05 plus D06's `hp_from_physical`, assembled so that
the assumption list of the main theorem is visible without opening a structure.

SIZE. `I n = Fin (n+1)`, so the ambient instance `I (2*q+1)` has `2*q+2`
coordinates and the retained set has `k = q+1` of them. At `q = 8`: `18`
coordinates, `k = 9` retained.

WHAT IS STILL ASSUMED. `strong` remains an input. It is not free: `b ≤ 1/4`
forces `q ≥ 5` (`strong_needs_size`), and a floating-point grid scan — evidence,
not a theorem — finds the full region empty for `q ≤ 7` and first inhabited at
`q = 8`. Every theorem below is therefore vacuous on any `(q,t,rho)` where the
hypotheses cannot be met; `LeanD6ReferencePhaseWitnessV1` supplies one triple
where they can.

SCOPE. This is a minimax over the actual same-response world family
`worlds q j` built by the construction, NOT over every `F` with the same
response. The lower certificate does quantify over every finite randomized
decision rule of the original budget.
-/

namespace CIGAMF.P13.D6ReferencePhysicalMinimax
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceLegalCountMinimum CIGAMF.P13.D6ReferencePhaseRegretBridge
open CIGAMF.P13.D6ReferenceEndpointWorlds CIGAMF.P13.D6ReferenceEndpointWorlds.Region
open CIGAMF.P13.D6ReferencePhaseValue CIGAMF.P13.D6ReferenceMatchingMinimax
open CIGAMF.P13.D6ReferencePhysicalBounds CIGAMF.P13.D6ReferenceCertifiedPhaseValue
noncomputable section

variable {q : ℕ} {j : I (2*q+1)} {T : Finset (I (2*q+1))}

/-! ## Physical spellings of the two objects the certificates talk about -/

/-- Regret of decision `S` in world `A`, in physical parameters only. -/
def physicalRegret (T : Finset (I (2*q+1))) (j : I (2*q+1))
    (A S : Finset (I (2*q+1))) (rho t : ℝ) : ℝ :=
  actualLoss A T S j rho t-legalMinimum A T j rho t

/-- The finite-`k` phase value (`k = q+1`), in physical parameters only. -/
def physicalValue (q : ℕ) (T : Finset (I (2*q+1))) (j : I (2*q+1)) (rho t : ℝ) : ℝ :=
  phaseValueFull ((q:ℝ)+1) (rho-2*slopeBval t T j) (gateMass t T j-slopeBval t T j)
    (min (gateMass t T j) (2*slopeBval t T j)) (2*gateMass t T j-rho)

theorem physicalRegret_eq (M : Region q j T) (A S : Finset (I (2*q+1))) :
    physicalRegret T j A S M.rho M.t = M.regret A S := rfl

theorem physicalValue_eq (M : Region q j T) :
    physicalValue q T j M.rho M.t = phaseValueFull ((q:ℝ)+1) M.p M.c M.e M.r := rfl

/-! ## The public theorem -/

/-- D05 + D06, with a fully physical hypothesis list. Upper: one fixed pair of
legal decisions, mixed with a fixed weight, is at most the value in EVERY world.
Lower: for every finite randomized legal decision rule there is a world of the
family in which it pays at least the value. -/
theorem physical_minimax_certificates (q : ℕ) (j : I (2*q+1)) (T : Finset (I (2*q+1)))
    (t rho : ℝ) (hq : 2 ≤ q) (hT : T ∈ worlds q j) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : 1 ≤ rho) (hr2 : rho ≤ 2) (strong : 1 ≤ ((q:ℝ)-1)*slopeBval t T j) :
    (∃ w : ℝ,0 ≤ w ∧ w ≤ 1 ∧ Tᶜ.card=T.card ∧
      ∀ A ∈ worlds q j,
        w*physicalRegret T j A T rho t+(1-w)*physicalRegret T j A Tᶜ rho t ≤
          physicalValue q T j rho t) ∧
    (∀ (decisions : Finset (Finset (I (2*q+1)))) (w : Finset (I (2*q+1)) → ℝ),
      (∀ S ∈ decisions,0 ≤ w S) → (∑ S ∈ decisions,w S=1) →
      (∀ S ∈ decisions,S.card=T.card) →
      ∃ A ∈ worlds q j,physicalValue q T j rho t ≤
        ∑ S ∈ decisions,w S*physicalRegret T j A S rho t) :=
  full_actual_minimax_certificates (physicalRegion q j T t rho hq hT ht0 ht1 hr hr2 strong)

/-! ## The phase dichotomy, also physical

`e ≤ k r` is `min a (2b) ≤ (q+1) (2a - rho)`: the gate's correction is cheap
enough that the learner must still pay. Above it the value is exactly zero. -/

theorem physicalValue_inactive (q : ℕ) (j : I (2*q+1)) (T : Finset (I (2*q+1))) (t rho : ℝ)
    (hinact : ((q:ℝ)+1)*(2*gateMass t T j-rho) ≤ min (gateMass t T j) (2*slopeBval t T j)) :
    physicalValue q T j rho t=0 :=
  phaseValueFull_zero _ _ _ _ _ hinact

theorem physicalValue_active (q : ℕ) (j : I (2*q+1)) (T : Finset (I (2*q+1)))
    (t rho : ℝ) (hq : 2 ≤ q) (hT : T ∈ worlds q j) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : 1 ≤ rho) (hr2 : rho ≤ 2) (strong : 1 ≤ ((q:ℝ)-1)*slopeBval t T j)
    (hact : min (gateMass t T j) (2*slopeBval t T j) ≤ ((q:ℝ)+1)*(2*gateMass t T j-rho)) :
    physicalValue q T j rho t =
      uTop ((q:ℝ)+1) (2*gateMass t T j-rho) (min (gateMass t T j) (2*slopeBval t T j))*
        vTerm ((q:ℝ)+1) (rho-2*slopeBval t T j) (min (gateMass t T j) (2*slopeBval t T j))
          (2*gateMass t T j-rho)/
        ((gateMass t T j-slopeBval t T j)*(((q:ℝ)+1)-1)) := by
  have hb := region_bounds (physicalRegion q j T t rho hq hT ht0 ht1 hr hr2 strong)
  have hc : (gateMass t T j-slopeBval t T j)*(((q:ℝ)+1)-1) ≠ 0 := by
    rw [add_sub_cancel_right]
    exact ne_of_gt (mul_pos hb.2.2.2 (by exact_mod_cast (show 0<q by omega)))
  exact phaseValueFull_eq _ _ _ _ _ hact hc

/-- The gate condition `hp` is a THEOREM of the geometry, not an input: no
hypothesis of `physical_minimax_certificates` mentions it. -/
theorem hp_not_assumed (t rho : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hr : 1 ≤ rho)
    (q : ℕ) (hq : 2 ≤ q) (T : Finset (I (2*q+1))) (j : I (2*q+1)) (hT : T ∈ worlds q j) :
    1/2 ≤ rho-2*slopeBval t T j :=
  hp_from_physical t rho ht0 ht1 hr q hq T j hT

/-- The ambient coordinate count and the retained count, spelled out. -/
theorem instance_size (q : ℕ) (j : I (2*q+1)) (T : Finset (I (2*q+1))) (hq : 2 ≤ q)
    (hT : T ∈ worlds q j) :
    Fintype.card (I (2*q+1))=2*q+2 ∧ T.card=q+1 ∧ (others T j).card=q := by
  have hpar := world_parameters q j hq hT
  refine ⟨by simp [I],hpar.2.1,?_⟩
  change (Tᶜ.erase j).card=q
  rw [Finset.card_erase_of_mem (by simp [hpar.1]),hpar.2.2.1,hpar.2.1]
  omega

#print axioms physicalRegret_eq
#print axioms physicalValue_eq
#print axioms physical_minimax_certificates
#print axioms physicalValue_inactive
#print axioms physicalValue_active
#print axioms hp_not_assumed
#print axioms instance_size

end
end CIGAMF.P13.D6ReferencePhysicalMinimax
