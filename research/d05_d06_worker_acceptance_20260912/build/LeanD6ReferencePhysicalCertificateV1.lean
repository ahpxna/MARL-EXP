import «LeanD6ReferenceCertifiedPhaseValueV1»
import «LeanD6ReferencePhaseWitnessV1»
import «LeanD6ReferenceCenteredGeometryV1»

/-! Physical-parameter acceptance theorem for D05/D06.
The upper policy is selected before the world. The lower certificate covers every
finite randomized legal policy. The game is the actual construction family
`worlds q j`; no upper bound over arbitrary functions or adaptive information
game is claimed. `strong` remains an explicit restriction.

The two examples use the same explicit reference: j = 17, T = {0,...,8} in
Fin 18, t = 1/25. No minimality claim about q = 8 is made.
-/
namespace CIGAMF.P13.D6ReferencePhysicalCertificate
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceEndpointWorlds CIGAMF.P13.D6ReferenceEndpointWorlds.Region
open CIGAMF.P13.D6ReferenceMatchingMinimax CIGAMF.P13.D6ReferenceCertifiedPhaseValue
open CIGAMF.P13.D6ReferencePhysicalBounds CIGAMF.P13.D6ReferencePhaseWitness
open CIGAMF.P13.D6ReferencePhaseValue CIGAMF.P13.D6ReferenceCenteredGeometry
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section

variable {q : ℕ} {j : I (2*q+1)} {T : Finset (I (2*q+1))}

/-- Both quantifiers of the actual finite minimax game, with an explicit legal
upper policy and arbitrary finitely randomized legal policies in the lower bound. -/
def CertifiedValue (M : Region q j T) (V : ℝ) : Prop :=
    (∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ Tᶜ.card = T.card ∧
      ∀ A ∈ worlds q j, w*M.regret A T+(1-w)*M.regret A Tᶜ ≤ V) ∧
    (∀ (decisions : Finset (Finset (I (2*q+1)))) (w : Finset (I (2*q+1)) → ℝ),
      (∀ S ∈ decisions, 0 ≤ w S) → (∑ S ∈ decisions, w S = 1) →
      (∀ S ∈ decisions, S.card = T.card) →
      ∃ A ∈ worlds q j, V ≤ ∑ S ∈ decisions, w S*M.regret A S)

/-- The algebraic threshold is the threshold of a certified actual game value. -/
theorem region_certified_threshold (M : Region q j T) :
    CertifiedValue M (phaseValueFull ((q:ℝ)+1) M.p M.c M.e M.r) ∧
    (phaseValueFull ((q:ℝ)+1) M.p M.c M.e M.r = 0 ↔
      2*M.a-M.e/((q:ℝ)+1) ≤ M.rho) := by
  have hq := M.hq
  have hk : (1:ℝ) < (q:ℝ)+1 := by
    have : (2:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  exact ⟨full_actual_minimax_certificates M,
    phase_value_zero_iff _ _ _ _ _ _ _ hk (by have hp : (1:ℝ)/2 ≤ M.p := M.hp; linarith)
      (region_bounds M).2.2.2 rfl⟩

/-- Inputs are physical parameters and the remaining strong restriction; no
`hp`, minimax bound, or threshold assertion is assumed. -/
theorem physical_certified_threshold (q : ℕ) (j : I (2*q+1))
    (T : Finset (I (2*q+1))) (t rho : ℝ)
    (hq : 2 ≤ q) (hT : T ∈ worlds q j) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : 1 ≤ rho) (hr2 : rho ≤ 2)
    (strong : 1 ≤ ((q:ℝ)-1)*slopeBval t T j) :
    let M := physicalRegion q j T t rho hq hT ht0 ht1 hr hr2 strong
    CertifiedValue M (phaseValueFull ((q:ℝ)+1) M.p M.c M.e M.r) ∧
    (phaseValueFull ((q:ℝ)+1) M.p M.c M.e M.r = 0 ↔
      2*M.a-M.e/((q:ℝ)+1) ≤ rho) :=
  region_certified_threshold _

/-- Fully explicit finite reference world. -/
def exampleJ : I (2*8+1) := ⟨17, by norm_num [I]⟩
def exampleT : Finset (I (2*8+1)) := Finset.univ.filter (fun i => i.val < 9)

theorem exampleT_mem : exampleT ∈ worlds 8 exampleJ := by
  apply Finset.mem_powersetCard.mpr
  constructor
  · intro i hi
    have hi9 : i.val < 9 := (Finset.mem_filter.mp hi).2
    simp only [positiveGround, Finset.mem_erase, Finset.mem_univ, and_true]
    intro he
    have hv := congrArg Fin.val he
    change i.val = 17 at hv
    omega
  · decide

def exampleRegion (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    Region 8 exampleJ exampleT :=
  physicalRegion 8 exampleJ exampleT (1/25) rho (by norm_num) exampleT_mem
    (by norm_num) (by norm_num) hr hr2 (strong_witness exampleJ exampleT exampleT_mem)

lemma example_coefficients (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    let M := exampleRegion rho hr hr2
    M.a = 32/25*((24/25:ℝ)^16) ∧ M.b = 7/25*((24/25:ℝ)^16) ∧
    M.e = 14/25*((24/25:ℝ)^16) ∧ M.c = ((24/25:ℝ)^16) := by
  dsimp only
  have ha : (exampleRegion rho hr hr2).a = 32/25*((24/25:ℝ)^16) :=
    gateMass_witness exampleJ exampleT exampleT_mem
  have hb : (exampleRegion rho hr hr2).b = 7/25*((24/25:ℝ)^16) :=
    slopeBval_witness exampleJ exampleT exampleT_mem
  refine ⟨ha,hb,?_,?_⟩
  · dsimp only [e]
    rw [ha,hb,min_eq_right (by norm_num)]
    ring
  · dsimp only [c]
    rw [ha,hb]
    ring

/-- Exact rational formula and strict interior location, independent of rho. -/
theorem example_threshold (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    let M := exampleRegion rho hr hr2
    2*M.a-M.e/9 = (562/225:ℝ)*(24/25)^16 ∧
    1 < 2*M.a-M.e/9 ∧ 2*M.a-M.e/9 < 2 := by
  dsimp only
  have h := example_coefficients rho hr hr2
  rw [h.1,h.2.2.1]
  refine ⟨by ring,witness_threshold_strictly_inside⟩

/-- Every cube point has positive mass at this same reference. -/
theorem example_full_support (x : I (2*8+1) → Bool) :
    0 < jointWeight (bern (1/25 : ℝ)) x :=
  reference_full_support _ (by norm_num) (by norm_num) x

/-- The positive phase is an actual minimax certificate on the explicit world. -/
theorem example_active_certified :
    let M := exampleRegion 1 le_rfl (by norm_num)
    CertifiedValue M (phaseValueFull 9 M.p M.c M.e M.r) ∧
    0 < phaseValueFull 9 M.p M.c M.e M.r := by
  dsimp only
  refine ⟨?_,?_⟩
  · simpa only [CertifiedValue, Nat.cast_ofNat, show (8:ℝ)+1=9 by norm_num] using
      full_actual_minimax_certificates (exampleRegion 1 le_rfl (by norm_num))
  
  · have h := example_coefficients 1 le_rfl (by norm_num)
    dsimp only [p,r]
    rw [h.1,h.2.1,h.2.2.1,h.2.2.2]
    exact witness_active_value

/-- The zero phase is an actual minimax certificate with the same T and t. -/
theorem example_inactive_certified :
    let M := exampleRegion 2 (by norm_num) le_rfl
    CertifiedValue M 0 ∧ phaseValueFull 9 M.p M.c M.e M.r = 0 := by
  dsimp only
  have hzero : phaseValueFull 9 (exampleRegion 2 (by norm_num) le_rfl).p
      (exampleRegion 2 (by norm_num) le_rfl).c (exampleRegion 2 (by norm_num) le_rfl).e
      (exampleRegion 2 (by norm_num) le_rfl).r = 0 := by
    have h := example_coefficients 2 (by norm_num) le_rfl
    dsimp only [p,r]
    rw [h.1,h.2.1,h.2.2.1,h.2.2.2]
    exact witness_inactive_value
  refine ⟨?_,hzero⟩
  have h := full_actual_minimax_certificates (exampleRegion 2 (by norm_num) le_rfl)
  have hc : CertifiedValue (exampleRegion 2 (by norm_num) le_rfl)
      (phaseValueFull 9 (exampleRegion 2 (by norm_num) le_rfl).p
        (exampleRegion 2 (by norm_num) le_rfl).c (exampleRegion 2 (by norm_num) le_rfl).e
        (exampleRegion 2 (by norm_num) le_rfl).r) := by
    simpa only [CertifiedValue, Nat.cast_ofNat, show (8:ℝ)+1=9 by norm_num] using h
  rwa [hzero] at hc

#print axioms region_certified_threshold
#print axioms physical_certified_threshold
#print axioms exampleT_mem
#print axioms example_coefficients
#print axioms example_threshold
#print axioms example_full_support
#print axioms example_active_certified
#print axioms example_inactive_certified
end
end CIGAMF.P13.D6ReferencePhysicalCertificate
