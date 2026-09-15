import «LeanD6ReferencePhysicalBoundsV1»
import «LeanD6ReferencePhaseThresholdV1»

/-! # D05/D06: the phase threshold as an iff, and a non-empty witness.

Two things a minimax certificate on `Region q j T` still needs before it is a
research result rather than a vacuous implication.

## 1. The threshold is an iff on the value, not a one-sided collapse

`LeanD6ReferencePhaseValueV1` proves `phaseValueFull = 0` when `k*r ≤ e`, and
`LeanD6ReferencePhaseThresholdV1` proves `0 < phaseValueFull ↔ e < k*r`.
`phase_value_zero_iff` below closes the remaining direction by first proving the
value is never negative on the region, giving

    phaseValueFull k p c e r = 0  ↔  rho ≥ rho_star,     rho_star = 2a - e/k,

with `r = 2a - rho`. Both branches of every downstream theorem are therefore
reachable, and `rho_star` is exact at finite `k`.

## 2. The region is inhabited — but only from `q = 8`

`LeanD6ReferencePhysicalBoundsV1` removed `hp` but left `strong`, and `strong`
is a genuine size restriction. The witness formalised here is the exact rational
point

    q = 8,  k = q+1 = 9,  t = 1/25,  z = (24/25)^16,

for which, on ANY `T ∈ worlds 8 j` (all of them have `|T| = 9`,
`|others T j| = 8`, so the reference coefficients do not depend on which world
is picked):

    a = gateMass  = (32/25) z,     b = slopeBval = (7/25) z,
    e = min a (2b) = (14/25) z,    c = a - b = z,
    (q-1) b = (49/25) z > 1   -- `strong` holds,
    rho_star = 2a - e/k = (562/225) z,  and  1 < rho_star < 2.

Because `rho_star` lies strictly inside `[1,2]`, the SAME reference exhibits both
phases, which is what makes the two-branch threshold testable rather than
decorative:

* `rho = 1` : `e < k*r`, the minimax value is strictly positive;
* `rho = 2` : `k*r ≤ e`, the minimax value is exactly `0`.

Note that `rho = 2` also fails `hact`, so it exercises the INACTIVE branch and
is deliberately NOT covered by `actual_dual_lower` / `randomized_dual_lower`.

## What this does NOT establish

* It does not show the region is non-empty for any `q ≠ 8`; `q ≤ 7` is empty by
  a floating-point grid scan recorded in
  `research/high_risk_20260910/D05_REGION_SIZE_AND_PHYSICAL_BOUNDS_20260912.md`,
  which is NUMERICAL EVIDENCE, not a theorem here.
* It does not remove `strong`.
* `rho_star` is the threshold of the VALUE FORMULA. Calling it the actual
  minimax threshold requires the matching certificates, which live in
  `LeanD6ReferenceMatchingMinimaxV1` / `LeanD6ReferenceCertifiedPhaseValueV1`.
-/

namespace CIGAMF.P13.D6ReferencePhaseWitness
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceResponseJoin CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.P13.D6ReferenceRetainedOscillation CIGAMF.P13.D6ReferenceEndpointWorlds
open CIGAMF.P13.D6ReferencePhysicalBounds
open CIGAMF.P13.D6ReferencePhaseValue CIGAMF.P13.D6ReferencePhaseThreshold
noncomputable section

/-! ## 1. The threshold, as an iff -/

theorem phaseValueFull_nonneg (k p c e r : ℝ) (hk : 1 < k) (hp : 0 < p) (hc : 0 < c) :
    0 ≤ phaseValueFull k p c e r := by
  have hk1 : (0:ℝ) < k-1 := by linarith
  have h1 : (0:ℝ) ≤ max 0 (k*r-e) := le_max_left _ _
  have hm : (0:ℝ) ≤ max 0 (e-r) := le_max_left _ _
  have h2 : (0:ℝ) ≤ p*(k-1)+max 0 (e-r) := by
    have := mul_pos hp hk1
    linarith
  have h3 : (0:ℝ) < 4*(c*(k-1)) := by
    have := mul_pos hc hk1
    linarith
  unfold phaseValueFull
  exact div_nonneg (mul_nonneg h1 h2) h3.le

/-- The exact finite-`k` phase threshold, in the margin variable. -/
theorem phase_value_zero_iff (k p c e r a rho : ℝ) (hk : 1 < k) (hp : 0 < p) (hc : 0 < c)
    (hr : r = 2*a-rho) :
    phaseValueFull k p c e r = 0 ↔ 2*a-e/k ≤ rho := by
  have hk0 : (0:ℝ) < k := by linarith
  have hpos := phaseValueFull_pos_iff k p c e r hk hp hc
  have hnn := phaseValueFull_nonneg k p c e r hk hp hc
  constructor
  · intro h0
    by_contra hcon
    push_neg at hcon
    have h1 : e < k*r := by
      rw [hr]
      exact (threshold_margin k a e rho hk0).mpr hcon
    have h2 := hpos.mpr h1
    rw [h0] at h2
    exact lt_irrefl 0 h2
  · intro hge
    by_contra h0
    have h2 : 0 < phaseValueFull k p c e r := lt_of_le_of_ne hnn (Ne.symm h0)
    have h3 := hpos.mp h2
    rw [hr] at h3
    have h4 := (threshold_margin k a e rho hk0).mp h3
    linarith

/-! ## 2. The reference coefficients at `q = 8`, `t = 1/25` -/

variable (j : I (2*8+1))

theorem witness_cards (T : Finset (I (2*8+1))) (hT : T ∈ worlds 8 j) :
    T.card = 9 ∧ (others T j).card = 8 := by
  have hp := world_parameters 8 j (by norm_num) hT
  have h9 : T.card = 9 := hp.2.1
  have hB : (others T j).card = Tᶜ.card-1 := by
    unfold others
    rw [Finset.card_erase_of_mem (by simp [hp.1])]
    rfl
  refine ⟨h9,?_⟩
  rw [hB,hp.2.2.1,h9]

theorem gateMass_witness (T : Finset (I (2*8+1))) (hT : T ∈ worlds 8 j) :
    gateMass (1/25 : ℝ) T j = 32/25*((24/25:ℝ)^16) := by
  have hc := witness_cards j T hT
  unfold gateMass tailFactor
  rw [hc.1,hc.2,show (8:ℕ)-1 = 7 from rfl]
  push_cast
  ring

theorem slopeBval_witness (T : Finset (I (2*8+1))) (hT : T ∈ worlds 8 j) :
    slopeBval (1/25 : ℝ) T j = 7/25*((24/25:ℝ)^16) := by
  have hc := witness_cards j T hT
  unfold slopeBval
  rw [hc.1,hc.2,show (9:ℕ)+8-1 = 16 from rfl]
  push_cast
  ring

/-- `strong` holds at the witness: `(q-1)*b = (49/25)*(24/25)^16 > 1`. -/
theorem strong_witness (T : Finset (I (2*8+1))) (hT : T ∈ worlds 8 j) :
    1 ≤ (((8:ℕ):ℝ)-1)*slopeBval (1/25 : ℝ) T j := by
  rw [slopeBval_witness j T hT]
  norm_num

/-! ## 3. A concrete inhabited Region at `q = 8`, in both phases -/

def Twit : Finset (I (2*8+1)) := (worlds_nonempty 8 j).choose

theorem Twit_mem : Twit j ∈ worlds 8 j := (worlds_nonempty 8 j).choose_spec

def Mwit (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho ≤ 2) : Region 8 j (Twit j) :=
  physicalRegion 8 j (Twit j) (1/25) rho (by norm_num) (Twit_mem j)
    (by norm_num) (by norm_num) hr hr2 (strong_witness j (Twit j) (Twit_mem j))

theorem Mwit_a (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    (Mwit j rho hr hr2).a = 32/25*((24/25:ℝ)^16) := by
  show gateMass (1/25 : ℝ) (Twit j) j = _
  exact gateMass_witness j (Twit j) (Twit_mem j)

theorem Mwit_b (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    (Mwit j rho hr hr2).b = 7/25*((24/25:ℝ)^16) := by
  show slopeBval (1/25 : ℝ) (Twit j) j = _
  exact slopeBval_witness j (Twit j) (Twit_mem j)

theorem Mwit_e (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    (Mwit j rho hr hr2).e = 14/25*((24/25:ℝ)^16) := by
  show min ((Mwit j rho hr hr2).a) (2*(Mwit j rho hr hr2).b) = _
  rw [Mwit_a j rho hr hr2,Mwit_b j rho hr hr2]
  rw [min_eq_right (by norm_num)]
  ring

theorem Mwit_c (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    (Mwit j rho hr hr2).c = ((24/25:ℝ)^16) := by
  show (Mwit j rho hr hr2).a-(Mwit j rho hr hr2).b = _
  rw [Mwit_a j rho hr hr2,Mwit_b j rho hr hr2]
  ring

theorem Mwit_r (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    (Mwit j rho hr hr2).r = 2*(32/25*((24/25:ℝ)^16))-rho := by
  show 2*(Mwit j rho hr hr2).a-(Mwit j rho hr hr2).rho = _
  rw [Mwit_a j rho hr hr2]
  rfl

theorem Mwit_p (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho ≤ 2) :
    (Mwit j rho hr hr2).p = rho-2*(7/25*((24/25:ℝ)^16)) := by
  show (Mwit j rho hr hr2).rho-2*(Mwit j rho hr hr2).b = _
  rw [Mwit_b j rho hr hr2]
  rfl

/-- The threshold at the witness reference lies STRICTLY inside `[1,2]`, so the
same reference realises both phases. -/
theorem witness_threshold_strictly_inside :
    (1:ℝ) < 2*(32/25*((24/25:ℝ)^16))-(14/25*((24/25:ℝ)^16))/9 ∧
      2*(32/25*((24/25:ℝ)^16))-(14/25*((24/25:ℝ)^16))/9 < 2 := by
  constructor <;> norm_num

/-- Active phase at `rho = 1`: the activity condition `e ≤ k*r` holds. -/
theorem witness_active_hact (hr : (1:ℝ) ≤ 1) (hr2 : (1:ℝ) ≤ 2) :
    (Mwit j 1 hr hr2).e ≤ ((8:ℝ)+1)*(Mwit j 1 hr hr2).r := by
  rw [Mwit_e j 1 hr hr2,Mwit_r j 1 hr hr2]
  norm_num

/-- Active phase at `rho = 1`: the minimax value is strictly positive. -/
theorem witness_active_value :
    0 < phaseValueFull 9 (1-2*(7/25*((24/25:ℝ)^16))) ((24/25:ℝ)^16)
      (14/25*((24/25:ℝ)^16)) (2*(32/25*((24/25:ℝ)^16))-1) :=
  (phaseValueFull_pos_iff 9 _ _ _ _ (by norm_num) (by norm_num) (by norm_num)).mpr
    (by norm_num)

/-- Inactive phase at `rho = 2`: the minimax value is exactly zero. -/
theorem witness_inactive_value :
    phaseValueFull 9 (2-2*(7/25*((24/25:ℝ)^16))) ((24/25:ℝ)^16)
      (14/25*((24/25:ℝ)^16)) (2*(32/25*((24/25:ℝ)^16))-2) = 0 :=
  phaseValueFull_zero 9 _ _ _ _ (by norm_num)

/-- Inactive phase at `rho = 2`: `hact` FAILS, so the active-phase certificates
are genuinely inapplicable there; this is the other branch, not a gap. -/
theorem witness_inactive_not_hact (hr : (1:ℝ) ≤ 2) (hr2 : (2:ℝ) ≤ 2) :
    ¬ ((Mwit j 2 hr hr2).e ≤ ((8:ℝ)+1)*(Mwit j 2 hr hr2).r) := by
  rw [Mwit_e j 2 hr hr2,Mwit_r j 2 hr hr2]
  norm_num

/-- The region is inhabited at `q = 8`, in the active phase. -/
theorem region_nonempty_active :
    ∃ (j : I (2*8+1)) (T : Finset (I (2*8+1))) (M : Region 8 j T),
      M.t = 1/25 ∧ M.rho = 1 ∧ M.e ≤ ((8:ℝ)+1)*M.r :=
  ⟨0,Twit 0,Mwit 0 1 le_rfl (by norm_num),rfl,rfl,
    witness_active_hact 0 le_rfl (by norm_num)⟩

/-- The region is inhabited at `q = 8`, in the inactive phase. -/
theorem region_nonempty_inactive :
    ∃ (j : I (2*8+1)) (T : Finset (I (2*8+1))) (M : Region 8 j T),
      M.t = 1/25 ∧ M.rho = 2 ∧ ¬ (M.e ≤ ((8:ℝ)+1)*M.r) :=
  ⟨0,Twit 0,Mwit 0 2 (by norm_num) le_rfl,rfl,rfl,
    witness_inactive_not_hact 0 (by norm_num) le_rfl⟩

#print axioms phaseValueFull_nonneg
#print axioms phase_value_zero_iff
#print axioms witness_cards
#print axioms gateMass_witness
#print axioms slopeBval_witness
#print axioms strong_witness
#print axioms Twit_mem
#print axioms Mwit_a
#print axioms Mwit_b
#print axioms Mwit_e
#print axioms Mwit_c
#print axioms Mwit_r
#print axioms Mwit_p
#print axioms witness_threshold_strictly_inside
#print axioms witness_active_hact
#print axioms witness_active_value
#print axioms witness_inactive_value
#print axioms witness_inactive_not_hact
#print axioms region_nonempty_active
#print axioms region_nonempty_inactive

end
end CIGAMF.P13.D6ReferencePhaseWitness
