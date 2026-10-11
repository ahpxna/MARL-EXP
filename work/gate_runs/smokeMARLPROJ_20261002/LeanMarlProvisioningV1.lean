import Mathlib
import LeanMarlNetFloorV1

/-!
# The provisioning rule (rule A) is a corollary of the net floor

PROTOCOL_E3_NET_COUNT_20261001 Part 3 (rule A) and ledger L-240: empirically, the gain of relay over compiled silence is
positive iff the channel-only count `net / (m − 1) = (fresh − stale_τ) / (m − 1)` exceeds a threshold `θ` (frozen at
`θ = −0.08` on the 3×3 cells; 4/4 known cells), with `τ` the receiver's training age range.  Rule A says: at constant
capacity `K`, no scheduler can put the receiver on the positive side unless `K > K_min = (1 + θ)(m − 1)/(τ + 2)`.  This file
proves the channel half of that statement from `LeanMarlNetFloorV1.net_floor` (fresh + (m − 1) ≤ K (τ + 2) + stale_τ).

## WHAT IS PROVED
* `net_le` — net = fresh − stale_τ ≤ K (τ + 2) − (m − 1) in ℝ, for every scheduler, receiver and step `t ≥ τ + 1`.
* `provisioning` — if `K (τ + 2) ≤ (1 + θ)(m − 1)` then `net ≤ θ (m − 1)` for EVERY scheduler: the count can never exceed
  the threshold; `provisioning_div` — the same with `K ≤ K_min = (1 + θ)(m − 1)/(τ + 2)`.
* `kmin_antitone` — `K_min` falls as the training range `τ` grows (for `1 + θ ≥ 0`): a receiver trained on staler copies
  needs less capacity (the training-relative reading: 3×3 iid-trained τ = 2 gives K_min 1.84; K = 1-trained τ = 8 gives 0.74).
* `provisioning_witness` — the hypotheses are satisfiable and the bound is attained: three agents, `K = 1`, `τ = 0`,
  `θ = 0`: `K (τ + 2) = 2 = (1 + θ)(m − 1)` and the receiver of the net-floor witness has `net = 0 = θ (m − 1)`.

## WHAT THIS DOES NOT ESTABLISH
- That the gain follows the count (the sign rule is empirical, L-239 / L-240); only that the channel caps the count.
- Sufficiency: `K > K_min` does not make the gain positive (the scheduler must also attain the floor, and the receiver's
  other limits apply).
-/

namespace CIGAMF.P13.MarlProvisioningV1

open Finset CIGAMF.P13.MarlReceiverFloor CIGAMF.P13.MarlNetFloorV1

variable {α : Type*} [DecidableEq α] [Fintype α] (sch : ℕ → Step α)

/-- fresh senders at receiver `i`, time `t` -/
noncomputable def fresh (t : ℕ) (i : α) : ℕ := ((univ.filter (fun j => t ≤ tk sch t i j)).erase i).card
/-- senders whose freshest copy is older than `τ` steps (or never heard) -/
noncomputable def stale (t τ : ℕ) (i : α) : ℕ := ((univ.erase i).filter (fun j => tk sch t i j ≤ t - (τ + 1))).card

theorem net_le (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (t τ : ℕ) (hτ : τ + 1 ≤ t) (i : α) (hm : 1 ≤ Fintype.card α) :
    (fresh sch t i : ℝ) - stale sch t τ i ≤ (K : ℝ) * (τ + 2) - ((Fintype.card α : ℝ) - 1) := by
  have h := net_floor sch K hK t τ hτ i
  have h' : ((fresh sch t i + (Fintype.card α - 1) : ℕ) : ℝ) ≤ ((K * (τ + 2) + stale sch t τ i : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast [Nat.cast_sub hm] at h'
  linarith

theorem provisioning (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (t τ : ℕ) (hτ : τ + 1 ≤ t) (i : α) (hm : 1 ≤ Fintype.card α)
    (θ : ℝ) (hcap : (K : ℝ) * (τ + 2) ≤ (1 + θ) * ((Fintype.card α : ℝ) - 1)) :
    (fresh sch t i : ℝ) - stale sch t τ i ≤ θ * ((Fintype.card α : ℝ) - 1) := by
  have h := net_le sch K hK t τ hτ i hm
  have e : (1 + θ) * ((Fintype.card α : ℝ) - 1) = ((Fintype.card α : ℝ) - 1) + θ * ((Fintype.card α : ℝ) - 1) := by ring
  linarith

theorem provisioning_div (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (t τ : ℕ) (hτ : τ + 1 ≤ t) (i : α) (hm : 1 ≤ Fintype.card α)
    (θ : ℝ) (hkmin : (K : ℝ) ≤ (1 + θ) * ((Fintype.card α : ℝ) - 1) / ((τ : ℝ) + 2)) :
    (fresh sch t i : ℝ) - stale sch t τ i ≤ θ * ((Fintype.card α : ℝ) - 1) := by
  have hpos : (0 : ℝ) < (τ : ℝ) + 2 := by positivity
  have hcap : (K : ℝ) * (τ + 2) ≤ (1 + θ) * ((Fintype.card α : ℝ) - 1) := by
    rw [le_div_iff₀ hpos] at hkmin; exact_mod_cast hkmin
  exact provisioning sch K hK t τ hτ i hm θ hcap

theorem kmin_antitone (m θ : ℝ) (hm : 1 ≤ m) (hθ : 0 ≤ 1 + θ) (τ τ' : ℕ) (h : τ ≤ τ') :
    (1 + θ) * (m - 1) / ((τ' : ℝ) + 2) ≤ (1 + θ) * (m - 1) / ((τ : ℝ) + 2) := by
  have hnum : 0 ≤ (1 + θ) * (m - 1) := mul_nonneg hθ (by linarith)
  have h1 : (0 : ℝ) < (τ : ℝ) + 2 := by positivity
  have h2 : ((τ : ℝ) + 2) ≤ (τ' : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right h 2
  exact div_le_div_of_nonneg_left hnum h1 h2

/-- Satisfiable and attained: the net-floor witness (three agents, `K = 1`, receiver 2, `t = 1`, `τ = 0`) with `θ = 0`. -/
theorem provisioning_witness :
    ((1 : ℕ) : ℝ) * ((0 : ℕ) + 2) ≤ (1 + 0) * ((Fintype.card (Fin 3) : ℝ) - 1) ∧
      (fresh witness 1 (2 : Fin 3) : ℝ) - stale witness 1 0 (2 : Fin 3) = 0 * ((Fintype.card (Fin 3) : ℝ) - 1) := by
  have hf : fresh witness 1 (2 : Fin 3) = 1 := by unfold fresh; decide
  have hs : stale witness 1 0 (2 : Fin 3) = 1 := by unfold stale; decide
  refine ⟨by norm_num, ?_⟩
  rw [hf, hs]; norm_num

end CIGAMF.P13.MarlProvisioningV1

#print axioms CIGAMF.P13.MarlProvisioningV1.net_le
#print axioms CIGAMF.P13.MarlProvisioningV1.provisioning
#print axioms CIGAMF.P13.MarlProvisioningV1.provisioning_div
#print axioms CIGAMF.P13.MarlProvisioningV1.kmin_antitone
#print axioms CIGAMF.P13.MarlProvisioningV1.provisioning_witness
