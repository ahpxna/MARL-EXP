import Mathlib
import LeanMarlProvisioningV1

/-!
# The provisioning constants quoted for the 3×3 and 4×4 networks, and rule A on the 16-agent network at K = 1

Ledger L-240 / L-270: K_min = (1 + θ)(m − 1)/(τ_train + 2) with θ = −0.08 gives 1.84 (3×3, iid-trained, τ = 2), 0.736 (3×3,
K = 1-trained, τ = 8), 1.2545… (4×4, iid-trained, training-relative τ = 9) and 3.45 (4×4 with the absolute τ = 2); the 4×4
const-K target confirmed the training-relative version prospectively (K1 negative, K2 / K3 positive).

## WHAT IS PROVED
* `kmin_3x3_iid`, `kmin_3x3_k1`, `kmin_4x4_rel`, `kmin_4x4_abs` — the four constants (exact rationals).
* `k1_forced_4x4` — at K = 1 the cap condition of `provisioning` holds on 16 agents with τ = 9 and θ = −0.08
  (1 · 11 ≤ 0.92 · 15), so `rule_a_4x4_k1`: for EVERY scheduler on 16 agents at constant capacity 1, every receiver at every
  step t ≥ 10 has (fresh − stale_9) ≤ −0.08 · 15 — the training-relative count can never cross the frozen threshold.
* `k2_not_forced_4x4` — at K = 2 the cap condition fails (2 · 11 > 13.8): rule A does not force the sign (as observed, K2
  was positive), while with the absolute τ = 2 it would (`k2_forced_4x4_abs`: 2 · 4 ≤ 13.8) — the version the data refuted.

## WHAT THIS DOES NOT ESTABLISH
- The empirical link between the count and the gain (L-239, L-240, L-270).
-/

namespace CIGAMF.P13.MarlProvisioningInstancesV1

open CIGAMF.P13.MarlReceiverFloor CIGAMF.P13.MarlProvisioningV1

theorem kmin_3x3_iid : (1 + (-0.08 : ℝ)) * (9 - 1) / ((2 : ℝ) + 2) = 1.84 := by norm_num
theorem kmin_3x3_k1 : (1 + (-0.08 : ℝ)) * (9 - 1) / ((8 : ℝ) + 2) = 0.736 := by norm_num
theorem kmin_4x4_rel : (1 + (-0.08 : ℝ)) * (16 - 1) / ((9 : ℝ) + 2) = 13.8 / 11 := by norm_num
theorem kmin_4x4_abs : (1 + (-0.08 : ℝ)) * (16 - 1) / ((2 : ℝ) + 2) = 3.45 := by norm_num

theorem k1_forced_4x4 : ((1 : ℕ) : ℝ) * ((9 : ℕ) + 2) ≤ (1 + (-0.08 : ℝ)) * ((Fintype.card (Fin 16) : ℝ) - 1) := by
  simp; norm_num

theorem rule_a_4x4_k1 (sch : ℕ → Step (Fin 16)) (hK : ∀ s, (sch s).P.card ≤ 1) (t : ℕ) (ht : 9 + 1 ≤ t) (i : Fin 16) :
    (fresh sch t i : ℝ) - stale sch t 9 i ≤ (-0.08 : ℝ) * ((Fintype.card (Fin 16) : ℝ) - 1) :=
  provisioning sch 1 hK t 9 ht i (by simp) (-0.08) k1_forced_4x4

theorem k2_not_forced_4x4 : ¬ (((2 : ℕ) : ℝ) * ((9 : ℕ) + 2) ≤ (1 + (-0.08 : ℝ)) * ((Fintype.card (Fin 16) : ℝ) - 1)) := by
  simp; norm_num

theorem k2_forced_4x4_abs : ((2 : ℕ) : ℝ) * ((2 : ℕ) + 2) ≤ (1 + (-0.08 : ℝ)) * ((Fintype.card (Fin 16) : ℝ) - 1) := by
  simp; norm_num

end CIGAMF.P13.MarlProvisioningInstancesV1

#print axioms CIGAMF.P13.MarlProvisioningInstancesV1.kmin_4x4_rel
#print axioms CIGAMF.P13.MarlProvisioningInstancesV1.rule_a_4x4_k1
#print axioms CIGAMF.P13.MarlProvisioningInstancesV1.k2_not_forced_4x4
#print axioms CIGAMF.P13.MarlProvisioningInstancesV1.k2_forced_4x4_abs
