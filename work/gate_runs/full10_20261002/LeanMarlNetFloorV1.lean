import Mathlib
import LeanMarlReceiverFloorV1

/-!
# The net fresh-minus-stale count is bounded by the channel, for every scheduler

PROTOCOL_E3_NET_COUNT_20261001.md Part 2 (01/10/2026 23:4x EDT).  Empirically (ledger L-239) the per-receiver count
`net = fresh − stale_τ` (fresh = senders measured at the last step, stale_τ = senders whose freshest copy is older than τ
steps or absent) orders the value of communication across channels.  This file bounds it with the timed floor of
`LeanMarlReceiverFloorV1` at constant capacity `K`:

  fresh + (m − 1) ≤ K (τ + 2) + stale_τ,      i.e.   net ≤ K (τ + 2) − (m − 1),

for every scheduler, relay content and memory.  Never-heard senders have last-measured time 0 and are counted in stale_τ.

## WHAT IS PROVED
* `net_floor` — the inequality above, in ℕ, for every receiver `i`, step `t ≥ τ + 1`.
* `fresh_le` — at most `K` senders are fresh at any receiver (the case `n = 1` of `timed_floor`).
* `net_floor_witness` — the bound is attained with equality (V1's witness: three agents, K = 1, τ = 0), so the hypotheses
  are satisfiable.

## WHAT THIS DOES NOT ESTABLISH
- Anything about the value of communication: the link from `net` to the gain is empirical (L-239, PROTOCOL_E3_NET_COUNT).
- That a scheduler attains the bound (measured for age-first in the replica / CityFlow, not proved).
-/

namespace CIGAMF.P13.MarlNetFloorV1

open Finset CIGAMF.P13.MarlReceiverFloor

variable {α : Type*} [DecidableEq α] [Fintype α] (sch : ℕ → Step α)

/-- At most `K` senders are fresh (measured at the last step) at any receiver. -/
theorem fresh_le (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (t : ℕ) (ht : 1 ≤ t) (i : α) :
    ((univ.filter (fun j => t ≤ tk sch t i j)).erase i).card ≤ K := by
  have h := timed_floor sch K hK t 1 ht i
  simp only [Nat.sub_add_cancel ht, mul_one] at h
  exact h

/-- **Net floor.**  fresh + (m − 1) ≤ K (τ + 2) + stale_τ at every receiver, for every scheduler. -/
theorem net_floor (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (t τ : ℕ) (hτ : τ + 1 ≤ t) (i : α) :
    ((univ.filter (fun j => t ≤ tk sch t i j)).erase i).card + (Fintype.card α - 1) ≤
      K * (τ + 2) + ((univ.erase i).filter (fun j => tk sch t i j ≤ t - (τ + 1))).card := by
  have h1 := fresh_le sch K hK t (by omega) i
  have h2 := timed_forced_stale sch K hK t (τ + 1) hτ i
  have e : K * (τ + 2) = K * (τ + 1) + K := by ring
  rw [e]
  generalize K * (τ + 1) = A at h2 ⊢
  omega

/-- The bound is ATTAINED (so the hypotheses are satisfiable): V1's witness on three agents (`P = {0}`, `h = 1`, `K = 1`),
receiver 2 at `t = 1`, `τ = 0`: one fresh sender, one stale, `1 + 2 = 1 · 2 + 1`. -/
theorem net_floor_witness :
    (∀ s, (witness s).P.card ≤ 1) ∧
      ((univ.filter (fun j => 1 ≤ tk witness 1 (2 : Fin 3) j)).erase 2).card + (Fintype.card (Fin 3) - 1) =
        1 * (0 + 2) + ((univ.erase (2 : Fin 3)).filter (fun j => tk witness 1 2 j ≤ 1 - (0 + 1))).card := by
  refine ⟨fun s => by simp [witness], ?_⟩
  decide

end CIGAMF.P13.MarlNetFloorV1

#print axioms CIGAMF.P13.MarlNetFloorV1.fresh_le
#print axioms CIGAMF.P13.MarlNetFloorV1.net_floor
#print axioms CIGAMF.P13.MarlNetFloorV1.net_floor_witness
