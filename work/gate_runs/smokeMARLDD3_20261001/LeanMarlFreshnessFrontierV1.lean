import Mathlib
import LeanMarlPriceOfCoverageV1

/-!
# H2, the necessity direction: at constant capacity EVERY one-step-fresh relay protocol pays the coverage price

`LeanMarlPriceOfCoverageV1` proved that the COVERING-HEAD schedule makes consecutive steps share a sender and so obeys
the larger injection floor.  The open question (ledger L-191, "the necessity direction decides whether the story
lives") was whether ANY protocol that keeps every receiver one step fresh must pay it.  It must.

**Causality.**  At step `t+1` receiver `i` can hold a copy of agent `j` at least as recent as `j`'s step-`t`
transmission only (a) by decoding `j` directly at `t+1`, (b) by having decoded `j` directly at `t`, or (c) by decoding at
`t+1` the packet of some `k` that decoded `j` directly at `t` — a packet sent at `t+1` carries what its sender knew at
the end of step `t`, and within one step no record travels two hops.  `CausalFresh` is exactly this requirement for
every receiver and every agent transmitted at `t`; any forwarding rule whatsoever (full tables, news, slots, memory) can
only meet it through these routes.

## WHAT IS PROVED
* `fresh_forces_share` — on the prefix channel at constant capacity `K ≥ 1` with at least `K + 2` agents, if step `t`
  is one-step fresh then some sender is transmitted at both `t` and `t + 1`.  The agent at position `K` is decoded at
  `t` only by the prefix; the receiver at position `K + 1` must get it through a relayer that decoded it at `t`, which
  sits in the prefix of `t`, hence was transmitted at `t`, and is decoded at `t+1`, hence transmitted at `t+1`.
* `fresh_floor` — **the price**: a protocol that is one-step fresh at every step obeys
  `∑_{s ≤ t} (m − (K+1) − sK)₊ ≤ ∑_j f_t(j)` (via `coverage_floor`, `hub_card`), whatever its ordering and relay rule.
  At `K = 1` this is `28/9` on `m = 9` and `105/16` on `m = 16` (`coverage_floor_nine/_sixteen`), against the age-first
  floors `16/9` and `56/16`: one-step freshness at every receiver and the minimum injection age are incompatible.
* `fresh_witness` — the hypotheses are satisfiable: a three-agent rotation step at `K = 1` is one-step fresh.

## WHAT THIS DOES NOT ESTABLISH
- Achievability of the larger floor by a specific protocol (the replica's covering-head numbers are measured, not proved).
- Anything for non-constant capacities: with a rich receiver outside the prefix the price vanishes (`rich_cover_free`).
-/

namespace CIGAMF.P13.MarlFreshnessFrontier

open Finset
open CIGAMF.P13.MarlRelayOneHop (prefixDecoded)
open CIGAMF.P13.MarlPrefixThreshold (threshold)
open CIGAMF.P13.MarlPriceOfCoverage (tx mem_tx coverage_floor hub_card)
open CIGAMF.P13.MarlInjectionFloor (injAge)

variable {m : ℕ}

/-- The decoded set of receiver `i` at step `t` on the prefix channel at constant capacity `K`. -/
def D (pos : ℕ → Fin m → ℕ) (K t : ℕ) (i : Fin m) : Finset (Fin m) :=
  prefixDecoded (pos t) (threshold (pos t) K) i

/-- The transmitted set at step `t`. -/
def T (pos : ℕ → Fin m → ℕ) (K t : ℕ) : Finset (Fin m) := tx (pos t) (threshold (pos t) K)

/-- **One-step freshness, causally.**  Every agent transmitted at `t` reaches every other receiver by `t + 1` through a
direct decode at `t + 1` or `t`, or one relay hop at `t + 1` from a sender that decoded it directly at `t`. -/
def CausalFresh (pos : ℕ → Fin m → ℕ) (K t : ℕ) : Prop :=
  ∀ i j : Fin m, j ≠ i → j ∈ T pos K t →
    j ∈ D pos K (t + 1) i ∨ j ∈ D pos K t i ∨ ∃ k ∈ D pos K (t + 1) i, j ∈ D pos K t k

theorem mem_D {pos : ℕ → Fin m → ℕ} {K t : ℕ} {i j : Fin m} :
    j ∈ D pos K t i ↔ j ≠ i ∧ pos t j < threshold (pos t) K i := by
  simp [D, prefixDecoded]

theorem mem_T_of_D {pos : ℕ → Fin m → ℕ} {K t : ℕ} {i j : Fin m} (h : j ∈ D pos K t i) : j ∈ T pos K t := by
  unfold T; rw [mem_tx]
  exact ⟨i, (mem_D.mp h).1, (mem_D.mp h).2⟩

/-- **One-step freshness forces a shared sender.** -/
theorem fresh_forces_share (pos : ℕ → Fin m → ℕ) (K : ℕ) (hK : 1 ≤ K) (t : ℕ)
    (a0 aK aK1 : Fin m) (h0 : pos t a0 = 0) (hk : pos t aK = K) (hk1 : pos t aK1 = K + 1)
    (hfresh : CausalFresh pos K t) : ∃ k, k ∈ T pos K t ∧ k ∈ T pos K (t + 1) := by
  -- the agent at position K is transmitted (the head decodes it)
  have hjT : aK ∈ T pos K t := by
    unfold T; rw [mem_tx]
    refine ⟨a0, fun h => by rw [h, h0] at hk; omega, ?_⟩
    unfold threshold; rw [if_pos (by omega)]; omega
  have hij : aK ≠ aK1 := fun h => by rw [h, hk1] at hk; omega
  -- the receiver at position K + 1 does not decode it at t
  have hnot : aK ∉ D pos K t aK1 := by
    rw [mem_D]; rintro ⟨-, hlt⟩
    unfold threshold at hlt; rw [if_neg (by omega)] at hlt; omega
  rcases hfresh aK1 aK hij hjT with h | h | ⟨k, hk', hjk⟩
  · exact ⟨aK, hjT, mem_T_of_D h⟩
  · exact absurd h hnot
  · -- the relayer decoded the position-K agent at t, so it sits in the prefix of t
    have hkpos : pos t k < K := by
      have := (mem_D.mp hjk).2
      unfold threshold at this; split_ifs at this with hc
      · exact hc
      · omega
    refine ⟨k, ?_, mem_T_of_D hk'⟩
    unfold T; rw [mem_tx]
    refine ⟨aK1, fun h => by rw [h, hk1] at hkpos; omega, ?_⟩
    unfold threshold; rw [if_neg (by omega)]; exact hkpos

/-- **The price of one-step freshness.**  A protocol that is one-step fresh at every step pays the coverage floor. -/
theorem fresh_floor (pos : ℕ → Fin m → ℕ) (K : ℕ) (hK : 1 ≤ K) (hinj : ∀ t, Function.Injective (pos t))
    (a0 aK aK1 : ℕ → Fin m) (h0 : ∀ t, pos t (a0 t) = 0) (hk : ∀ t, pos t (aK t) = K)
    (hk1 : ∀ t, pos t (aK1 t) = K + 1) (hfresh : ∀ t, CausalFresh pos K t) (t : ℕ) :
    ∑ s ∈ range (t + 1), (m - ((K + 1) + s * (K + 1 - 1))) ≤ ∑ j, injAge (fun u => T pos K u) t j :=
  coverage_floor (fun u => T pos K u) (K + 1) (fun u => hub_card K (pos u) (hinj u))
    (fun u => fresh_forces_share pos K hK u (a0 u) (aK u) (aK1 u) (h0 u) (hk u) (hk1 u) (hfresh u)) t

/-! ## The hypotheses are satisfiable -/

/-- Step 0 orders the agents `0, 1, 2`; step 1 orders them `1, 2, 0`. -/
def wPos (t : ℕ) (j : Fin 3) : ℕ := if t = 0 then j.val else ((j : Fin 3) - 1 : Fin 3).val

/-- **A one-step-fresh rotation step** (three agents, `K = 1`). -/
theorem fresh_witness : CausalFresh wPos 1 0 := by
  unfold CausalFresh
  decide

end CIGAMF.P13.MarlFreshnessFrontier

#print axioms CIGAMF.P13.MarlFreshnessFrontier.mem_D
#print axioms CIGAMF.P13.MarlFreshnessFrontier.mem_T_of_D
#print axioms CIGAMF.P13.MarlFreshnessFrontier.fresh_forces_share
#print axioms CIGAMF.P13.MarlFreshnessFrontier.fresh_floor
#print axioms CIGAMF.P13.MarlFreshnessFrontier.fresh_witness
