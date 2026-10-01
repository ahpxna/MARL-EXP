import Mathlib
import LeanMarlRelayOneHopV1
import LeanMarlAgeFirstInjectionV1

/-!
# The age-first head breaks the one-step bound; the covering head restores it (paper_marl_v2, Claim onehop, replica)

`LeanMarlRelayOneHopV1.one_hop` needs three hypotheses on the head sequence: the head is decoded by everybody, the
next head covers the step, consecutive heads differ.  The replica (`scripts/MARL_e3_math_replica.py`, ledger L-181)
finds the lower bound violated in 7–38% of checks under the AGE-FIRST head and never under the covering (hub) head.
This module gives the smallest exact instance.

Four agents, capacity `K = 1`, prefix decoding in the threshold form (`r = K + [pos < K]`):
* step 0, order `(0, 1, 2, 3)`: receivers `1, 2, 3` decode `0`, receiver `0` decodes `1`; agents `0, 1` are sent;
* step 1, the AGE-FIRST order `(2, 3, 0, 1)` (agents `2, 3` never sent come first, ties by index): head `2`.

## WHAT IS PROVED
* `agefirst_step1_head` — `2` is the key-minimal sender at step `1` for the age-first key of
  `LeanMarlAgeFirstInjectionV1` (and `0` at step `0`): the order above IS the age-first order.
* `agefirst_breaks_one_hop` — the head `2` is decoded by every other receiver at step `1` and differs from the step-0
  head, but it did not cover step `0` (it did not decode agent `1`), and the one-step lower bound FAILS: agent `1` was
  transmitted at step `0` (`lastTx = 1`) and receiver `3` holds no copy of it after step `1` (table `= 0`).
* `cover_head_restores` — with the covering receiver of step `0` (agent `1`) as the step-1 head, order `(1, 2, 3, 0)`,
  the lower bound holds for every receiver other than the head and every agent.

## WHAT THIS DOES NOT ESTABLISH
- How often the bound fails under age-first in E3: that is the replica's measurement (7–38%), not a theorem.
-/

namespace CIGAMF.P13.MarlAgeFirstBreaksOneHop

open Finset
open CIGAMF.P13.MarlRelayOneHop

/-- Positions at step 0: the order `(0, 1, 2, 3)`. -/
def pos0 (j : Fin 4) : ℕ := j.val

/-- Positions at step 1 under the age-first order `(2, 3, 0, 1)`. -/
def pos1 (j : Fin 4) : ℕ := (j.val + 2) % 4

/-- Positions at step 1 with the covering head first: the order `(1, 2, 3, 0)`. -/
def pos1c (j : Fin 4) : ℕ := (j.val + 3) % 4

/-- The threshold `K + [pos < K]` with `K = 1`. -/
def thr (pos : Fin 4 → ℕ) (i : Fin 4) : ℕ := if pos i < 1 then 2 else 1

/-- Decoded sets: step 0 with `pos0`, every later step with `p1`. -/
def sched (p1 : Fin 4 → ℕ) (t : ℕ) (i : Fin 4) : Finset (Fin 4) :=
  if t = 0 then prefixDecoded pos0 (thr pos0) i else prefixDecoded p1 (thr p1) i

/-- Transmitted sets. -/
def tx (p1 : Fin 4 → ℕ) (t : ℕ) : Finset (Fin 4) := univ.biUnion (sched p1 t)

/-- The orders used are the age-first orders: `0` is key-minimal at step `0` and `2` at step `1`. -/
theorem agefirst_step1_head :
    (∀ j : Fin 4, j ≠ 0 → CIGAMF.P13.MarlAgeFirstInjection.key (tx pos1) 0 0 <
        CIGAMF.P13.MarlAgeFirstInjection.key (tx pos1) 0 j) ∧
    (∀ j : Fin 4, j ≠ 2 → CIGAMF.P13.MarlAgeFirstInjection.key (tx pos1) 1 2 <
        CIGAMF.P13.MarlAgeFirstInjection.key (tx pos1) 1 j) := by
  decide

/-- **The age-first head breaks the one-step bound.** -/
theorem agefirst_breaks_one_hop :
    (∀ i : Fin 4, i ≠ 2 → (2 : Fin 4) ∈ sched pos1 1 i) ∧ (2 : Fin 4) ≠ 0 ∧
    (1 : Fin 4) ∈ tx pos1 0 ∧ (1 : Fin 4) ∉ sched pos1 0 2 ∧
    lastTx (sched pos1) 0 1 = 1 ∧ table (sched pos1) 1 3 1 = 0 := by
  decide

/-- **The covering head restores it** (at the same step, for every receiver other than the head and every agent). -/
theorem cover_head_restores :
    (∀ j : Fin 4, j ∈ tx pos1c 0 → j ≠ 1 → j ∈ sched pos1c 0 1) ∧
    ∀ i j : Fin 4, i ≠ 1 → lastTx (sched pos1c) 0 j ≤ table (sched pos1c) 1 i j := by
  decide

end CIGAMF.P13.MarlAgeFirstBreaksOneHop

#print axioms CIGAMF.P13.MarlAgeFirstBreaksOneHop.agefirst_step1_head
#print axioms CIGAMF.P13.MarlAgeFirstBreaksOneHop.agefirst_breaks_one_hop
#print axioms CIGAMF.P13.MarlAgeFirstBreaksOneHop.cover_head_restores
