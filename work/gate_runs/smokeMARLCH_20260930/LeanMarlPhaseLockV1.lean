import Mathlib

/-!
# The phase-lock of age-first ordering without relay (paper_marl_v2, Remark "Phase-lock")

Nine senders, every receiver decodes `K = 2` packets per step, raw one-sender packets, age-first ordering with ties
broken by index.  Under prefix decoding the transmitted set is the first `L = K + 1 = 3` positions (the receivers in
the first two positions skip themselves and read the third).  Those three become the newest and, tied, go last in index
order; the others keep their relative order.  So the order evolves by

    next(π) = drop 3 π ++ sort(take 3 π).

## WHAT IS PROVED
* `orders_periodic` — the order sequence is periodic with period 3 from the start.
* `transmitted_is_prefix` — at every step the union of the decoded sets is exactly the first three positions.
* `receiver0_never_decodes_5`, `receiver0_never_decodes_8` — receiver `0` never decodes senders `5` and `8`, at any
  step: the third member of each other triple is decoded only inside its triple.
* `never_covered_count` — each receiver misses exactly two of its eight senders forever (checked for every receiver),
  so 18 of the 72 ordered pairs, 25 %, are never covered: the replica's value and the formula `(m - L)/(L (m - 1))`.

## WHAT THIS DOES NOT ESTABLISH
- The general formula for `L` dividing `m`, or the non-divisible cases (numerical only).
- That relay removes the lock (true in the replica; not proved here).
-/

namespace CIGAMF.P13.MarlPhaseLock

/-- One age-first step (constant capacity `K = 2`, nine senders, index ties). -/
def nextOrder (π : List (Fin 9)) : List (Fin 9) := π.drop 3 ++ (π.take 3).insertionSort (· ≤ ·)

/-- The order at step `t`, starting from the index order (nobody transmitted yet). -/
def orderAt : ℕ → List (Fin 9)
  | 0 => List.finRange 9
  | t + 1 => nextOrder (orderAt t)

/-- Receiver `i` decodes the first `K = 2` senders of the order other than itself. -/
def decoded (π : List (Fin 9)) (i : Fin 9) : List (Fin 9) := (π.filter (· ≠ i)).take 2

theorem orderAt_three : orderAt 3 = orderAt 0 := by decide

theorem orders_periodic : ∀ t, orderAt (t + 3) = orderAt t := by
  intro t
  induction t with
  | zero => exact orderAt_three
  | succ t ih =>
      show nextOrder (orderAt (t + 3)) = nextOrder (orderAt t)
      rw [ih]

theorem orderAt_mod : ∀ t, orderAt t = orderAt (t % 3) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      by_cases ht : t < 3
      · rw [Nat.mod_eq_of_lt ht]
      · have h3 : t = (t - 3) + 3 := by omega
        rw [h3, orders_periodic, ih (t - 3) (by omega)]
        congr 1
        omega

theorem orderAt_cases (t : ℕ) : orderAt t = orderAt 0 ∨ orderAt t = orderAt 1 ∨ orderAt t = orderAt 2 := by
  rw [orderAt_mod t]
  have : t % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases (t % 3) <;> simp

/-- The transmitted set (union of the decoded sets) is the first three positions, at every step. -/
theorem transmitted_is_prefix (t : ℕ) (j : Fin 9) :
    (∃ i, j ∈ decoded (orderAt t) i) ↔ j ∈ (orderAt t).take 3 := by
  rcases orderAt_cases t with h | h | h <;> rw [h] <;> revert j <;> decide

theorem receiver0_never_decodes_5 (t : ℕ) : (5 : Fin 9) ∉ decoded (orderAt t) 0 := by
  rcases orderAt_cases t with h | h | h <;> rw [h] <;> decide

theorem receiver0_never_decodes_8 (t : ℕ) : (8 : Fin 9) ∉ decoded (orderAt t) 0 := by
  rcases orderAt_cases t with h | h | h <;> rw [h] <;> decide

/-- The senders receiver `i` decodes at some step of one period (every step's order is one of these three). -/
def everDecoded (i : Fin 9) : List (Fin 9) := decoded (orderAt 0) i ++ decoded (orderAt 1) i ++ decoded (orderAt 2) i

/-- Every receiver misses exactly two of its eight senders in a whole period, hence forever. -/
theorem never_covered_count :
    ∀ i : Fin 9, ((List.finRange 9).filter fun j => j ≠ i ∧ j ∉ everDecoded i).length = 2 := by
  decide

theorem never_covered_forever (t : ℕ) (i j : Fin 9) (hj : j ∉ everDecoded i) : j ∉ decoded (orderAt t) i := by
  intro hmem
  apply hj
  unfold everDecoded
  rcases orderAt_cases t with h | h | h <;> rw [h] at hmem <;> simp [hmem]

end CIGAMF.P13.MarlPhaseLock

#print axioms CIGAMF.P13.MarlPhaseLock.orders_periodic
#print axioms CIGAMF.P13.MarlPhaseLock.transmitted_is_prefix
#print axioms CIGAMF.P13.MarlPhaseLock.receiver0_never_decodes_5
#print axioms CIGAMF.P13.MarlPhaseLock.receiver0_never_decodes_8
#print axioms CIGAMF.P13.MarlPhaseLock.never_covered_count
#print axioms CIGAMF.P13.MarlPhaseLock.never_covered_forever
