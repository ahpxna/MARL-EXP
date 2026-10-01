import Mathlib

/-!
# Age-first ordering transmits every sender at least once in every `m` steps

`U t ⊆ Fin m` is the set of senders transmitted at step `t`.  `tau t j` is the encoded time of `j`'s last transmission
BEFORE step `t` (`0` if none, `s + 1` for step `s`).  The age-first order ranks senders by `key t j = tau t j · m + j`
(oldest last transmission first, ties by index; the encoding is exact because `j < m`).  The head `h t` is the
key-minimal sender.  In the prefix channel every other receiver decodes the head when capacities are at least one, so
the head is transmitted.

## WHAT IS PROVED
* `exists_head` — a key-minimal sender exists at every step (`m ≥ 1`).
* `ahead_shrinks` — if `j` is not transmitted at step `t`, strictly fewer senders are ahead of it at `t + 1`: the head
  moves behind it, every transmitted sender moves behind it, and nobody overtakes it.
* `transmitted_within` — hence `j` is transmitted within `#ahead + 1` steps, and `injection_bound`: EVERY sender is
  transmitted at least once in every `m` consecutive steps, for every sequence of transmitted sets that contains the
  age-first head.
* `sticky_starvation` — under a fixed order, in the threshold form of prefix decoding, a sender whose position is at
  least every receiver's threshold is never decoded: no bound of this kind holds for the congestion order.
* `ageFirst_witness` — the hypotheses are satisfiable (every sender transmitted at every step, the head is sender `0`).

## WHAT THIS DOES NOT ESTABLISH
- That the head visits every sender: it need not (with ties broken by index and several transmissions per step, the
  head concentrates on a few senders; replica L-180).  The bound is on TRANSMISSION, not on the head.
- Any bound on receiver ages (relay does the spreading: `LeanMarlRelayOneHopV1`).
-/

namespace CIGAMF.P13.MarlAgeFirstInjection

open Finset

variable {m : ℕ} (U : ℕ → Finset (Fin m))

/-- Encoded time of the last transmission BEFORE step `t`. -/
def tau : ℕ → Fin m → ℕ
  | 0, _ => 0
  | t + 1, j => if j ∈ U t then t + 1 else tau t j

/-- The age-first key: oldest last transmission first, ties by index. -/
def key (t : ℕ) (j : Fin m) : ℕ := tau U t j * m + j.val

/-- The senders ranked ahead of `j` at step `t`. -/
def ahead (t : ℕ) (j : Fin m) : Finset (Fin m) := univ.filter fun k => key U t k < key U t j

theorem tau_le (t : ℕ) (j : Fin m) : tau U t j ≤ t := by
  induction t with
  | zero => simp [tau]
  | succ t ih => simp only [tau]; split_ifs <;> omega

theorem key_lt_of_tau_lt {t : ℕ} {k j : Fin m} (h : tau U t k < tau U t j) : key U t k < key U t j := by
  unfold key
  have hk := k.isLt
  calc tau U t k * m + k.val < tau U t k * m + m := by omega
    _ = (tau U t k + 1) * m := by ring
    _ ≤ tau U t j * m := Nat.mul_le_mul_right m h
    _ ≤ tau U t j * m + j.val := Nat.le_add_right _ _

/-- A sender just transmitted is behind every sender that was not. -/
theorem key_behind {t : ℕ} {k j : Fin m} (hk : k ∈ U t) (hj : j ∉ U t) : key U (t + 1) j < key U (t + 1) k := by
  apply key_lt_of_tau_lt
  simp only [tau, if_pos hk, if_neg hj]
  have := tau_le U t j
  omega

/-- The age-first head: key-minimal at every step, and transmitted. -/
structure AgeFirstHead (h : ℕ → Fin m) : Prop where
  transmitted : ∀ t, h t ∈ U t
  minimal : ∀ t j, j ≠ h t → key U t (h t) < key U t j

theorem key_injective (t : ℕ) : Function.Injective (key U t) := by
  intro a b hab
  unfold key at hab
  have ha := a.isLt
  have hb := b.isLt
  have h1 : tau U t a = tau U t b := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := key_lt_of_tau_lt U hlt; unfold key at this; omega
    · have := key_lt_of_tau_lt U hlt; unfold key at this; omega
  rw [h1] at hab
  exact Fin.ext (by omega)

theorem exists_head [NeZero m] (t : ℕ) : ∃ k, ∀ j, j ≠ k → key U t k < key U t j := by
  obtain ⟨k, -, hk⟩ := exists_min_image univ (key U t) univ_nonempty
  refine ⟨k, fun j hj => lt_of_le_of_ne (hk j (mem_univ _)) fun he => hj ?_⟩
  exact (key_injective U t he).symm

variable {U}

theorem ahead_shrinks {h : ℕ → Fin m} (H : AgeFirstHead U h) (t : ℕ) (j : Fin m) (hj : j ∉ U t) :
    (ahead U (t + 1) j).card < (ahead U t j).card := by
  have hne : j ≠ h t := fun he => hj (he ▸ H.transmitted t)
  have hhead : h t ∈ ahead U t j := by
    simp only [ahead, mem_filter, mem_univ, true_and]; exact H.minimal t j hne
  have hsub : ahead U (t + 1) j ⊆ (ahead U t j).erase (h t) := by
    intro k hk
    simp only [ahead, mem_filter, mem_univ, true_and] at hk
    by_cases hkU : k ∈ U t
    · exact absurd hk (not_lt.mpr (le_of_lt (key_behind U hkU hj)))
    · refine mem_erase.mpr ⟨fun he => hkU (he ▸ H.transmitted t), ?_⟩
      simp only [ahead, mem_filter, mem_univ, true_and]
      unfold key at hk ⊢
      simp only [tau, if_neg hkU, if_neg hj] at hk
      exact hk
  calc (ahead U (t + 1) j).card ≤ ((ahead U t j).erase (h t)).card := card_le_card hsub
    _ < (ahead U t j).card := card_erase_lt_of_mem hhead

theorem transmitted_within {h : ℕ → Fin m} (H : AgeFirstHead U h) :
    ∀ n t j, (ahead U t j).card ≤ n → ∃ u, t ≤ u ∧ u ≤ t + n ∧ j ∈ U u := by
  intro n
  induction n with
  | zero =>
      intro t j hc
      have hempty : ahead U t j = ∅ := card_eq_zero.mp (by omega)
      have hjh : j = h t := by
        by_contra hne
        have : h t ∈ ahead U t j := by
          simp only [ahead, mem_filter, mem_univ, true_and]; exact H.minimal t j hne
        rw [hempty] at this; simp at this
      exact ⟨t, le_rfl, by omega, hjh ▸ H.transmitted t⟩
  | succ n ih =>
      intro t j hc
      by_cases hj : j ∈ U t
      · exact ⟨t, le_rfl, by omega, hj⟩
      · have hlt := ahead_shrinks H t j hj
        obtain ⟨u, hu1, hu2, hu⟩ := ih (t + 1) j (by omega)
        exact ⟨u, by omega, by omega, hu⟩

theorem ahead_card_le (t : ℕ) (j : Fin m) : (ahead U t j).card ≤ m - 1 := by
  have hsub : ahead U t j ⊆ univ.erase j := by
    intro k hk
    simp only [ahead, mem_filter, mem_univ, true_and] at hk
    exact mem_erase.mpr ⟨fun he => by rw [he] at hk; exact lt_irrefl _ hk, mem_univ _⟩
  calc (ahead U t j).card ≤ (univ.erase j).card := card_le_card hsub
    _ = m - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]

/-- **Injection bound.**  Under age-first ordering, every sender is transmitted at least once in every `m`
consecutive steps. -/
theorem injection_bound {h : ℕ → Fin m} (H : AgeFirstHead U h) (t : ℕ) (j : Fin m) :
    ∃ u, t ≤ u ∧ u ≤ t + (m - 1) ∧ j ∈ U u :=
  transmitted_within H (m - 1) t j (ahead_card_le t j)

/-- **Starvation under a fixed order** (threshold form of prefix decoding): a sender at a position no receiver's
threshold exceeds is never decoded, at any step. -/
theorem sticky_starvation (pos : Fin m → ℕ) (r : ℕ → Fin m → ℕ) (R : ℕ) (hr : ∀ t i, r t i ≤ R) (j : Fin m)
    (hj : R ≤ pos j) : ∀ t i, ¬ (j ≠ i ∧ pos j < r t i) := by
  intro t i ⟨_, hlt⟩
  have := hr t i
  omega

/-- The hypotheses are satisfiable: every sender transmitted at every step, head `0`. -/
theorem ageFirst_witness : AgeFirstHead (m := 3) (fun _ => univ) (fun _ => 0) := by
  refine ⟨fun t => mem_univ _, fun t j hj => ?_⟩
  have htau : ∀ k : Fin 3, tau (m := 3) (fun _ => univ) t k = t := by
    intro k
    cases t with
    | zero => rfl
    | succ t => simp [tau]
  unfold key
  rw [htau, htau]
  have : (0 : Fin 3).val < j.val := by
    rcases Fin.val_ne_iff.mpr hj with h
    have := j.isLt
    omega
  omega

end CIGAMF.P13.MarlAgeFirstInjection

#print axioms CIGAMF.P13.MarlAgeFirstInjection.exists_head
#print axioms CIGAMF.P13.MarlAgeFirstInjection.ahead_shrinks
#print axioms CIGAMF.P13.MarlAgeFirstInjection.transmitted_within
#print axioms CIGAMF.P13.MarlAgeFirstInjection.injection_bound
#print axioms CIGAMF.P13.MarlAgeFirstInjection.sticky_starvation
#print axioms CIGAMF.P13.MarlAgeFirstInjection.ageFirst_witness
