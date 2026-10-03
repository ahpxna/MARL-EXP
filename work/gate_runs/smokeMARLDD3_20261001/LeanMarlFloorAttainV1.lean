import Mathlib
import LeanMarlAgeFirstInjectionV1
import LeanMarlInjectionFloorV1

/-!
# Age-first ordering attains the injection floor exactly

`LeanMarlInjectionFloorV1.injection_floor` bounds the injection ages of ANY schedule with at most `L` transmissions per
step from below by `∑_{s ≤ t} (m - (s + 1) L)`.  This module proves that age-first ordering with exactly `L`
transmissions per step (the `L` senders with the oldest last transmission, ties by index:
`LeanMarlAgeFirstInjectionV1.key`) meets that bound with EQUALITY at every step.

## WHAT IS PROVED
* `tau_succ_eq_lastTx` — the two encodings agree: last transmission before `t + 1` = last transmission up to `t`.
* `no_repeat` — under age-first with `L` per step, a sender transmitted at `t1` is not transmitted again at
  `t1 + d + 1` unless `m < (d + 2) L`: while at least `L` senders are older, it is not among the `L` oldest.
* `recent_within` — every sender is transmitted in every window of `q` consecutive steps with `m ≤ q L`.
* `layer_exact` — for every `s ≤ t` with `(s + 1) L ≤ m`, exactly `(s + 1) L` senders have injection age at most `s`.
* `floor_attained` — hence `∑_j injAge t j = ∑_{s ≤ t} (m - (s + 1) L)` for every `t`: the floor, attained.
* `alt_hyps`, `alt_floor` — the hypotheses hold for two senders alternating (`L = 1`), and the equality applies.

## WHAT THIS DOES NOT ESTABLISH
- Anything when the number of transmissions varies from step to step (E3's iid capacities); there the floor is a
  lower bound only (`injection_floor`).
- Receiver ages (they exceed injection ages by the propagation gap; `LeanMarlRelayOneHopV1` bounds it by one step under
  a covering head).
-/

namespace CIGAMF.P13.MarlFloorAttain

open Finset
open CIGAMF.P13.MarlAgeFirstInjection
open CIGAMF.P13.MarlInjectionFloor

variable {m : ℕ} (U : ℕ → Finset (Fin m))

theorem tau_succ_eq_lastTx (t : ℕ) (j : Fin m) : tau U (t + 1) j = lastTx U t j := by
  induction t with
  | zero => simp [tau, lastTx]
  | succ t ih =>
      show (if j ∈ U (t + 1) then t + 1 + 1 else tau U (t + 1) j) = lastTx U (t + 1) j
      simp only [lastTx]
      rw [ih]

/-- Age-first with exactly `L` transmissions per step. -/
structure AgeFirstL (L : ℕ) : Prop where
  card : ∀ t, (U t).card = L
  oldest : ∀ t j k, j ∈ U t → k ∉ U t → key U t j < key U t k

/-- `tau` does not move while a sender is not transmitted. -/
theorem tau_const (k : Fin m) (t1 : ℕ) :
    ∀ n, (∀ u, t1 ≤ u → u < t1 + n → k ∉ U u) → tau U (t1 + n) k = tau U t1 k := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      show (if k ∈ U (t1 + n) then t1 + n + 1 else tau U (t1 + n) k) = tau U t1 k
      rw [if_neg (h (t1 + n) (by omega) (by omega))]
      exact ih fun u h1 h2 => h u h1 (by omega)

variable {U}

/-- The core step: if `j` was last transmitted at `t1` and is transmitted again at `t1 + d + 1`, then
`m < (d + 2) L`. -/
theorem no_repeat_last {L : ℕ} (H : AgeFirstL U L) (t1 d : ℕ) (j : Fin m) (h1 : j ∈ U t1) (h2 : j ∈ U (t1 + d + 1))
    (hgap : ∀ u, t1 < u → u < t1 + d + 1 → j ∉ U u) : m < (d + 2) * L := by
  set t2 := t1 + d + 1 with ht2
  set W := (Icc t1 (t1 + d)).biUnion U with hW
  set O := univ \ W with hO
  -- the senders not transmitted in [t1, t2) are older than j at t2, so they must all be transmitted at t2
  have htauj : tau U t2 j = t1 + 1 := by
    have hstep : tau U (t1 + 1) j = t1 + 1 := by simp [tau, h1]
    have := tau_const U j (t1 + 1) d (fun u hu1 hu2 => hgap u (by omega) (by omega))
    rw [show t1 + 1 + d = t2 by omega] at this
    rw [this, hstep]
  have hO_sub : insert j O ⊆ U t2 := by
    intro k hk
    rcases mem_insert.mp hk with rfl | hk
    · exact h2
    · by_contra hkU
      have hkW : ∀ u, t1 ≤ u → u < t1 + d + 1 → k ∉ U u := by
        intro u hu1 hu2 hku
        have : k ∈ W := mem_biUnion.mpr ⟨u, mem_Icc.mpr ⟨hu1, by omega⟩, hku⟩
        exact (mem_sdiff.mp hk).2 this
      have htk : tau U t2 k = tau U t1 k := by
        have := tau_const U k t1 (d + 1) (fun u hu1 hu2 => hkW u hu1 (by omega))
        rwa [show t1 + (d + 1) = t2 by omega] at this
      have hlt : tau U t2 k < tau U t2 j := by
        rw [htk, htauj]; exact Nat.lt_succ_of_le (tau_le U t1 k)
      exact absurd (H.oldest t2 j k h2 hkU) (not_lt.mpr (le_of_lt (key_lt_of_tau_lt U hlt)))
  have hjO : j ∉ O := fun hj => (mem_sdiff.mp hj).2 (mem_biUnion.mpr ⟨t1, mem_Icc.mpr ⟨le_rfl, by omega⟩, h1⟩)
  have hcardO : (insert j O).card ≤ L := by rw [← H.card t2]; exact card_le_card hO_sub
  rw [card_insert_of_notMem hjO] at hcardO
  have hW : W.card ≤ (d + 1) * L := by
    calc W.card ≤ ∑ u ∈ Icc t1 (t1 + d), (U u).card := card_biUnion_le
      _ = ∑ _u ∈ Icc t1 (t1 + d), L := sum_congr rfl fun u _ => H.card u
      _ = (d + 1) * L := by rw [sum_const, Nat.card_Icc, smul_eq_mul]; congr 1; omega
  have hOc : O.card = m - W.card := by
    rw [hO, card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin]
  rw [hOc] at hcardO
  have hL : 0 < L := by rw [← H.card t1]; exact card_pos.mpr ⟨j, h1⟩
  have h3 : (d + 2) * L = (d + 1) * L + L := by ring
  omega

/-- **No early repeat.** -/
theorem no_repeat {L : ℕ} (H : AgeFirstL U L) :
    ∀ d t1 (j : Fin m), j ∈ U t1 → j ∈ U (t1 + d + 1) → m < (d + 2) * L := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
      intro t1 j h1 h2
      by_cases hmid : ∃ u, t1 < u ∧ u < t1 + d + 1 ∧ j ∈ U u
      · obtain ⟨u, hu1, hu2, hu⟩ := hmid
        have := ih (t1 + d - u) (by omega) u j hu (by rw [show u + (t1 + d - u) + 1 = t1 + d + 1 by omega]; exact h2)
        have h4 : (t1 + d - u + 2) * L ≤ (d + 2) * L := Nat.mul_le_mul_right L (by omega)
        omega
      · push_neg at hmid
        exact no_repeat_last H t1 d j h1 h2 fun u hu1 hu2 => hmid u hu1 hu2

theorem lastTx_ge_of_mem (j : Fin m) (u : ℕ) (hu : j ∈ U u) : ∀ t, u ≤ t → u + 1 ≤ lastTx U t j := by
  intro t ht
  induction t with
  | zero =>
      have : u = 0 := by omega
      subst this; simp [lastTx, hu]
  | succ t ih =>
      simp only [lastTx]
      split_ifs with h
      · omega
      · rcases Nat.eq_or_lt_of_le ht with he | hlt
        · rw [← he] at h; exact absurd hu h
        · exact ih (by omega)

/-- The senders of injection age at most `s` are exactly those transmitted in the last `s + 1` steps. -/
theorem recent_eq_union (t s : ℕ) (hs : s ≤ t) :
    (univ.filter fun j => injAge U t j ≤ s) = (Icc (t - s) t).biUnion U := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_Icc]
  constructor
  · intro hj
    unfold injAge at hj
    have hle := lastTx_le U t j
    obtain ⟨u, hu, hmem, he⟩ := lastTx_spec U t j (by omega)
    exact ⟨u, ⟨by omega, hu⟩, hmem⟩
  · rintro ⟨u, ⟨hu1, hu2⟩, hmem⟩
    have := lastTx_ge_of_mem j u hmem t hu2
    unfold injAge; omega

/-- **Exact layers.** -/
theorem layer_exact {L : ℕ} (H : AgeFirstL U L) (t s : ℕ) (hs : s ≤ t) (hsL : (s + 1) * L ≤ m) :
    (univ.filter fun j => injAge U t j ≤ s).card = (s + 1) * L := by
  rw [recent_eq_union t s hs, card_biUnion]
  · rw [sum_congr rfl fun u _ => H.card u, sum_const, Nat.card_Icc, smul_eq_mul]
    congr 1; omega
  · intro u1 hu1 u2 hu2 hne
    rw [Function.onFun, disjoint_left]
    intro j hj1 hj2
    simp only [coe_Icc, Set.mem_Icc] at hu1 hu2
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := no_repeat H (u2 - u1 - 1) u1 j hj1 (by rw [show u1 + (u2 - u1 - 1) + 1 = u2 by omega]; exact hj2)
      have : (u2 - u1 - 1 + 2) * L ≤ (s + 1) * L := Nat.mul_le_mul_right L (by omega)
      omega
    · have := no_repeat H (u1 - u2 - 1) u2 j hj2 (by rw [show u2 + (u1 - u2 - 1) + 1 = u1 by omega]; exact hj1)
      have : (u1 - u2 - 1 + 2) * L ≤ (s + 1) * L := Nat.mul_le_mul_right L (by omega)
      omega

/-- While `j` is not transmitted, the transmitted senders are all ahead of it and then fall behind it. -/
theorem ahead_drop {L : ℕ} (H : AgeFirstL U L) (t : ℕ) (j : Fin m) (hj : j ∉ U t) :
    (ahead U (t + 1) j).card + L ≤ (ahead U t j).card := by
  have hsubU : U t ⊆ ahead U t j := by
    intro k hk
    simp only [ahead, mem_filter, mem_univ, true_and]
    exact H.oldest t k j hk hj
  have hsub : ahead U (t + 1) j ⊆ ahead U t j \ U t := by
    intro k hk
    simp only [ahead, mem_filter, mem_univ, true_and] at hk
    by_cases hkU : k ∈ U t
    · exact absurd hk (not_lt.mpr (le_of_lt (key_behind U hkU hj)))
    · refine mem_sdiff.mpr ⟨?_, hkU⟩
      simp only [ahead, mem_filter, mem_univ, true_and]
      unfold key at hk ⊢
      simp only [tau, if_neg hkU, if_neg hj] at hk
      exact hk
  have h1 := card_le_card hsub
  rw [card_sdiff_of_subset hsubU, H.card t] at h1
  have h2 := card_le_card hsubU
  rw [H.card t] at h2
  omega

/-- **Every sender is transmitted in every window of `q` steps with `m ≤ q L`.** -/
theorem recent_within {L : ℕ} (H : AgeFirstL U L) (hL : 0 < L) (q : ℕ) (hq : m ≤ q * L) (t0 : ℕ) (j : Fin m) :
    ∃ u, t0 ≤ u ∧ u < t0 + q ∧ j ∈ U u := by
  by_contra hno
  push_neg at hno
  have hdrop : ∀ n, n ≤ q → (ahead U (t0 + n) j).card + n * L ≤ (ahead U t0 j).card := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have := ahead_drop H (t0 + n) j (hno (t0 + n) (by omega) (by omega))
        have := ih (by omega)
        rw [show t0 + (n + 1) = t0 + n + 1 by omega]
        nlinarith
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h
      have : m = 0 := by omega
      exact absurd j.isLt (by omega)
    · exact h
  have := hdrop q le_rfl
  have hc := ahead_card_le (U := U) t0 j
  have hjm := j.isLt
  have : q * L ≤ m - 1 := by omega
  omega

/-- **The floor is attained at every step.** -/
theorem floor_attained {L : ℕ} (H : AgeFirstL U L) (hL : 0 < L) (t : ℕ) :
    ∑ j, injAge U t j = ∑ s ∈ range (t + 1), (m - (s + 1) * L) := by
  rw [sum_injAge_layer U t]
  refine sum_congr rfl fun s hs => ?_
  have hst : s ≤ t := by simpa [mem_range, Nat.lt_succ_iff] using hs
  have hU : (univ : Finset (Fin m)) =
      (univ.filter fun j => injAge U t j ≤ s) ∪ (univ.filter fun j => s < injAge U t j) := by
    ext j; simp only [mem_univ, mem_union, mem_filter, true_and, true_iff]; exact le_or_gt _ _
  have hdisj : Disjoint (univ.filter fun j => injAge U t j ≤ s) (univ.filter fun j => s < injAge U t j) := by
    rw [disjoint_filter]; intro j _ h1 h2; omega
  have hsplit : m = (univ.filter fun j => injAge U t j ≤ s).card + (univ.filter fun j => s < injAge U t j).card := by
    rw [← card_union_of_disjoint hdisj, ← hU, card_univ, Fintype.card_fin]
  by_cases hsL : (s + 1) * L ≤ m
  · have := layer_exact H t s hst hsL
    omega
  · -- every sender was transmitted in the last s + 1 steps
    have hall : (univ.filter fun j => injAge U t j ≤ s) = univ := by
      apply eq_univ_of_forall
      intro j
      obtain ⟨u, hu1, hu2, hu⟩ := recent_within H hL (s + 1) (by omega) (t - s) j
      rw [recent_eq_union t s hst]
      exact mem_biUnion.mpr ⟨u, mem_Icc.mpr ⟨hu1, by omega⟩, hu⟩
    rw [hall, card_univ, Fintype.card_fin] at hsplit
    omega

/-- Two senders alternating, one transmission per step. -/
def altU (t : ℕ) : Finset (Fin 2) := {⟨t % 2, Nat.mod_lt _ (by decide)⟩}

theorem alt_tau (t : ℕ) : ∀ j : Fin 2,
    tau altU (t + 1) j = if j.val = t % 2 then t + 1 else if t = 0 then 0 else t := by
  induction t with
  | zero => decide
  | succ t ih =>
      intro j
      show (if j ∈ altU (t + 1) then t + 1 + 1 else tau altU (t + 1) j) = _
      have hj := j.isLt
      have hmem : j ∈ altU (t + 1) ↔ j.val = (t + 1) % 2 := by simp [altU, Fin.ext_iff]
      by_cases h : j.val = (t + 1) % 2
      · rw [if_pos (hmem.mpr h), if_pos h]
      · have hv : j.val = t % 2 := by omega
        rw [if_neg (fun hm => h (hmem.mp hm)), ih j, if_neg h, if_neg (show t + 1 ≠ 0 by omega), if_pos hv]

theorem alt_hyps : AgeFirstL altU 1 := by
  refine ⟨fun t => by simp [altU], fun t j k hj hk => ?_⟩
  have hjv : j.val = t % 2 := by simp [altU, Fin.ext_iff] at hj; exact hj
  have hkv : k.val ≠ t % 2 := by intro he; exact hk (by simp [altU, Fin.ext_iff, he])
  have := j.isLt; have := k.isLt
  unfold key
  rcases t with _ | t
  · simp only [tau]; omega
  · rw [alt_tau t j, alt_tau t k]
    split_ifs <;> omega

theorem alt_floor (t : ℕ) : ∑ j, injAge altU t j = ∑ s ∈ range (t + 1), (2 - (s + 1) * 1) :=
  floor_attained alt_hyps (by decide) t

end CIGAMF.P13.MarlFloorAttain

#print axioms CIGAMF.P13.MarlFloorAttain.tau_succ_eq_lastTx
#print axioms CIGAMF.P13.MarlFloorAttain.no_repeat
#print axioms CIGAMF.P13.MarlFloorAttain.layer_exact
#print axioms CIGAMF.P13.MarlFloorAttain.recent_within
#print axioms CIGAMF.P13.MarlFloorAttain.floor_attained
#print axioms CIGAMF.P13.MarlFloorAttain.alt_hyps
#print axioms CIGAMF.P13.MarlFloorAttain.alt_floor
