import Mathlib
import «LeanMarlMenuRevisionV1»

/-!
# The three-message XOR team game: exact randomised and deterministic commitment prices

The model (MARL_SYNTHESIS_RESEARCH_PROPOSAL_20260926, Decision 5):
- `M₁ = X ⊕ E`, `M₂ = Y`, `M₃ = X ⊕ Y`, with `X, Y` uniform bits and `E ~ Bernoulli(p)`,
  `0 < p < 1/2`;
- two agents must both output `X`.

The optimal team failure is `ℓ(∅) = ½`, `ℓ{1} = p`, `ℓ{2} = ℓ{3} = ½`, `ℓ{1,2} = ℓ{1,3} = p`,
`ℓ{2,3} = ℓ{1,2,3} = 0`.  It is derived from the joint law at the end of this file
(`table_lower`, `table_attained`).  In `Fin 3` indexing, message `j` is `j − 1`.
The per-budget regrets are therefore
- budget 1: `0` at `{0}`, and `½ − p` at `{1}` and `{2}`;
- budget 2: `0` at `{1,2}`, and `p` at `{0,1}` and `{0,2}`.

## WHAT IS PROVED

* `randomised_price_lower` — for EVERY probability law `P` on rankings of three items, the
  worst-budget expected regret is at least `p(1 − 2p)` (the q, r argument).
* `randomised_price_attained` — the law `(1 − 2p)·[identity] + 2p·[finRotate 3]` attains it.
* `deterministic_price` — every single ranking has worst-budget regret at least
  `min(p, ½ − p)`, and the identity and `finRotate 3` attain `p` and `½ − p` respectively.
* `one_revision_closes` — from EVERY ranking, one replacement reaches regret `0` at both
  budgets.  The randomised price is strictly positive, so the revision gain is exactly
  `p(1 − 2p)`.

* `table_lower`, `table_attained`, `pairing_lower`, `team_ge_single`, `team_self` — the loss
  table DERIVED from the joint law.  Every decoder errs at least `½`, `½`, `½`, `p`, `p`, `p` on
  `∅`, `{1}`, `{2}`, `{0}`, `{0,1}`, `{0,2}` (pairing by involutions that keep the transcript and
  flip `X`).  Explicit decoders attain every entry, including `0` on `{1,2}` and `{0,1,2}`.  Team
  failure equals the best single-decoder error.

## WHAT THIS DOES NOT ESTABLISH

- Messages with noise beyond `E`, more agents, or learned decoders.  This is the exact finite game.
-/

namespace CIGAMF.P13.MarlXorGame

open Finset
open CIGAMF.P13.PaperCStabilityEndgame CIGAMF.P13.MarlMenuRevision

/-- Regret at budget 1. -/
noncomputable def reg1 (p : ℝ) (S : Finset (Fin 3)) : ℝ := if S = {0} then 0 else 1 / 2 - p
/-- Regret at budget 2. -/
noncomputable def reg2 (p : ℝ) (S : Finset (Fin 3)) : ℝ := if S = {1, 2} then 0 else p

/-- Indicator that the budget-1 prefix is the best singleton. -/
noncomputable def good1 (σ : Equiv.Perm (Fin 3)) : ℝ := if prefixSet σ 1 = {0} then 1 else 0
/-- Indicator that the budget-2 prefix is the best pair. -/
noncomputable def good2 (σ : Equiv.Perm (Fin 3)) : ℝ := if prefixSet σ 2 = {1, 2} then 1 else 0

theorem reg1_eq (p : ℝ) (σ : Equiv.Perm (Fin 3)) :
    reg1 p (prefixSet σ 1) = (1 - good1 σ) * (1 / 2 - p) := by
  unfold reg1 good1; split_ifs <;> ring

theorem reg2_eq (p : ℝ) (σ : Equiv.Perm (Fin 3)) :
    reg2 p (prefixSet σ 2) = (1 - good2 σ) * p := by
  unfold reg2 good2; split_ifs <;> ring

/-- The two good events are disjoint: a ranking starting with `0` has `0` in its 2-prefix. -/
theorem good_disjoint (σ : Equiv.Perm (Fin 3)) : good1 σ + good2 σ ≤ 1 := by
  unfold good1 good2
  by_cases h1 : prefixSet σ 1 = {0}
  · by_cases h2 : prefixSet σ 2 = {1, 2}
    · exfalso
      have hm := prefixSet_mono σ 1 2 (by decide)
      rw [h1, h2] at hm
      have : (0 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := hm (by simp)
      exact absurd this (by decide)
    · simp [h1, h2]
  · by_cases h2 : prefixSet σ 2 = {1, 2} <;> simp [h1, h2]

theorem good1_nonneg (σ : Equiv.Perm (Fin 3)) : 0 ≤ good1 σ := by
  unfold good1; split_ifs <;> norm_num
theorem good2_nonneg (σ : Equiv.Perm (Fin 3)) : 0 ≤ good2 σ := by
  unfold good2; split_ifs <;> norm_num

/-- **Lower bound, every law.**  `max(E₁, E₂) ≥ p(1 − 2p)`. -/
theorem randomised_price_lower (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2)
    (P : Equiv.Perm (Fin 3) → ℝ) (hP : ∀ σ, 0 ≤ P σ) (hP1 : ∑ σ, P σ = 1) :
    p * (1 - 2 * p) ≤ max (∑ σ, P σ * reg1 p (prefixSet σ 1)) (∑ σ, P σ * reg2 p (prefixSet σ 2)) := by
  set q := ∑ σ, P σ * good1 σ with hq
  set r := ∑ σ, P σ * good2 σ with hr
  have hE1 : ∑ σ, P σ * reg1 p (prefixSet σ 1) = (1 - q) * (1 / 2 - p) := by
    simp_rw [reg1_eq]
    have : ∑ σ, P σ * ((1 - good1 σ) * (1 / 2 - p)) = (∑ σ, P σ - ∑ σ, P σ * good1 σ) * (1 / 2 - p) := by
      rw [sub_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun σ _ => by ring)
    rw [this, hP1]
  have hE2 : ∑ σ, P σ * reg2 p (prefixSet σ 2) = (1 - r) * p := by
    simp_rw [reg2_eq]
    have : ∑ σ, P σ * ((1 - good2 σ) * p) = (∑ σ, P σ - ∑ σ, P σ * good2 σ) * p := by
      rw [sub_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun σ _ => by ring)
    rw [this, hP1]
  have hqr : q + r ≤ 1 := by
    have : ∑ σ, P σ * (good1 σ + good2 σ) ≤ ∑ σ, P σ * 1 :=
      Finset.sum_le_sum (fun σ _ => mul_le_mul_of_nonneg_left (good_disjoint σ) (hP σ))
    simp only [mul_add, Finset.sum_add_distrib, mul_one] at this
    rw [hP1] at this
    linarith
  have hq0 : 0 ≤ q := Finset.sum_nonneg (fun σ _ => mul_nonneg (hP σ) (good1_nonneg σ))
  rw [hE1, hE2]
  -- max ≥ 2p·E₁ + (1−2p)·E₂ ≥ p(1−2p)
  have hmix : 2 * p * ((1 - q) * (1 / 2 - p)) + (1 - 2 * p) * ((1 - r) * p) ≤
      max ((1 - q) * (1 / 2 - p)) ((1 - r) * p) := by
    have h1 := le_max_left ((1 - q) * (1 / 2 - p)) ((1 - r) * p)
    have h2 := le_max_right ((1 - q) * (1 / 2 - p)) ((1 - r) * p)
    have ha : 0 ≤ 2 * p := by linarith
    have hb : 0 ≤ 1 - 2 * p := by linarith
    nlinarith
  have hlow : p * (1 - 2 * p) ≤ 2 * p * ((1 - q) * (1 / 2 - p)) + (1 - 2 * p) * ((1 - r) * p) := by
    have hb : 0 ≤ (1 - 2 * p) * p := by nlinarith
    nlinarith
  linarith

/-- The two rankings used by the optimal law. -/
theorem prefix_id : prefixSet (1 : Equiv.Perm (Fin 3)) 1 = {0} ∧
    prefixSet (1 : Equiv.Perm (Fin 3)) 2 = {0, 1} := by
  constructor <;> decide

theorem prefix_rot : prefixSet (finRotate 3) 1 = {1} ∧ prefixSet (finRotate 3) 2 = {1, 2} := by
  constructor <;> decide

theorem rot_ne_one : (finRotate 3) ≠ (1 : Equiv.Perm (Fin 3)) := by decide

/-- **Attainment.**  The law `(1 − 2p)·[identity] + 2p·[finRotate 3]` has worst-budget
expected regret exactly `p(1 − 2p)`. -/
theorem randomised_price_attained (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) :
    let P : Equiv.Perm (Fin 3) → ℝ := fun σ =>
      if σ = 1 then 1 - 2 * p else if σ = finRotate 3 then 2 * p else 0
    (∀ σ, 0 ≤ P σ) ∧ ∑ σ, P σ = 1 ∧
      max (∑ σ, P σ * reg1 p (prefixSet σ 1)) (∑ σ, P σ * reg2 p (prefixSet σ 2)) = p * (1 - 2 * p) := by
  intro P
  have hsplit : ∀ f : Equiv.Perm (Fin 3) → ℝ,
      ∑ σ, P σ * f σ = (1 - 2 * p) * f 1 + 2 * p * f (finRotate 3) := by
    intro f
    have hne := rot_ne_one
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin 3)))]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ (finRotate 3)⟩)]
    have hrest : ∑ σ ∈ ((Finset.univ.erase (1 : Equiv.Perm (Fin 3))).erase (finRotate 3)), P σ * f σ = 0 := by
      refine Finset.sum_eq_zero (fun σ hσ => ?_)
      have h1 : σ ≠ 1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hσ).2).1
      have h2 : σ ≠ finRotate 3 := (Finset.mem_erase.mp hσ).1
      simp [P, h1, h2]
    rw [hrest]
    simp [P, hne]
  refine ⟨fun σ => ?_, ?_, ?_⟩
  · simp only [P]; split_ifs <;> linarith
  · have := hsplit (fun _ => 1); simp only [mul_one] at this; rw [this]; ring
  · rw [hsplit (fun σ => reg1 p (prefixSet σ 1)), hsplit (fun σ => reg2 p (prefixSet σ 2))]
    simp only [prefix_id.1, prefix_id.2, prefix_rot.1, prefix_rot.2, reg1, reg2]
    have n1 : ({1} : Finset (Fin 3)) ≠ {0} := by decide
    have n2 : ({0, 1} : Finset (Fin 3)) ≠ {1, 2} := by decide
    simp only [n1, n2, ite_true, ite_false]
    have : (1 - 2 * p) * 0 + 2 * p * (1 / 2 - p) = p * (1 - 2 * p) := by ring
    have h' : (1 - 2 * p) * p + 2 * p * 0 = p * (1 - 2 * p) := by ring
    rw [this, h', max_self]

/-- **Deterministic price.**  Every ranking pays at least `min(p, ½ − p)` at its worse budget;
the identity pays `p` and `finRotate 3` pays `½ − p`. -/
theorem deterministic_price (p : ℝ) (hp0 : 0 < p) (hp : p < 1 / 2) :
    (∀ σ : Equiv.Perm (Fin 3), min p (1 / 2 - p) ≤
        max (reg1 p (prefixSet σ 1)) (reg2 p (prefixSet σ 2))) ∧
      max (reg1 p (prefixSet 1 1)) (reg2 p (prefixSet 1 2)) = p ∧
      max (reg1 p (prefixSet (finRotate 3) 1)) (reg2 p (prefixSet (finRotate 3) 2)) = 1 / 2 - p := by
  refine ⟨fun σ => ?_, ?_, ?_⟩
  · rw [reg1_eq, reg2_eq]
    have hd := good_disjoint σ
    unfold good1 good2 at hd ⊢
    split_ifs at hd ⊢ with h1 h2 h2
    · norm_num at hd
    · simp only [sub_self, zero_mul, sub_zero, one_mul]
      exact le_trans (min_le_left _ _) (le_max_right _ _)
    · simp only [sub_self, zero_mul, sub_zero, one_mul]
      exact le_trans (min_le_right _ _) (le_max_left _ _)
    · simp only [sub_zero, one_mul]
      exact le_trans (min_le_left _ _) (le_max_right _ _)
  · simp only [prefix_id.1, prefix_id.2, reg1, reg2]
    have n2 : ({0, 1} : Finset (Fin 3)) ≠ {1, 2} := by decide
    simp only [n2, ite_true, ite_false]
    exact max_eq_right hp0.le
  · simp only [prefix_rot.1, prefix_rot.2, reg1, reg2]
    have n1 : ({1} : Finset (Fin 3)) ≠ {0} := by decide
    simp only [n1, ite_true, ite_false]
    exact max_eq_left (by linarith)

/-- **One revision closes the price**: from every ranking, one replacement reaches regret `0` at
both budgets. -/
theorem one_revision_closes (p : ℝ) (σ : Equiv.Perm (Fin 3)) :
    (∃ S : Finset (Fin 3), S.card = 1 ∧ (prefixSet σ 1 \ S).card ≤ 1 ∧ reg1 p S = 0) ∧
      (∃ S : Finset (Fin 3), S.card = 2 ∧ (prefixSet σ 2 \ S).card ≤ 1 ∧ reg2 p S = 0) := by
  refine ⟨⟨{0}, by decide, ?_, by simp [reg1]⟩, ⟨{1, 2}, by decide, ?_, by simp [reg2]⟩⟩
  · calc (prefixSet σ 1 \ {0}).card ≤ (prefixSet σ 1).card := Finset.card_le_card Finset.sdiff_subset
      _ = 1 := prefixSet_card σ 1
  · have hsub : prefixSet σ 2 \ {1, 2} ⊆ ({0} : Finset (Fin 3)) := by
      intro x hx
      have hx2 : x ∉ ({1, 2} : Finset (Fin 3)) := (Finset.mem_sdiff.mp hx).2
      fin_cases x <;> simp_all
    calc (prefixSet σ 2 \ {1, 2}).card ≤ ({0} : Finset (Fin 3)).card := Finset.card_le_card hsub
      _ = 1 := by decide

/-! ## The loss table DERIVED from the joint law (Bayes over every decoder)

Worlds `w = (X, Y, E) ∈ Bool³` with weight `(E ? p : 1 − p)/4`.  Messages (index `0,1,2`):
`X ⊕ E`, `Y`, `X ⊕ Y`.  A decoder sees the transcript `obs S w` (messages outside `S` masked).
A team of two decoders fails unless both output `X`; its failure is at least that of either
decoder and equals it when both use the same decoder, so the optimal team failure is the
optimal single-decoder error. -/

abbrev World := Bool × Bool × Bool

noncomputable def wt (p : ℝ) (w : World) : ℝ := (if w.2.2 then p else 1 - p) / 4

def msg (w : World) : Fin 3 → Bool := ![xor w.1 w.2.2, w.2.1, xor w.1 w.2.1]

def obs (S : Finset (Fin 3)) (w : World) : Fin 3 → Bool := fun i => if i ∈ S then msg w i else false

/-- Single-decoder error. -/
noncomputable def err (p : ℝ) (S : Finset (Fin 3)) (d : (Fin 3 → Bool) → Bool) : ℝ :=
  ∑ w : World, wt p w * (if d (obs S w) = w.1 then 0 else 1)

/-- Team failure of two decoders. -/
noncomputable def teamErr (p : ℝ) (S : Finset (Fin 3)) (d₁ d₂ : (Fin 3 → Bool) → Bool) : ℝ :=
  ∑ w : World, wt p w * (if d₁ (obs S w) = w.1 ∧ d₂ (obs S w) = w.1 then 0 else 1)

theorem wt_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : World) : 0 ≤ wt p w := by
  unfold wt; split_ifs <;> linarith

theorem team_ge_single (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin 3))
    (d₁ d₂ : (Fin 3 → Bool) → Bool) : err p S d₁ ≤ teamErr p S d₁ d₂ := by
  unfold err teamErr
  refine Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left ?_ (wt_nonneg p hp0 hp1 w))
  by_cases h1 : d₁ (obs S w) = w.1 <;> by_cases h2 : d₂ (obs S w) = w.1 <;> simp [h1, h2]

theorem team_self (p : ℝ) (S : Finset (Fin 3)) (d : (Fin 3 → Bool) → Bool) :
    teamErr p S d d = err p S d := by
  unfold err teamErr; simp

/-- **Pairing lower bound.**  If an involution `f` keeps the transcript and flips `X`, every
decoder errs on at least one world of each pair. -/
theorem pairing_lower (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin 3))
    (f : World → World) (hf : Function.Involutive f)
    (hobs : ∀ w, obs S (f w) = obs S w) (hX : ∀ w, (f w).1 = !w.1)
    (d : (Fin 3 → Bool) → Bool) :
    (∑ w : World, min (wt p w) (wt p (f w))) / 2 ≤ err p S d := by
  classical
  set e : World → ℝ := fun w => if d (obs S w) = w.1 then 0 else 1 with he
  have hpair : ∀ w, 1 ≤ e w + e (f w) := by
    intro w
    simp only [he, hobs w, hX w]
    by_cases h : d (obs S w) = w.1
    · have h' : ¬ d (obs S w) = !w.1 := by rw [h]; cases w.1 <;> decide
      simp [h, h']
    · have h' : d (obs S w) = !w.1 := by
        cases hd : d (obs S w) <;> cases hw : w.1 <;> simp_all
      simp [h, h']
  have he0 : ∀ w, 0 ≤ e w := fun w => by simp only [he]; split_ifs <;> norm_num
  have hre : ∑ w, wt p w * e w = ∑ w, wt p (f w) * e (f w) :=
    (Equiv.sum_comp hf.toPerm (fun w => wt p w * e w)).symm
  have hsum : ∑ w, min (wt p w) (wt p (f w)) ≤ ∑ w, (wt p w * e w + wt p (f w) * e (f w)) := by
    refine Finset.sum_le_sum (fun w _ => ?_)
    have hm0 : 0 ≤ min (wt p w) (wt p (f w)) := le_min (wt_nonneg p hp0 hp1 w) (wt_nonneg p hp0 hp1 (f w))
    have h1 : min (wt p w) (wt p (f w)) * e w ≤ wt p w * e w :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (he0 w)
    have h2 : min (wt p w) (wt p (f w)) * e (f w) ≤ wt p (f w) * e (f w) :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (he0 (f w))
    nlinarith [hpair w]
  rw [Finset.sum_add_distrib, ← hre] at hsum
  unfold err
  change (∑ w : World, min (wt p w) (wt p (f w))) / 2 ≤ ∑ w, wt p w * e w
  linarith

theorem sum_World (g : World → ℝ) :
    ∑ w : World, g w = g (false, false, false) + g (false, false, true) + g (false, true, false) +
      g (false, true, true) + g (true, false, false) + g (true, false, true) + g (true, true, false) +
      g (true, true, true) := by
  simp [Fintype.sum_prod_type, Fintype.sum_bool]; ring

/-- Involutions: `flipX` (keeps E, Y), `flipXY` (keeps E), `flipXE` (keeps Y), `flipXYE`. -/
def flipX (w : World) : World := (!w.1, w.2.1, w.2.2)
def flipXY (w : World) : World := (!w.1, !w.2.1, w.2.2)
def flipXE (w : World) : World := (!w.1, w.2.1, !w.2.2)
def flipXYE (w : World) : World := (!w.1, !w.2.1, !w.2.2)

theorem inv_flipX : Function.Involutive flipX := fun w => by simp [flipX]
theorem inv_flipXY : Function.Involutive flipXY := fun w => by simp [flipXY]
theorem inv_flipXE : Function.Involutive flipXE := fun w => by simp [flipXE]
theorem inv_flipXYE : Function.Involutive flipXYE := fun w => by simp [flipXYE]

theorem min_sum_keepE (p : ℝ) (f : World → World) (hE : ∀ w, (f w).2.2 = w.2.2) :
    ∑ w : World, min (wt p w) (wt p (f w)) = 1 := by
  have : ∀ w, min (wt p w) (wt p (f w)) = wt p w := fun w => by
    have : wt p (f w) = wt p w := by unfold wt; rw [hE w]
    rw [this, min_self]
  simp_rw [this]
  rw [sum_World]; unfold wt; simp; ring

theorem min_sum_flipE (p : ℝ) (hp : p ≤ 1 / 2) (f : World → World) (hE : ∀ w, (f w).2.2 = !w.2.2) :
    ∑ w : World, min (wt p w) (wt p (f w)) = 2 * p := by
  have : ∀ w, min (wt p w) (wt p (f w)) = p / 4 := fun w => by
    unfold wt; rw [hE w]
    cases w.2.2 <;> simp <;> linarith
  simp_rw [this]; simp; ring

/-- **The loss table, lower sides, for every decoder.** -/
theorem table_lower (p : ℝ) (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (d : (Fin 3 → Bool) → Bool) :
    1 / 2 ≤ err p ∅ d ∧ 1 / 2 ≤ err p {1} d ∧ 1 / 2 ≤ err p {2} d ∧
    p ≤ err p {0} d ∧ p ≤ err p {0, 1} d ∧ p ≤ err p {0, 2} d := by
  have hp1 : p ≤ 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := pairing_lower p hp0 hp1 ∅ flipX inv_flipX (by decide) (fun w => rfl) d
    rw [min_sum_keepE p flipX (fun w => rfl)] at h; linarith
  · have h := pairing_lower p hp0 hp1 {1} flipX inv_flipX (by decide) (fun w => rfl) d
    rw [min_sum_keepE p flipX (fun w => rfl)] at h; linarith
  · have h := pairing_lower p hp0 hp1 {2} flipXY inv_flipXY (by decide) (fun w => rfl) d
    rw [min_sum_keepE p flipXY (fun w => rfl)] at h; linarith
  · have h := pairing_lower p hp0 hp1 {0} flipXE inv_flipXE (by decide) (fun w => rfl) d
    rw [min_sum_flipE p hp flipXE (fun w => rfl)] at h; linarith
  · have h := pairing_lower p hp0 hp1 {0, 1} flipXE inv_flipXE (by decide) (fun w => rfl) d
    rw [min_sum_flipE p hp flipXE (fun w => rfl)] at h; linarith
  · have h := pairing_lower p hp0 hp1 {0, 2} flipXYE inv_flipXYE (by decide) (fun w => rfl) d
    rw [min_sum_flipE p hp flipXYE (fun w => rfl)] at h; linarith

/-- **The loss table, attained**: constant `false` (error `½`), read `X ⊕ E` (error `p`), and
`Y ⊕ (X ⊕ Y) = X` (error `0`). -/
theorem table_attained (p : ℝ) :
    err p ∅ (fun _ => false) = 1 / 2 ∧ err p {1} (fun _ => false) = 1 / 2 ∧
    err p {2} (fun _ => false) = 1 / 2 ∧
    err p {0} (fun o => o 0) = p ∧ err p {0, 1} (fun o => o 0) = p ∧ err p {0, 2} (fun o => o 0) = p ∧
    err p {1, 2} (fun o => xor (o 1) (o 2)) = 0 ∧ err p {0, 1, 2} (fun o => xor (o 1) (o 2)) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold err; rw [sum_World]; simp [obs, msg, wt]; try ring)

end CIGAMF.P13.MarlXorGame

#print axioms CIGAMF.P13.MarlXorGame.randomised_price_lower
#print axioms CIGAMF.P13.MarlXorGame.randomised_price_attained
#print axioms CIGAMF.P13.MarlXorGame.deterministic_price
#print axioms CIGAMF.P13.MarlXorGame.one_revision_closes
#print axioms CIGAMF.P13.MarlXorGame.team_ge_single
#print axioms CIGAMF.P13.MarlXorGame.team_self
#print axioms CIGAMF.P13.MarlXorGame.pairing_lower
#print axioms CIGAMF.P13.MarlXorGame.table_lower
#print axioms CIGAMF.P13.MarlXorGame.table_attained
